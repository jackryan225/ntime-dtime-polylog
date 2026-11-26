import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic
import Mathlib.Data.Nat.Log

/-!
# P1, wave 2: the common skeleton of a check program (lane P1-lean-W2-chkfinal)

Every check of the witness (paper l.1104-1122) does the same four things: (A) strip the input `x` to a SMALL datum
`s` (binary length of `x`, the index word, ...), keeping the witness `u`; (B) compute from `s` the list of
requests `(address, length)` of the fields it reads (polynomial in the size of `s`); (C) fetch the fields from `u`
with ONE batched look-up (`P1Batch.batch_lookup`); (D) decide from `s` and the fields (polynomial).

`checkSkeleton`: from Tasks for (A), (B), (D) and the batched look-up, one Task for the whole check whose budget is
the budget of (A), plus `|u|`, plus a term `t` that is polynomial in a size measure `σ` of the small data, provided
the small datum and the total requested length are polynomial in `σ`. OpenAI's Task framework
(`OAI/Computability/IntegerMultiplication/Code/Task.lean`): `Task.compose`, `Task.left`, `Task.right`, `Easy`,
`Poly`, `Dom`.
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- [P1-lean-W2-batch] The statement of `P1Batch.batch_lookup` (PROVED there, job batch-11). -/
def BatchHyp : Prop :=
  ∃ c : ℕ, Code.Task (fun i : P1Batch.BatchIn => i.val.1.length + (size i.val.2 + P1Batch.total i.val.2 + 1) ^ c)
    (fun i => send i.val) (fun i => send (i.val.2.map (P1Batch.fetch i.val.1)))

/-! ## Binary words (least significant bit first, `P1Batch.bval`) -/

/-- The canonical binary word of `n`, least significant bit first. -/
def bin : ℕ → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: bin ((n + 1) / 2)

theorem bval_bin : ∀ n, P1Batch.bval (bin n) = n
  | 0 => by simp [bin, P1Batch.bval]
  | n + 1 => by
    rw [bin, P1Batch.bval, bval_bin ((n + 1) / 2)]
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
    · rw [h]
      simp only [Nat.zero_ne_one, decide_false, Bool.toNat_false]
      omega
    · rw [h]
      simp only [decide_true, Bool.toNat_true]
      omega

theorem length_bin_le : ∀ k n, n < 2 ^ k → (bin n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [bin]
  | k + 1, 0, _ => by simp [bin]
  | k + 1, n + 1, h => by
    rw [bin, List.length_cons]
    have h2 : (n + 1) / 2 < 2 ^ k := by
      rw [pow_succ] at h
      omega
    have := length_bin_le k ((n + 1) / 2) h2
    omega

theorem length_bin_log (n : ℕ) : (bin n).length ≤ Nat.log 2 n + 1 :=
  length_bin_le _ n (Nat.lt_pow_succ_log_self (by norm_num) n)

theorem size_listBool (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [size_cons, size_bit, ih, List.length_cons]
    omega

theorem length_le_size {α : Type*} [Codec α] (l : List α) : l.length ≤ size l := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons b l ih =>
    rw [size_cons, List.length_cons]
    omega

theorem total_cons (q : P1Batch.Req) (qs : List P1Batch.Req) :
    P1Batch.total (q :: qs) = P1Batch.bval q.2 + P1Batch.total qs := by
  simp [P1Batch.total]

/-- The fetched fields are small: at most twice the requested length, plus the list overhead. -/
theorem size_fields (w : List Bool) (qs : List P1Batch.Req) :
    size (qs.map (P1Batch.fetch w)) ≤ 2 * P1Batch.total qs + 2 * size qs + 1 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    rw [List.map_cons, size_cons, size_listBool, size_cons, total_cons]
    have hf : (P1Batch.fetch w q).length ≤ P1Batch.bval q.2 := by
      unfold P1Batch.fetch
      exact List.length_take_le _ _
    have hq := size_pos q
    omega

/-- **The check skeleton.** -/
theorem checkSkeleton {X S : Type*} [Codec S] (hbatch : BatchHyp)
    (Q : X → Tree) (u : X → List Bool) (s : X → S) (rq : S → List P1Batch.Req)
    (dec : S × List (List Bool) → Bool) (ck : X → Bool) (a σ : X → ℕ)
    (hA : Code.Task a Q (fun p => send (u p, s p)))
    (hrq : Poly (fun z : S => (rq z, z)))
    (hdec : Poly dec)
    (hσ : Dom σ (fun p => size (s p)))
    (htot : Dom σ (fun p => P1Batch.total (rq (s p))))
    (haddr : ∀ p, ∀ r ∈ rq (s p), P1Batch.bval r.1 ≤ (u p).length)
    (hck : ∀ p, ck p = dec (s p, (rq (s p)).map (P1Batch.fetch (u p)))) :
    ∃ t : X → ℕ, Dom σ t ∧ Code.Task (fun p => a p + (u p).length + t p) Q (fun p => send (ck p)) := by
  have hlenR := hrq.length
  obtain ⟨cb, hB⟩ := hbatch
  obtain ⟨t2, ht2d, ht2⟩ := hrq
  obtain ⟨t5, ht5d, ht5⟩ := hdec
  -- (B) the requests, on the right component
  have T2 : Code.Task (fun p => (send (u p)).count + t2 (s p)) (fun p => send (u p, s p))
      (fun p => send (u p, (rq (s p), s p))) :=
    (ht2.on s).right (fun p => send (u p))
  -- reassociate
  have E3 : Easy (fun w : List Bool × (List P1Batch.Req × S) => ((w.1, w.2.1), w.2.2)) :=
    Easy.pair (Easy.pair Easy.fst (Easy.compose Easy.snd Easy.fst)) (Easy.compose Easy.snd Easy.snd)
  have T3 := E3.on (fun p => (u p, (rq (s p), s p)))
  -- (C) the batched look-up, on the left component
  let bin : X → P1Batch.BatchIn := fun p => ⟨(u p, rq (s p)), haddr p⟩
  have T4 : Code.Task (fun p => (u p).length + (size (rq (s p)) + P1Batch.total (rq (s p)) + 1) ^ cb)
      (fun p => send ((u p, rq (s p)), s p))
      (fun p => send ((rq (s p)).map (P1Batch.fetch (u p)), s p)) :=
    (hB.on bin).left (fun p => send (s p))
  -- (D) swap and decide
  have T5a := (Easy.exchange (X := List (List Bool)) (Y := S)).on
    (fun p => ((rq (s p)).map (P1Batch.fetch (u p)), s p))
  have T5b := ht5.on (fun p => (s p, (rq (s p)).map (P1Batch.fetch (u p))))
  have T := ((((hA.compose T2).compose T3).compose T4).compose T5a).compose T5b
  -- the polynomial part of the budget
  let Fd : X → List (List Bool) := fun p => (rq (s p)).map (P1Batch.fetch (u p))
  let t : X → ℕ := fun p => t2 (s p) + size (rq (s p)) + size (s p) +
    (size (rq (s p)) + P1Batch.total (rq (s p)) + 1) ^ cb + size (Fd p) + t5 (s p, Fd p) + 4
  have hR : Dom σ (fun p => size (rq (s p))) := by
    have h1 : Dom size (fun z : S => size (rq z)) :=
      hlenR.mono fun z => by simp only [size_prod]; omega
    exact (h1.map s).sub hσ
  have hF : Dom σ (fun p => size (Fd p)) :=
    ((((Dom.const σ 2).mul htot).add ((Dom.const σ 2).mul hR)).add (Dom.const σ 1)).mono
      fun p => size_fields (u p) (rq (s p))
  have ht : Dom σ t := by
    have h2 : Dom σ (fun p => t2 (s p)) := (ht2d.map s).sub hσ
    have h4 : Dom σ (fun p => (size (rq (s p)) + P1Batch.total (rq (s p)) + 1) ^ cb) :=
      ((hR.add htot).add (Dom.const σ 1)).pow cb
    have h5 : Dom σ (fun p => t5 (s p, Fd p)) := by
      have hs5 : Dom σ (fun p => size (s p, Fd p)) :=
        ((hσ.add hF).add (Dom.const σ 1)).mono fun p => by rw [size_prod]
      exact (ht5d.map (fun p => (s p, Fd p))).sub hs5
    exact (((((h2.add hR).add hσ).add h4).add hF).add h5).add (Dom.const σ 4)
  refine ⟨t, ht, ?_⟩
  have T' : Code.Task (fun p => a p + (u p).length + t p) Q (fun p => send (dec (s p, Fd p))) := by
    refine T.bound 8 fun p => ?_
    have hu : (send (u p)).count = 2 * (u p).length + 1 := size_listBool (u p)
    have hu' : size (u p) = 2 * (u p).length + 1 := size_listBool (u p)
    simp only [size_prod, t, Fd]
    generalize (size (rq (s p)) + P1Batch.total (rq (s p)) + 1) ^ cb = P4
    omega
  exact T'.conform (fun _ => rfl) (fun _ => rfl) (fun p => by rw [hck p])

end P1ChkFinal
