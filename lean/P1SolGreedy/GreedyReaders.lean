import P1SolGreedy.GreedyFormat
import P1SolGreedy.GreedyBatch
import P1ChkFinal.ProgC11

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal

namespace P1SolGreedy.SolDemand

theorem bval_add (x y : NumberWord) :
    P1Batch.bval (Bits.add (x, y)) = P1Batch.bval x + P1Batch.bval y := by
  rw [← value_bval, Bits.add_val, value_bval, value_bval]

theorem bval_mul (x y : NumberWord) :
    P1Batch.bval (Carry.times0 (x, y)) = P1Batch.bval x * P1Batch.bval y := by
  rw [← value_bval, Carry.tm_value, value_bval, value_bval]

theorem bval_bitsVal (w : NumberWord) : P1Batch.bval w = bitsVal w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [P1Batch.bval, bitsVal, Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, ite_false, ite_true, ih]

theorem size_snd_le {A T : Type} [Codec A] [Codec T] (p : A × T) : size p.2 ≤ size p := by
  rw [size_prod]
  omega

theorem total_le_of_width_le (qs : List P1Batch.Req) (W : ℕ)
    (hW : ∀ q ∈ qs, P1Batch.bval q.2 ≤ W) :
    P1Batch.total qs ≤ qs.length * W := by
  induction qs with
  | nil => simp [P1Batch.total]
  | cons r qs ih =>
    rw [P1ChkFinal.total_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ht := ih fun q hq => hW q (List.mem_cons_of_mem r hq)
    have hh := hW r List.mem_cons_self
    omega

def requestNumbers (req : P1Batch.Req) : ℕ × ℕ := (P1Batch.bval req.1, P1Batch.bval req.2)

theorem requestNumbers_field (o w i : NumberWord) :
    requestNumbers (fieldWords ((o, w), i)) =
      (P1Batch.bval o + P1Batch.bval i * P1Batch.bval w, P1Batch.bval w) :=
  Prod.ext (fieldWords_start o w i) rfl

theorem requestNumbers_fieldReq (D : Dims) (s i : ℕ) :
    requestNumbers (fieldReq D s i) = (D.off s + i * D.width s, D.width s) := by
  simp only [requestNumbers, fieldReq, bval_bin]

theorem requestNumbers_rowField (D : Dims) (ℓ : ℕ) (c : Mem) (i : NumberWord) :
    requestNumbers (fieldWords (rowSection c (levelRow D ℓ), i)) =
      requestNumbers (fieldReq D (secLev ℓ c) (P1Batch.bval i)) := by
  rw [rowSection_levelRow, requestNumbers_field, requestNumbers_fieldReq, bval_bin, bval_bin]

theorem fetch_of_requestNumbers (u : List Bool) {a b : P1Batch.Req}
    (h : requestNumbers a = requestNumbers b) : P1Batch.fetch u a = P1Batch.fetch u b :=
  congrArg (fun p : ℕ × ℕ => (u.drop p.1).take p.2) h

theorem fetches_of_requestNumbers (u : List Bool) {a b : List P1Batch.Req}
    (h : a.map requestNumbers = b.map requestNumbers) : a.map (P1Batch.fetch u) = b.map (P1Batch.fetch u) := by
  let get (p : ℕ × ℕ) := (u.drop p.1).take p.2
  change a.map (fun q => get (requestNumbers q)) = b.map (fun q => get (requestNumbers q))
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map get) h

theorem total_of_requestNumbers {a b : List P1Batch.Req}
    (h : a.map requestNumbers = b.map requestNumbers) : P1Batch.total a = P1Batch.total b := by
  simpa only [P1Batch.total, List.map_map, Function.comp_def, requestNumbers] using
    congrArg (fun p : List (ℕ × ℕ) => (p.map Prod.snd).sum) h

/-- Bound the bit start before submitting a request to the batch program. -/
def clipRequest (p : NumberWord × P1Batch.Req) : P1Batch.Req :=
  (minNumber (p.2.1, p.1), p.2.2)

@[fun_prop] theorem clipRequest_poly : Poly clipRequest := by
  unfold clipRequest
  fun_prop

def clipRequests (p : NumberWord × List P1Batch.Req) : List P1Batch.Req :=
  Code.polyPush clipRequest p

@[fun_prop] theorem clipRequests_poly : Poly clipRequests :=
  Poly.push [] ([], []) clipRequest_poly

theorem clipRequests_bound (len : NumberWord) (qs : List P1Batch.Req) {q : P1Batch.Req}
    (hq : q ∈ clipRequests (len, qs)) :
    P1Batch.bval q.1 ≤ P1Batch.bval len := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
  change P1Batch.bval (minNumber (r.1, len)) ≤ _
  rw [minNumber_value]
  exact min_le_right _ _

theorem clipRequests_total (len : NumberWord) (qs : List P1Batch.Req) :
    P1Batch.total (clipRequests (len, qs)) = P1Batch.total qs := by
  simp only [clipRequests, Code.polyPush, P1Batch.total, List.map_map, Function.comp_def, clipRequest]

theorem clipRequests_fetch (u : List Bool) (len : NumberWord) (hl : P1Batch.bval len = u.length)
    (qs : List P1Batch.Req) :
    (clipRequests (len, qs)).map (P1Batch.fetch u) = qs.map (P1Batch.fetch u) := by
  unfold clipRequests Code.polyPush
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def, P1Batch.fetch, clipRequest, minNumber_value, hl]
  by_cases h : P1Batch.bval q.1 ≤ u.length
  · rw [min_eq_left h]
  · have hh := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [min_eq_right hh, List.drop_of_length_le (le_refl _), List.drop_of_length_le hh]

abbrev SetupIdx {M K : ℕ → ℕ} (p : QDom M K) : IndexWord :=
  (bin p.val.1.length, p.val.2.2)

def smallSize {M K : ℕ → ℕ} (p : QDom M K) : ℕ :=
  Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length

theorem index_size {M K : ℕ → ℕ} :
    Dom (smallSize (M := M) (K := K)) (fun p => size (SetupIdx p)) := by
  refine ⟨1, 5, fun p => ?_⟩
  have h := (length_bin_log p.val.1.length).trans
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)
  simp only [Nat.succ_eq_add_one] at h
  simp only [SetupIdx, size_prod, size_listBool, smallSize, pow_one]
  omega

theorem prepareWitness {M K : ℕ → ℕ} {S : Type} [Codec S] (hl : LenHyp)
    (setup : IndexWord → S) (hsetup : Poly setup) :
    ∃ t : QDom M K → ℕ, Dom smallSize t ∧
      Code.Task (fun p => p.val.1.length + 3 * p.val.2.1.length + t p)
        (fun p => send p.val) (fun p => send (p.val.2.1, setup (SetupIdx p))) := by
  obtain ⟨t, ht, T⟩ := hsetup.on (q := SetupIdx (M := M) (K := K)) index_size
  let cost : QDom M K → ℕ := fun p => t p + size (SetupIdx p) + 3
  have hcost : Dom smallSize cost := (ht.add index_size).add (Dom.const _ 3)
  have T₀ := ((lenHyp_bin hl).on (fun p : QDom M K => p.val.1)).left (fun p => send p.val.2)
  have rearrange : Easy (fun q : NumberWord × (NumberWord × NumberWord) =>
      (q.2.1, (q.1, q.2.2))) := by fun_prop
  have T₁ := rearrange.on (fun p : QDom M K => (bin p.val.1.length, p.val.2))
  have T₂ := T.right (fun p => send p.val.2.1)
  refine ⟨cost, hcost, ((T₀.compose T₁).compose T₂).bound 4 ?_⟩
  intro p
  have hu : (send p.val.2.1).count = 2 * p.val.2.1.length + 1 := size_listBool _
  simp only [hu, size_prod, size_listBool, cost, SetupIdx]
  omega

theorem pack_budget {M K : ℕ → ℕ} {t : QDom M K → ℕ} {reply : QDom M K → Tree} {E : ℕ}
    (ht : Dom smallSize t)
    (T : Code.Task (fun p => E * (p.val.1.length + p.val.2.1.length + p.val.2.2.length) + t p)
      (fun p => send p.val) reply) :
    ∃ c : ℕ, Code.Task (fun p => budget c p.val) (fun p => send p.val) reply := by
  obtain ⟨k, C, hC⟩ := ht
  refine ⟨k, T.bound (E + C + 1) fun p => ?_⟩
  have h := hC p
  simp only [budget, smallSize] at h ⊢
  set L := p.val.1.length + p.val.2.1.length + p.val.2.2.length
  set P := (Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length + 1) ^ k
  have he := Nat.mul_le_mul_left E (show L ≤ L + P + 1 by omega)
  have hc := Nat.mul_le_mul_left C (show P ≤ L + P + 1 by omega)
  simp only [Nat.add_mul, Nat.one_mul] at *
  omega

theorem taskOneBatch {M K : ℕ → ℕ} {S : Type} [Codec S] (hb : BatchHyp) (hl : LenHyp)
    (setup : IndexWord → S) (hsetup : Poly setup)
    (rq : S → List P1Batch.Req) (hrq : Poly rq)
    (dec : S × List (List Bool) → Bool) (hd : Poly dec)
    (ck : QDom M K → Bool)
    (ht : Dom smallSize (fun p : QDom M K => P1Batch.total (rq (setup (SetupIdx p)))))
    (ha : ∀ p : QDom M K, ∀ r ∈ rq (setup (SetupIdx p)), P1Batch.bval r.1 ≤ p.val.2.1.length)
    (hc : ∀ p : QDom M K,
      ck p = dec (setup (SetupIdx p), (rq (setup (SetupIdx p))).map (P1Batch.fetch p.val.2.1))) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (ck p)) := by
  obtain ⟨t, ht', T⟩ := prepareWitness (M := M) (K := K) hl setup hsetup
  have hs : Dom smallSize (fun p : QDom M K => size (setup (SetupIdx p))) :=
    (hsetup.length.map SetupIdx).sub index_size
  obtain ⟨s, hs', T'⟩ := checkSkeleton hb (fun p : QDom M K => send p.val) (fun p => p.val.2.1)
    (fun p => setup (SetupIdx p)) rq dec ck _ _ T (hrq.pair Poly.identity) hd hs ht ha hc
  apply pack_budget (E := 4) (ht'.add hs')
  exact T'.bound 1 (fun p => by simp only [Nat.one_mul]; omega)

end P1SolGreedy.SolDemand
