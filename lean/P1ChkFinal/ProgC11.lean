import P1ChkFinal.Progs
import P1ChkFinal.BinBits
import P1Wit.Decode
import Mathlib.Tactic.Linarith

/-!
# P1, wave 2: the program of family 10 (check C11) from the check skeleton (lane P1-lean-W2-chkfinal)

* `fieldReq D s i`: the P6 field `i` of section `s` as a batch request (address, width in binary);
  `readField_eq`: P6's reader is `bitsVal` of the fetched field.
* `rqC11`: the requests of C11 at index `i` (`Ω(i)`, `Ω(i+1)` and the `lanes * slots` widths of final base `i`,
  none if `i` is out of range); `decC11`: the decision from `(bin |x|, ρ)` and the fetched fields;
  `hckC11`: `decide (C11w dims x u (bval ρ)) = decC11 ...` (the semantic step).
* `progC11`: the Task of family 10, from `checkSkeleton`. Its ONLY arithmetic hypotheses are `Poly` of the two
  concrete functions `rqC11`, `decC11` (polynomial in the small datum) and a polylog bound on the requested length.
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit

open scoped Classical

/-- `LenHyp` (with Mathlib's `Nat.bits`) gives the length word `bin |x|` of the skeleton (`bin_eq_bits`). -/
theorem lenHyp_bin (hl : LenHyp) : Computes (fun x : List Bool => x.length) (fun x : List Bool => bin x.length) :=
  Task.conform hl (fun _ => rfl) (fun _ => rfl) (fun x => by simp only [bin_eq_bits])

/-! ## P6 fields as requests -/

/-- Field `i` of section `s` of the format `D`, as a batch request. -/
def fieldReq (D : Dims) (s i : ℕ) : P1Batch.Req := (bin (D.off s + i * D.width s), bin (D.width s))

theorem fetch_fieldReq (u : List Bool) (D : Dims) (s i : ℕ) :
    P1Batch.fetch u (fieldReq D s i) = (u.drop (D.off s + i * D.width s)).take (D.width s) := by
  simp only [P1Batch.fetch, fieldReq, bval_bin]

theorem readField_eq (D : Dims) (u : List Bool) (s i : ℕ) :
    readField D u s i = bitsVal (P1Batch.fetch u (fieldReq D s i)) := by
  rw [fetch_fieldReq]
  rfl

theorem offAt_mono (count width : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) : offAt count width s ≤ offAt count width t := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst this
    exact le_refl _
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h' | h'
    · refine (ih (by omega)).trans ?_
      show offAt count width t ≤ offAt count width t + count t * width t
      exact Nat.le_add_right _ _
    · have : s = t + 1 := by omega
      subst this
      exact le_refl _

/-- Every field of a section lies inside the fixed part. -/
theorem field_le_fixedLen (D : Dims) {s i : ℕ} (hs : s < D.nSec) (hi : i ≤ D.count s) :
    D.off s + i * D.width s ≤ D.fixedLen := by
  have h1 : D.off s + i * D.width s ≤ offAt D.count D.width (s + 1) := by
    show D.off s + i * D.width s ≤ offAt D.count D.width s + D.count s * D.width s
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  exact h1.trans (offAt_mono _ _ hs)

theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = pre f n := by
  induction n with
  | zero => simp [pre]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, pre_succ]
    simp

/-! ## The requests and the decision of C11 -/

/-- Index of the width field of arc `t` of final base `i` (`t = lane * slots + slot`). -/
def wIdx (D : Dims) (i t : ℕ) : ℕ :=
  (i * (D.lv D.top).lanes + t / (D.lv D.top).slots) * (D.lv D.top).slots + t % (D.lv D.top).slots

/-- The requests of C11 at index `bval z.2`, for `n = bval z.1`. -/
def rqC11 (dims : ℕ → Dims) (z : List Bool × List Bool) : List P1Batch.Req :=
  if P1Batch.bval z.2 < finN (dims (P1Batch.bval z.1)) then
    fieldReq (dims (P1Batch.bval z.1)) (dims (P1Batch.bval z.1)).secOmega (P1Batch.bval z.2) ::
      fieldReq (dims (P1Batch.bval z.1)) (dims (P1Batch.bval z.1)).secOmega (P1Batch.bval z.2 + 1) ::
      (List.range (finArcs (dims (P1Batch.bval z.1)))).map fun t =>
        fieldReq (dims (P1Batch.bval z.1)) (secLev (dims (P1Batch.bval z.1)).top .width)
          (wIdx (dims (P1Batch.bval z.1)) (P1Batch.bval z.2) t)
  else []

/-- The decision of C11 from the small datum and the fetched fields. -/
def decC11 (dims : ℕ → Dims) (zf : (List Bool × List Bool) × List (List Bool)) : Bool :=
  match zf.2 with
  | f0 :: f1 :: fw =>
    decide (P1Batch.bval zf.1.2 < finN (dims (P1Batch.bval zf.1.1)) →
      (P1Batch.bval zf.1.2 = 0 → bitsVal f0 = 0) ∧
      (P1Batch.bval zf.1.2 + 1 < finN (dims (P1Batch.bval zf.1.1)) →
        bitsVal f1 = bitsVal f0 + (fw.map bitsVal).sum))
  | _ => true

/-- **The semantic step of C11**: the decision on the fetched fields is the check. -/
theorem hckC11 (dims : ℕ → Dims) (x u ρ : List Bool) :
    decide (C11w dims x u (P1Batch.bval ρ)) =
      decC11 dims ((bin x.length, ρ), (rqC11 dims (bin x.length, ρ)).map (P1Batch.fetch u)) := by
  by_cases hi : P1Batch.bval ρ < finN (dims x.length)
  · have hi' : P1Batch.bval ρ < finN (dims (P1Batch.bval (bin x.length))) := by rw [bval_bin]; exact hi
    simp only [rqC11, if_pos hi', List.map_cons, List.map_map, decC11]
    rw [decide_eq_decide]
    simp only [bval_bin]
    unfold C11w C11
    have hw : (List.map (bitsVal ∘ P1Batch.fetch u ∘ fun t =>
        fieldReq (dims x.length) (secLev (dims x.length).top .width) (wIdx (dims x.length) (P1Batch.bval ρ) t))
          (List.range (finArcs (dims x.length)))).sum = wsOf (dims x.length) u (P1Batch.bval ρ) := by
      rw [sum_map_range]
      unfold wsOf
      congr 1
      funext t
      simp only [Function.comp, ← readField_eq]
      rfl
    rw [hw]
    simp only [rdOmega, readField_eq]
    constructor
    · intro h hlt
      obtain ⟨h0, h1⟩ := h hlt
      refine ⟨fun hz => ?_, h1⟩
      have := h0 hz
      rw [hz]
      exact this
    · intro h hlt
      obtain ⟨h0, h1⟩ := h hlt
      refine ⟨fun hz => ?_, h1⟩
      have := h0 hz
      rw [hz] at this
      exact this
  · have hi' : ¬ P1Batch.bval ρ < finN (dims (P1Batch.bval (bin x.length))) := by rw [bval_bin]; exact hi
    simp only [rqC11, if_neg hi', List.map_nil, decC11]
    exact decide_eq_true (C11_out (not_lt.mp hi))

/-! ## Bounds -/

/-- The requested length of C11 (Ω twice, the widths of one final base). -/
def totC11 (D : Dims) : ℕ := 2 * D.width D.secOmega + finArcs D * D.width (secLev D.top .width)

theorem total_rqC11_le (dims : ℕ → Dims) (z : List Bool × List Bool) :
    P1Batch.total (rqC11 dims z) ≤ totC11 (dims (P1Batch.bval z.1)) := by
  unfold rqC11
  split_ifs
  · simp only [P1Batch.total, List.map_cons, List.map_map, List.sum_cons, fieldReq, bval_bin, totC11,
      Function.comp_def, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
    omega
  · simp [P1Batch.total]

theorem wIdx_lt (D : Dims) {i t : ℕ} (hi : i < finN D) (ht : t < finArcs D) :
    wIdx D i t < (D.lv D.top).bases * (D.lv D.top).lanes * (D.lv D.top).slots := by
  unfold wIdx
  unfold finN at hi
  unfold finArcs at ht
  set B := (D.lv D.top).bases
  set La := (D.lv D.top).lanes
  set S := (D.lv D.top).slots
  have hS : 0 < S := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at ht; exact Nat.not_lt_zero _ ht
  have h1 : t % S < S := Nat.mod_lt _ hS
  have h2 : t / S < La := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  calc (i * La + t / S) * S + t % S < (i * La + t / S) * S + S := by omega
    _ = (i * La + t / S + 1) * S := by ring
    _ ≤ (i * La + La) * S := Nat.mul_le_mul_right _ (by omega)
    _ = (i + 1) * La * S := by ring
    _ ≤ B * La * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)

theorem addr_rqC11 (dims : ℕ → Dims) (z : List Bool × List Bool) :
    ∀ r ∈ rqC11 dims z, P1Batch.bval r.1 ≤ (dims (P1Batch.bval z.1)).fixedLen := by
  intro r hr
  unfold rqC11 at hr
  split_ifs at hr with hi
  · set D := dims (P1Batch.bval z.1)
    have hcO : D.count D.secOmega = finN D := by simp only [Dims.count, D.kind_Omega]; rfl
    rcases List.mem_cons.mp hr with h | hr
    · subst h
      simp only [fieldReq, bval_bin]
      exact field_le_fixedLen D D.secOmega_lt_nSec (by rw [hcO]; exact hi.le)
    rcases List.mem_cons.mp hr with h | hr
    · subst h
      simp only [fieldReq, bval_bin]
      exact field_le_fixedLen D D.secOmega_lt_nSec (by rw [hcO]; exact hi)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      simp only [fieldReq, bval_bin]
      refine field_le_fixedLen D (D.secLev_lt_nSec .width (le_refl _)) ?_
      rw [D.count_secLev .width (le_refl _)]
      exact (wIdx_lt D hi (List.mem_range.mp ht)).le
  · simp at hr

/-! ## The program -/

theorem arith_aux (X U R B T Q Ct : ℕ) (hB : B ≤ Q) (hT : T ≤ Ct * Q) :
    X + (2 * B + 1 + (2 * U + 1 + (2 * R + 1) + 1) + 1) + U + T + 1 ≤ (Ct + 10) * (X + U + R + Q + 1) := by
  have : Ct * Q ≤ Ct * (X + U + R + Q + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

/-- **Family 10 (C11), program.** -/
theorem progC11 (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp)
    (hM : ∀ n, (dims n).fixedLen ≤ M n)
    (hrq : Poly (fun z : List Bool × List Bool => (rqC11 dims z, z)))
    (hdec : Poly (decC11 dims))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC11 (dims n))) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C11w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let σ : QDom M K → ℕ := fun p => Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length
  -- (A) the binary length of x; keep u and ρ
  have E1 : Easy (fun w : List Bool × (List Bool × List Bool) => (w.2.1, (w.1, w.2.2))) :=
    Easy.pair (Easy.compose Easy.snd Easy.fst) (Easy.pair Easy.fst (Easy.compose Easy.snd Easy.snd))
  have T1 := ((lenHyp_bin hl).on (fun p : QDom M K => p.val.1)).left (fun p => send p.val.2)
  have T1' := E1.on (fun p : QDom M K => (bin p.val.1.length, p.val.2))
  have hA : Code.Task (fun p : QDom M K => p.val.1.length + size (bin p.val.1.length, p.val.2))
      (fun p => send p.val) (fun p => send (p.val.2.1, (bin p.val.1.length, p.val.2.2))) :=
    T1.compose T1'
  have hlog : ∀ p : QDom M K, (bin p.val.1.length).length ≤ Nat.log 2 (p.val.1.length + 1) + 1 :=
    fun p => (length_bin_log _).trans (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)
  have hσ : Dom σ (fun p => size (bin p.val.1.length, p.val.2.2)) := by
    refine ⟨1, 5, fun p => ?_⟩
    simp only [size_prod, size_listBool, pow_one, σ]
    have := hlog p
    omega
  have htot : Dom σ (fun p => P1Batch.total (rqC11 dims (bin p.val.1.length, p.val.2.2))) := by
    obtain ⟨k, C, hk⟩ := hfb
    refine ⟨k, C, fun p => ?_⟩
    refine (total_rqC11_le dims _).trans ?_
    simp only [bval_bin]
    refine (hk _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    simp only [σ]
    omega
  have haddr : ∀ p : QDom M K, ∀ r ∈ rqC11 dims (bin p.val.1.length, p.val.2.2),
      P1Batch.bval r.1 ≤ p.val.2.1.length := by
    intro p r hr
    have h1 := addr_rqC11 dims _ r hr
    simp only [bval_bin] at h1
    rw [p.property.1]
    exact h1.trans (hM _)
  obtain ⟨t, ⟨kt, Ct, hkt⟩, T⟩ := checkSkeleton hb (fun p : QDom M K => send p.val) (fun p => p.val.2.1)
    (fun p => (bin p.val.1.length, p.val.2.2)) (rqC11 dims) (decC11 dims)
    (fun p => decide (C11w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) _ σ hA hrq hdec hσ htot haddr
    (fun p => hckC11 dims p.val.1 p.val.2.1 p.val.2.2)
  refine ⟨kt + 1, T.bound (Ct + 10) fun p => ?_⟩
  have h1 := hkt p
  have h2 := hlog p
  simp only [σ] at h1
  simp only [budget, size_prod, size_listBool]
  set P := Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length + 1 with hPdef
  have hP0 : 1 ≤ P := by omega
  have hP1 : P ≤ P ^ (kt + 1) := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ (kt + 1) := Nat.pow_le_pow_right hP0 (by omega)
  have hP2 : P ^ kt ≤ P ^ (kt + 1) := Nat.pow_le_pow_right hP0 (by omega)
  have h3 : t p ≤ Ct * P ^ (kt + 1) := h1.trans (Nat.mul_le_mul_left _ hP2)
  have hb2 : (bin p.val.1.length).length ≤ P ^ (kt + 1) := by omega
  exact arith_aux _ _ _ _ _ _ _ hb2 h3

end P1ChkFinal
