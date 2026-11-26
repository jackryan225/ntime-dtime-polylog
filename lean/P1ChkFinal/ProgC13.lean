import P1ChkFinal.ProgC11

/-!
# P1, wave 2: a generic family program, and the program of family 13 (C13ends) (lane P1-lean-W2-chkfinal)

* `progFamily`: the proof of `progC11` for ANY family that reads a polylog number of P6 fields: given concrete
  `rq` (requests from `(bin |x|, ρ)`), `dec` (decision on the fetched fields), the semantic step `hck`, the address
  bound `haddr` and a polylog bound on the requested length, the family has a Task of the `ofTask` form.
* `progC13ends`: family 13 (`C13ends`, chain ends) with `rqC13ends` (one chain field: entry `0` or entry `P`) and
  `decC13ends` (the two finite tables `b.repr 1` and `l ∘ b` of the fixed algebra).
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module

open scoped Classical

/-- **A family program from concrete requests and decision.** -/
theorem progFamily (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp)
    (hM : ∀ n, (dims n).fixedLen ≤ M n)
    (rq : List Bool × List Bool → List P1Batch.Req) (dec : (List Bool × List Bool) × List (List Bool) → Bool)
    (ck : List Bool → List Bool → ℕ → Prop)
    (hrq : Poly (fun z : List Bool × List Bool => (rq z, z))) (hdec : Poly dec)
    (tot : Dims → ℕ) (htotle : ∀ z, P1Batch.total (rq z) ≤ tot (dims (P1Batch.bval z.1)))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => tot (dims n)))
    (haddr : ∀ z, ∀ r ∈ rq z, P1Batch.bval r.1 ≤ (dims (P1Batch.bval z.1)).fixedLen)
    (hck : ∀ x u ρ : List Bool, decide (ck x u (P1Batch.bval ρ)) =
      dec ((bin x.length, ρ), (rq (bin x.length, ρ)).map (P1Batch.fetch u))) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (ck p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let σ : QDom M K → ℕ := fun p => Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length
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
  have htot : Dom σ (fun p => P1Batch.total (rq (bin p.val.1.length, p.val.2.2))) := by
    obtain ⟨k, C, hk⟩ := hfb
    refine ⟨k, C, fun p => ?_⟩
    refine (htotle _).trans ?_
    simp only [bval_bin]
    refine (hk _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    simp only [σ]
    omega
  have haddr' : ∀ p : QDom M K, ∀ r ∈ rq (bin p.val.1.length, p.val.2.2),
      P1Batch.bval r.1 ≤ p.val.2.1.length := by
    intro p r hr
    have h1 := haddr _ r hr
    simp only [bval_bin] at h1
    rw [p.property.1]
    exact h1.trans (hM _)
  obtain ⟨t, ⟨kt, Ct, hkt⟩, T⟩ := checkSkeleton hb (fun p : QDom M K => send p.val) (fun p => p.val.2.1)
    (fun p => (bin p.val.1.length, p.val.2.2)) rq dec
    (fun p => decide (ck p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) _ σ hA hrq hdec hσ htot haddr'
    (fun p => hck p.val.1 p.val.2.1 p.val.2.2)
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

/-! ## Family 13: the chain ends -/

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- Requests of C13ends: index `0` reads chain entry `0`, index `1` reads chain entry `P`, others read nothing. -/
def rqC13ends (dims : ℕ → Dims) (z : List Bool × List Bool) : List P1Batch.Req :=
  if P1Batch.bval z.2 = 0 then [fieldReq (dims (P1Batch.bval z.1)) (dims (P1Batch.bval z.1)).secChain 0]
  else if P1Batch.bval z.2 = 1 then
    [fieldReq (dims (P1Batch.bval z.1)) (dims (P1Batch.bval z.1)).secChain (finP (dims (P1Batch.bval z.1)))]
  else []

/-- The start table of the fixed algebra. -/
def startOK (b : Basis (Fin Dd) (ZMod 2) F) (j : ℕ) : Prop := ∃ h : j < Dd, b.repr 1 ⟨j, h⟩ = 1

/-- The end table of the fixed algebra. -/
def endOK (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (j : ℕ) : Prop :=
  ∃ h : j < Dd, l (b ⟨j, h⟩) = 1

/-- The decision of C13ends from the small datum and the fetched field. -/
noncomputable def decC13ends (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
    (zf : (List Bool × List Bool) × List (List Bool)) : Bool :=
  match zf.2 with
  | [f] => if P1Batch.bval zf.1.2 = 0 then decide (startOK b (bitsVal f)) else decide (endOK b l (bitsVal f))
  | _ => true

theorem hckC13ends (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims)
    (x u ρ : List Bool) :
    decide (C13endsw b l dims x u (P1Batch.bval ρ)) =
      decC13ends b l ((bin x.length, ρ), (rqC13ends dims (bin x.length, ρ)).map (P1Batch.fetch u)) := by
  by_cases h0 : P1Batch.bval ρ = 0
  · simp only [rqC13ends, bval_bin, if_pos h0, List.map_cons, List.map_nil, decC13ends]
    rw [decide_eq_decide]
    unfold C13endsw C13ends
    simp only [h0, true_implies, zero_ne_one, false_implies, and_true, rdChain, readField_eq, startOK]
  · by_cases h1 : P1Batch.bval ρ = 1
    · simp only [rqC13ends, bval_bin, if_neg h0, if_pos h1, List.map_cons, List.map_nil, decC13ends]
      rw [decide_eq_decide]
      unfold C13endsw C13ends
      simp only [h1, true_implies, one_ne_zero, false_implies, true_and, rdChain, readField_eq, endOK]
    · simp only [rqC13ends, bval_bin, if_neg h0, if_neg h1, List.map_nil, decC13ends]
      exact decide_eq_true (C13endsw_out b l dims x u (by unfold cnt13ends; omega))

theorem addr_rqC13ends (dims : ℕ → Dims) (z : List Bool × List Bool) :
    ∀ r ∈ rqC13ends dims z, P1Batch.bval r.1 ≤ (dims (P1Batch.bval z.1)).fixedLen := by
  intro r hr
  have hc : (dims (P1Batch.bval z.1)).count (dims (P1Batch.bval z.1)).secChain =
      (dims (P1Batch.bval z.1)).chainLen := by
    simp only [Dims.count, (dims (P1Batch.bval z.1)).kind_chain]
  unfold rqC13ends at hr
  split_ifs at hr
  · rw [List.mem_singleton] at hr
    subst hr
    simp only [fieldReq, bval_bin]
    exact field_le_fixedLen _ (Dims.secChain_lt_nSec _) (Nat.zero_le _)
  · rw [List.mem_singleton] at hr
    subst hr
    simp only [fieldReq, bval_bin]
    exact field_le_fixedLen _ (Dims.secChain_lt_nSec _) (by rw [hc]; unfold finP; omega)
  · simp at hr

/-- The requested length of C13ends: one chain field. -/
def totC13 (D : Dims) : ℕ := D.width D.secChain

theorem total_rqC13ends_le (dims : ℕ → Dims) (z : List Bool × List Bool) :
    P1Batch.total (rqC13ends dims z) ≤ totC13 (dims (P1Batch.bval z.1)) := by
  unfold rqC13ends
  split_ifs <;> simp [P1Batch.total, fieldReq, bval_bin, totC13]

/-- **Family 13 (C13ends), program.** -/
theorem progC13ends (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hM : ∀ n, (dims n).fixedLen ≤ M n)
    (hrq : Poly (fun z : List Bool × List Bool => (rqC13ends dims z, z)))
    (hdec : Poly (decC13ends b l))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC13 (dims n))) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw b l dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  progFamily dims M K hb hl hM (rqC13ends dims) (decC13ends b l) (C13endsw b l dims) hrq hdec totC13
    (total_rqC13ends_le dims) hfb (addr_rqC13ends dims) (hckC13ends b l dims)

end P1ChkFinal
