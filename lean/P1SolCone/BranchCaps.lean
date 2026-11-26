import P1SolCone.NumericLevel
import OAI.Computability.VPVNP.IteratedCompression

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel
open scoped Classical

/-- Uniform caps for the width lists and the predecessor enumeration at every phase. -/
def BranchCapsOK {R : Type} [CommSemiring R] {b n : ℕ} (c w : ℕ) :
    {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) → E.Choices → Prop
  | _, _, X, .done _, _ => X.maxWireWidth ≤ w
  | _, _, X, .more p tail, sel => X.maxWireWidth ≤ w ∧
      (∀ v, Fintype.card ((p.step.term sel.1).Preimage v) ≤ c) ∧
      BranchCapsOK c w (tail sel.1) sel.2

private theorem peak_mono {R : Type} {N Y : Network} (t : TermChain R N Y) {x y : ℕ} (h : x ≤ y) :
    t.peak x ≤ t.peak y := by
  cases t with
  | done => exact h
  | more => exact max_le_max h le_rfl

private theorem peak_cast {R : Type} {N N' Y : Network} (e : N' = N) (t : TermChain R N Y) (w : ℕ) :
    (e.symm ▸ t : TermChain R N' Y).peak w = t.peak w := by
  subst N'
  rfl

theorem branchCaps_of_peak {R : Type} [CommSemiring R] {b n a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {c w : ℕ} :
    ∀ (rec : E.Records) (sel : E.Choices), E.Bounded c rec →
      (E.termChain rec sel).peak X.maxWireWidth ≤ w → BranchCapsOK c w E sel := by
  induction E with
  | done => exact fun _ _ _ h => h
  | more p tail ih =>
    intro rec sel hb hpeak
    have h := hb.1 sel.1
    have hN : ∀ v, Fintype.card ((p.step.term sel.1).Preimage v) ≤ c :=
      fun v => (Nat.le_add_left _ _).trans (h.1 v)
    refine ⟨((StateExecution.termChain _ rec sel).le_peak _).trans hpeak, hN, ?_⟩
    let dat := TermChain.largest (rec.1 sel.1)
    let t := (tail sel.1).termChain (rec.2 sel.1) sel.2
    have htail : ((p.output_eq sel.1).symm ▸ t : TermChain R (p.step.term sel.1).output _).peak dat ≤ w :=
      (le_max_right _ _).trans hpeak
    rw [peak_cast (p.output_eq sel.1) t dat] at htail
    exact ih sel.1 (rec.2 sel.1) sel.2 (hb.2 sel.1) ((peak_mono t h.2.2).trans htail)

/-- The compressor's record bound controls each predecessor list. Its growth bound
controls the old widths at every phase as well as the terminal payload widths. -/
theorem branchCaps_execute {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ) {n : ℕ}
    (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (sel : (B.execute κ hκ T h X).Choices) :
    BranchCapsOK B.recordLimit (B.growthConstant ^ T * (X.maxWireWidth + 1)) (B.execute κ hκ T h X) sel := by
  let r := B.recordBounds κ hκ
  have hB := Procedure.repeat_recordBounds r (n - T * S.laneBits) T n (Nat.add_sub_of_le h).symm X
  have hb : (B.execute κ hκ T h X).Bounded B.recordLimit (B.records κ hκ T h X) := hB.1
  have hG := Procedure.repeat_history_growth r (show 1 ≤ B.recordLimit from le_max_left _ _) (n - T * S.laneBits)
    T n (Nat.add_sub_of_le h).symm X sel
  refine branchCaps_of_peak _ _ _ hb ?_
  exact (Nat.le_succ _).trans (hG.2.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (le_max_right 2 _) T)))

theorem BranchCapsOK.monoWidth {R : Type} [CommSemiring R] {b n a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {c w w' : ℕ} (h : w ≤ w') :
    ∀ sel : E.Choices, BranchCapsOK c w E sel → BranchCapsOK c w' E sel := by
  induction E with
  | done => exact fun _ hb => hb.trans h
  | more p tail ih => exact fun sel hb => ⟨hb.1.trans h, hb.2.1, ih sel.1 sel.2 hb.2.2⟩

theorem BranchCapsOK.finalWidth {R : Type} [CommSemiring R] {b n a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {c w : ℕ} :
    ∀ sel : E.Choices, BranchCapsOK c w E sel → (E.finalState sel).maxWireWidth ≤ w := by
  induction E with
  | done => exact fun _ hb => hb
  | more p tail ih => exact fun sel hb => ih sel.1 sel.2 hb.2.2

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.branchCaps_execute
