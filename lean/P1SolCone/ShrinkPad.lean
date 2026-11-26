import P1SolCone.ExecutionCone
import P1SolCone.BranchCaps
import P1P5.Generic
import P1P5.EvalExec

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel OAI.Computability.VPVNP.CompressorRecords
open OAI.Computability.VPVNP.Compression.ShrinkMotif OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion OAI.Computability.VPVNP.MotifSelector
open OAI.Computability.VPVNP.PairSimulation.LocalHistory
open OAI.Computability.IntegerMultiplication.Code P1P7

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The internal fields are an actual subset of the resident motif records.
Their finite product has at most one bit per unit of total internal width. -/
theorem shrinkWordCount_le {a b g : ℕ} {δ factor : ℝ} {k : Type} [Field k]
    (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass)
      (realWidths supplyMass) (31 / 16) factor)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    {R : Type} [CommRing R] (κ : (parameterData B).Entry → R)
    (hκ : (parameterData B).IsSolution κ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (x : X.Base) (j : TagW a) (l : BitWord g) :
    shrinkWordCount B X s x j l ≤
      2 ^ (State.shrinkHistoryFactor B a b ^ 2 * (X.maxWireWidth + 1)) := by
  classical
  let v := ((x, j), l)
  let p := X.shrinkStatePass B κ hκ ready
  let r := p.slotRecords (X.shrinkExtraRecords B κ hκ ready) s
  let C := State.shrinkHistoryFactor B a b
  let L := layoutBit B X s
  let A := {u : X.packingData.Motif × Fin 4 // v = X.packingData.shrinkInternalOwner L u}
  let field : A → (r v).Field := fun u => Sum.inl (Sum.inl ⟨u.1, u.2.symm⟩)
  have inj : Function.Injective field := by
    intro u u' he
    have hs : (⟨u.1, u.2.symm⟩ : {e : X.packingData.Motif × Fin 4 //
        X.packingData.shrinkInternalOwner L e = v}) = ⟨u'.1, u'.2.symm⟩ :=
      Sum.inl.inj (Sum.inl.inj he)
    exact Subtype.ext (congrArg (fun e : {e : X.packingData.Motif × Fin 4 //
      X.packingData.shrinkInternalOwner L e = v} => e.val) hs)
  have hb := X.shrinkStatePass_bounded B κ hκ ready s
  have hcount : Fintype.card A ≤ C := calc
    _ ≤ Fintype.card (r v).Field := Fintype.card_le_of_injective field inj
    _ ≤ (r v).count := by unfold SiteRecords.count; omega
    _ ≤ (r v).count + Fintype.card ((p.step.term s).Preimage v) := Nat.le_add_right _ _
    _ ≤ C := hb.1 v
  have hlargest : (r v).largest ≤ C * (X.maxWireWidth + 1) :=
    (Finset.le_sup (f := fun w => (r w).largest) (Finset.mem_univ v)).trans
      ((Nat.le_succ _).trans hb.2.1)
  let W := selW B X s
  have hfld (u : A) : W u.1.1 (!L, u.1.2) ≤ C * (X.maxWireWidth + 1) :=
    ((r v).width_le_largest (field u)).trans hlargest
  change Nat.card (Placed (X.packingData.shrinkInternalOwner L) (internalLabel W L) v) ≤ _
  let eq := P1P5.placedEquiv (X.packingData.shrinkInternalOwner L) (internalLabel W L) v
  rw [Nat.card_congr eq]
  change Nat.card ((u : A) → Fin (2 ^ W u.1.1 (!L, u.1.2))) ≤ _
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    _ ≤ Fintype.card A * (C * (X.maxWireWidth + 1)) := by
      calc
        _ ≤ ∑ _ : A, C * (X.maxWireWidth + 1) := Finset.sum_le_sum fun u _ => hfld u
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ C * (C * (X.maxWireWidth + 1)) := Nat.mul_le_mul_right _ hcount
    _ = C ^ 2 * (X.maxWireWidth + 1) := by ring

/-- A single tally supplies every shrink in a cone whose old widths are at most `w`. -/
def conePad (C w : ℕ) : Tally := tally (2 ^ (C ^ 2 * (w + 1)))

theorem conePad_dom {X : Type*} (C : ℕ) (w : X → ℕ) (hw : ∀ x, 1 ≤ w x) :
    Dom (fun x => 2 ^ (C * w x)) (fun x => (conePad C (w x)).length) := by
  apply ((Dom.base (fun x => 2 ^ (C * w x))).pow (2 * C)).mono
  intro x
  rw [conePad, tally_length, ← pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    _ ≤ C ^ 2 * (2 * w x) := Nat.mul_le_mul_left _ (by have := hw x; omega)
    _ = C * w x * (2 * C) := by ring

theorem originPad_of_width {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)
    {a g b n w : ℕ} {X : State a g} {p : StatePass R X b n}
    (origin : PassOrigin B κ hκ p) (s : p.step.Choice) (hw : X.maxWireWidth ≤ w) :
    OriginPadOK B κ hκ (conePad B.growthConstant w) origin s := by
  cases origin with
  | shrink i hm X =>
    subst_vars
    intro x j l
    have hC : State.shrinkHistoryFactor B.shrink (S.degreeExponent i.castSucc)
        (S.degreeExponent i.succ) ≤ B.growthConstant := by
      apply le_trans _ (P1P5.recordLimit_le_growth B)
      unfold BlockSchedule.Templates.recordLimit
      have hi := Finset.le_sup (f := fun j : Fin S.steps =>
        State.shrinkHistoryFactor B.shrink (S.degreeExponent j.castSucc)
          (S.degreeExponent j.succ)) (Finset.mem_univ i)
      exact Nat.le_trans hi (Nat.le_trans (le_max_left _ _) (le_max_right _ _))
    rw [conePad, tally_length]
    exact (shrinkWordCount_le B.shrink (S.shrink i) (κ ∘ Sum.inl) ((B.solution_iff κ).mp hκ).1
      X s x j l).trans (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul (Nat.pow_le_pow_left hC _) (Nat.succ_le_succ hw)))
  | refresh X => trivial

theorem branchPad_of_caps {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)
    {a g b n c w : ℕ} {X : State a g} (E : StateExecution R b n X)
    (origins : PassOrigins B κ hκ E) (s : E.Choices) (hc : BranchCapsOK c w E s) :
    BranchPadOK B κ hκ (conePad B.growthConstant w) E origins s := by
  induction E with
  | done => trivial
  | more p tail ih =>
    exact ⟨originPad_of_width B κ hκ origins.1 s.1 hc.1, ih s.1 (origins.2 s.1) s.2 hc.2.2⟩

end

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.branchPad_of_caps
