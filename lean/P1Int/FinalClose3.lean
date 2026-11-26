import P1Int.FinalClose
import P1SolCone.WHyp

/-!
# The cone input closed (P1-lean-integ): `ConeTargetIn` from `P1SolCone.whyp_cone` (Sol cone, PROVED by eval, p11_cone).
`FinalInputs3` = `GreedyIn` ∧ `DispIn` ∧ `EnergyFitIn` (greedy, disp, greedy); `openChecksRec_of_inputs3`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

theorem coneTargetIn_proved {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (d : ℕ)
    (bs : Module.Basis (Fin d) (ZMod 2) F) : ConeTargetIn Bt κ hκ d bs :=
  fun V a b bigBias termBias _ => P1SolCone.whyp_cone Bt κ hκ V a b d bigBias termBias _ bs

/-- **The inputs still owed after the cone and factor0 proofs**: greedy bridges, dispatcher, energy fit. -/
def FinalInputs3 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Module.Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant →
    haveI : Fintype F := Fintype.ofFinite F
    GreedyIn Bt κ hκ D ∧ DispIn Bt κ hκ D bs l ∧ EnergyFitIn Bt κ hκ D

theorem finalInputs2_of_3 (h : FinalInputs3) : FinalInputs2 := by
  intro S Bt F _ _ _ _ κ hκ D bs l hl1 hlane hgrow
  letI : Fintype F := Fintype.ofFinite F
  have h3 := h S Bt F κ hκ D bs l hl1 hlane hgrow
  exact ⟨coneTargetIn_proved Bt κ hκ D bs, h3.1, h3.2.1, h3.2.2⟩

theorem openChecksRec_of_inputs3 (h : FinalInputs3) : OpenChecksRec :=
  openChecksRec_of_inputs2 (finalInputs2_of_3 h)

end P11

end P1Int

#print axioms P1Int.P11.openChecksRec_of_inputs3
