import P1Int.FinalClose4
import P1ChkFinal.EnergyFitProof

/-!
# The energy fit closed (P1-lean-integ): `EnergyFitIn` from `P1ChkFinal.EnergyFitProof.energyFitLong`
(lane P1-lean-greedy, PROVED, grd-56). `FinalInputs5` = `GreedyIn` (the two bridges with `hE`); `openChecksRec_of_inputs5`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- **The inputs still owed**: the two greedy bridges (with the energy fit `hE`), at every port. -/
def FinalInputs5 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ),
    GreedyIn Bt κ hκ D

theorem finalInputs4_of_5 (h : FinalInputs5) : FinalInputs4 :=
  fun S Bt F _ _ _ _ κ hκ D =>
    ⟨h S Bt F κ hκ D, energyFitIn_of_long P1ChkFinal.EnergyFitProof.energyFitLong Bt κ hκ D⟩

theorem openChecksRec_of_inputs5 (h : FinalInputs5) : OpenChecksRec :=
  openChecksRec_of_inputs4 (finalInputs4_of_5 h)

end P11

end P1Int

#print axioms P1Int.P11.openChecksRec_of_inputs5
