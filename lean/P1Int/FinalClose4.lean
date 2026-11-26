import P1Int.FinalClose3
import P1Int.DispFam

/-!
# The dispatcher closed (P1-lean-integ): `DispIn` from `P1Int.P11.Disp.dispIn` (lane P1-lean-disp, PROVED, disp-9).
`FinalInputs4` = `GreedyIn` ∧ `EnergyFitIn` (lane P1-lean-greedy); `openChecksRec_of_inputs4`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- **The inputs still owed**: the two greedy bridges (with the energy fit `hE`) and the energy fit for long inputs. -/
def FinalInputs4 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ),
    GreedyIn Bt κ hκ D ∧ EnergyFitIn Bt κ hκ D

theorem finalInputs3_of_4 (h : FinalInputs4) : FinalInputs3 := by
  intro S Bt F _ _ _ _ κ hκ D bs l _ _ _
  letI : Fintype F := Fintype.ofFinite F
  have h2 := h S Bt F κ hκ D
  exact ⟨h2.1, Disp.dispIn Bt κ hκ D bs l, h2.2⟩

theorem openChecksRec_of_inputs4 (h : FinalInputs4) : OpenChecksRec :=
  openChecksRec_of_inputs3 (finalInputs3_of_4 h)

end P11

end P1Int

#print axioms P1Int.P11.openChecksRec_of_inputs4
