import P1ChkFinal.GreedyFieldTarget
import P1SolFmt.GrField

/-!
# P1ChkFinal.GreedyFieldCheck: owner type check of Sol grfield (file P1SolFmt/GrField.lean UNCHANGED, sha256 b033af4f..)
The field `greedy` now follows from the two bridges (Astra P1-astra-grbridge).
-/

namespace P1ChkFinal.GreedyField

theorem greedyField_of_bridges {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias) :
    GreedyFieldTarget Bt κ hκ V a b x d bigBias termBias hH :=
  P1SolGrField.greedyField Bt κ hκ V a b x d bigBias termBias hH

end P1ChkFinal.GreedyField

#print axioms P1ChkFinal.GreedyField.greedyField_of_bridges
