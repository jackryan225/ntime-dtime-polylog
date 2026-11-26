import P1ChkFinal.GreedyFieldCheck
import P1ChkFinal.EnergyFit

/-!
# P1ChkFinal.GreedyBridgeE: the greedy targets with the energy fit `hE` (decision D16; lane P1-lean-greedy)

Each target gets ONE extra hypothesis `hE : EnergyFitTarget ..` right after `hH` (integ, board 14:52Z). The bodies are the
statements of GreedyBridge.lean / GreedyFieldTarget.lean unchanged; the proofs may use `hE` (it is a binder of each theorem).
`greedyFieldE` holds already (Sol grfield, `greedyField_of_bridges`).
-/

namespace P1ChkFinal.GreedyBridge

open P1Int P1Int.P11 P1ChkFinal.EnergyFit

variable {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
  (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)

set_option linter.unusedVariables false in
/-- The shrinking bridge with the energy fit. -/
def BridgeShrinkTargetE (hE : EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) : Prop :=
  BridgeShrinkTarget Bt κ hκ V a b x d bigBias termBias hH

set_option linter.unusedVariables false in
/-- The refresh bridge with the energy fit. -/
def BridgeRefreshTargetE (hE : EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) : Prop :=
  BridgeRefreshTarget Bt κ hκ V a b x d bigBias termBias hH

set_option linter.unusedVariables false in
/-- The field with the energy fit (its bridges are the `E` forms). -/
def GreedyFieldTargetE (hE : EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) : Prop :=
  P1ChkFinal.GreedyField.GreedyFieldTarget Bt κ hκ V a b x d bigBias termBias hH

/-- **The field with `hE`, from the two bridges** (Sol grfield). -/
theorem greedyFieldE (hE : EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) :
    GreedyFieldTargetE Bt κ hκ V a b x d bigBias termBias hH hE :=
  P1ChkFinal.GreedyField.greedyField_of_bridges Bt κ hκ V a b x d bigBias termBias hH

end P1ChkFinal.GreedyBridge

#print axioms P1ChkFinal.GreedyBridge.greedyFieldE
