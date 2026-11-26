import P1SolGreedy.GreedyBridgeShrink
import P1SolGreedy.GreedyBridgeRefresh
import P1SolGreedy.GreedyBridgeEnergy
import P1ChkFinal.GreedyBridgeE
import P1ChkFinal.EnergyFitProof

/-!
# P1ChkFinal.GreedyBridgeCheck: integration of Astra P1-astra-grbridge (lane P1-lean-greedy, D16)

Files copied unchanged into `ChkFinal/P1SolGreedy/` (sha256 = DONE.md of the worker). The two bridges have the exact target
types; with `greedyFieldE` they give the field `D5Steps.greedy` at every input with `hH` and `hE`
(`greedyFieldClosed`), and `hE` holds for long inputs (`energyFitLong`, two independent proofs).
-/

namespace P1ChkFinal.GreedyBridgeCheck

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

example {k : Type} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) :
    P1ChkFinal.GreedyBridge.BridgeShrinkTargetE Bt κ hκ V a b x d bigBias termBias hH hE ∧
      P1ChkFinal.GreedyBridge.BridgeRefreshTargetE Bt κ hκ V a b x d bigBias termBias hH hE :=
  ⟨P1SolGreedy.bridgeShrinkE Bt κ hκ V a b x d bigBias termBias hH hE,
    P1SolGreedy.bridgeRefreshE Bt κ hκ V a b x d bigBias termBias hH hE⟩

example : P1ChkFinal.EnergyFit.EnergyFitLong := P1SolGreedy.energyFitLong
example : P1ChkFinal.EnergyFit.EnergyFitLong := P1ChkFinal.EnergyFitProof.energyFitLong

/-- **The field closed** from the two bridges (the hypotheses of `GreedyFieldTarget` discharged). -/
theorem greedyFieldClosed {k : Type} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) :
    P1ChkFinal.GreedyBridge.GreedyFieldTargetE Bt κ hκ V a b x d bigBias termBias hH hE ∧
      P1ChkFinal.GreedyBridge.BridgeShrinkTargetE Bt κ hκ V a b x d bigBias termBias hH hE ∧
      P1ChkFinal.GreedyBridge.BridgeRefreshTargetE Bt κ hκ V a b x d bigBias termBias hH hE :=
  ⟨P1ChkFinal.GreedyBridge.greedyFieldE Bt κ hκ V a b x d bigBias termBias hH hE,
    P1SolGreedy.bridgeShrinkE Bt κ hκ V a b x d bigBias termBias hH hE,
    P1SolGreedy.bridgeRefreshE Bt κ hκ V a b x d bigBias termBias hH hE⟩

example {k : Type} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) : True := by
  have _h := P1ChkFinal.GreedyBridge.greedyFieldE Bt κ hκ V a b x d bigBias termBias hH hE
    (P1SolGreedy.bridgeShrinkE Bt κ hκ V a b x d bigBias termBias hH hE)
    (P1SolGreedy.bridgeRefreshE Bt κ hκ V a b x d bigBias termBias hH hE)
  trivial

end P1ChkFinal.GreedyBridgeCheck

#print axioms P1SolGreedy.bridgeShrinkE
#print axioms P1SolGreedy.bridgeRefreshE
#print axioms P1SolGreedy.energyFitLong
#print axioms P1ChkFinal.GreedyBridgeCheck.greedyFieldClosed
