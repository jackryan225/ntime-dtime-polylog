import P1SolGreedy.DemandWidthCore

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif

namespace P1SolGreedy

attribute [local instance] P1P7.instDecEqBase

theorem dw_correct {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
    (hm : P1ChkGreedy.IsMotif X (packingArcEquiv X.Base a g ((y, k), w))) :
    P1SolGreedy.DW (a := a) (g := g) (D := D) u ℓ (P1P7.addr X y) (P1ChkGreedy.keyOf a g k w) =
      P1ChkGreedy.demandW X ⟨_, hm⟩ :=
  dw_correct_from_panels D u ℓ X hpan hcol y k w hm

#print axioms dw_correct

end P1SolGreedy
