import P1ChkFinal.GreedyIndex
import P1ChkFinal.C7RTests
import P1SolGreedy.GreedyStepShrink

/-!
# P1ChkFinal.GreedyStepAll: the greedy step at a SHRINKING level, D5 index form, family 6 = C7all (lane P1-lean-greedy)

Over all indices of the level (`lev c i = i % 2^L` for the families 4-7, `lev 8 i = i`), with the integration bridge as a
hypothesis (`hbridge`: premise ⇒ (`ShrinkTrue` ↔ `G`)), as `C7RTests.greedy_refresh_step` at refresh levels.
Pieces: `GreedyIndex` (index conversion), `C7all_shrink_iff` (D15), `P1SolGreedy.greedyShrinkStage` (Astra grshrink).
-/

namespace P1ChkFinal.GreedyIndex

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1SolGreedy P1ChkFinal.C7R

variable {a₀ dH aR : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ aR)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
  (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- **The greedy step at a shrinking level** (all indices of the level; family 6 = `C7all`). -/
theorem greedy_shrink_step (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {a g ℓ : ℕ}
    (X : State a (packingLaneBits a g)) (hℓ : ℓ ≤ (Dn x.length).top) (hS : ((Dn x.length).lv ℓ).shrink = true)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hslots : ((Dn x.length).lv ℓ).slots = 2 ^ a)
    (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (Pre G : Prop) (hbridge : Pre → (P1ChkFinal.GreedyStep.ShrinkTrue B (Dn x.length) u ℓ X ↔ G)) (hpre : Pre) :
    ((∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C5fam Dn x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C6fam Dn ag x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7all P hdH hconn F B Dn ag x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C8fam B Dn ag x u i) ∧ (∀ i, i = ℓ → C9fam Dn x u i)) ↔ G := by
  have h7 : (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7all P hdH hconn F B Dn ag x u i) ↔
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7fam B Dn ag x u i) :=
    forall_congr' fun i => forall_congr' fun hi =>
      C7all_shrink_iff P hdH hconn F B Dn ag x u i (by rw [hi]; exact hS)
  rw [h7, C5_all_iff Dn x u hℓ hS, C6_all_iff Dn x u ag hℓ hS, C7_all_iff Dn x u B ag hℓ hS,
    C8_all_iff Dn x u B ag hℓ hS, C9_all_iff, ← hbridge hpre]
  exact P1SolGreedy.greedyShrinkStage B Dn ag x u hℓ hS hN hslots hag hpan

end P1ChkFinal.GreedyIndex

#print axioms P1ChkFinal.GreedyIndex.greedy_shrink_step
