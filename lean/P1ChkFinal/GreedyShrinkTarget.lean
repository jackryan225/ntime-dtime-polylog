import P1SolGreedy.GreedyStages

/-!
# P1ChkFinal.GreedyShrinkTarget: the greedy step at a SHRINKING level, stage form (statement; lane P1-lean-greedy)

At a shrinking level `ℓ` whose stored panels are the true panels of the state `X` (premise of the group: `c4G` for `ℓ = 0`,
`c10G (ℓ - 1)` else), the five greedy families at the indices of the level pass exactly when the stored level-`ℓ` data are
the true data for some shrink selection `s` (`ShrinkTrue`): colours (C5), offsets (C6), terms (C7, `s`), energy prefixes (C8),
layout bit (C9). Pieces: `C5fam_level`, `C5chk_iff'`, `C5u_iff`; `C6fam_level`, `C6chk_iff`, `C6u_iff`; `C7fam_certifies`,
`C8fam_certifies` (Sol greedyprog2, GreedyStages.lean); `C9chk_iff`. The bridge from `ShrinkTrue` to `greedyG ℓ` is the
integration lemma (the same as the stub of `C7RTests.greedy_refresh_step`).
-/

namespace P1ChkFinal.GreedyStep

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1Wit P1ChkGreedy P1SolGreedy P1SolGreedy.SolDemand

section

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- **The stored data of a shrinking level are the true ones** for some shrink selection `s`. -/
def ShrinkTrue {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g)) : Prop :=
  (∀ z, rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ)) ∧
    (∀ z, rdOffset D u ℓ (P1P7.addr X z) = P1ChkFinal.bwNum (X.packingData.offset z)) ∧
    ∃ s : X.ShrinkSelection B, (∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e)) ∧
      (∀ y l, rdEnergy D u ℓ (P1P7.addr X y) (eCode l) = truePrefix X (termW B X s) y l) ∧ C9u D u ℓ X

/-- **Target of the shrinking-level stage** (statement only). -/
def ShrinkStageTarget : Prop :=
  ∀ {a g ℓ : ℕ} {X : State a (packingLaneBits a g)} (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool),
    ℓ ≤ (Dn x.length).top → ((Dn x.length).lv ℓ).shrink = true →
    ((Dn x.length).lv ℓ).bases = Fintype.card X.Base → ((Dn x.length).lv ℓ).slots = 2 ^ a →
    ag x.length ℓ = (a, g) →
    (∀ z : X.Base, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X z) (P1P7.panel X z)) →
    (((∀ Y < ((Dn x.length).lv ℓ).bases, C5fam Dn x u (encIdx (Dn x.length) ℓ Y)) ∧
      (∀ Y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ Y)) ∧
      (∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < termStride (ag x.length) ℓ,
        C7fam B Dn ag x u (encTermIdx (Dn x.length) (ag x.length) ℓ Y key)) ∧
      (∀ Y < ((Dn x.length).lv ℓ).bases, C8fam B Dn ag x u (encIdx (Dn x.length) ℓ Y)) ∧
      C9fam Dn x u ℓ) ↔
      ShrinkTrue B (Dn x.length) u ℓ X)

end

end P1ChkFinal.GreedyStep
