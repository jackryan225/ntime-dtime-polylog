import P1SolC10SA.Shrink
import P1C10.Code

/-!
# P1, check C10, SHRINKING substep: closed (lane P1-lean-c10)

The shrink program of the Sol prover P1-sol-c10sa (`P1SolC10SA.shrinkProgram`, folder P1SolC10SA/, 13 files compiled
UNCHANGED) has exactly the type of the target `P1C10.ShrinkProgram` (statement check `shrinkProgram_proved`). With it
the shrink stage lemma on codes holds for one explicit polynomial-time recomputation per substep (fixed `a`, `b`,
`ready`), for every lane dimension `g`, with no hypothesis on the recomputation left.
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

section Shrink

variable {a b : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- Statement check: the prover's theorem has exactly the type of the target T2. -/
theorem shrinkProgram_proved : ShrinkProgram B ready := P1SolC10SA.shrinkProgram B ready

/-- **C10 at a shrinking substep, closed**: one polynomial-time recomputation on codes for which C10 on codes passes at
every level-`ℓ+1` address iff the stored level-`ℓ+1` panels are the true ones (for every lane dimension `g`). -/
theorem shrink_code_stage_closed :
    ∃ rcS : ShrinkIn → Option PanelCode, Poly rcS ∧ ShrinkCodeOK B ready rcS ∧
      ∀ (g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
        (s : X.ShrinkSelection B),
        (D.lv ℓ).bases = Fintype.card X.Base →
        (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) →
        (∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ)) →
        (∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y)) →
        (∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y) →
        (rdLayout D u ℓ = if layoutBit B X s then 1 else 0) →
        ((∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sCode rcS a b g D u ℓ Y) ↔
          ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y)) := by
  obtain ⟨rcS, hp, hok⟩ := shrinkProgram_proved B ready
  exact ⟨rcS, hp, hok, fun g D u ℓ X s hN hP hcol hoff hterm hlay =>
    C10sCode_stage B ready hok g D u ℓ X s hN hP hcol hoff hterm hlay⟩

end Shrink

end P1C10
