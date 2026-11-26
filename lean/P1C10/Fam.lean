import P1C10.Fix
import P1C10.Fmt10Defs
import P1ChkFinal.BatchLink
import P1SolFmt.Length
import P1ProgDir.FamTask

/-!
# P1C10.Fam: family 9 (check C10) of the dispatcher in the form `P1Int.P11.FamProg` (lane P1-lean-c10wire)

`famC10`: the program of family 9, `ck 9 x u i = decide (C10w (fx10 Bt) (cutDims n₀ G) x u i)` with `G = genD ..` the
genuine dims, from `progC10_proved` (Sol c10prog, c10-28) with: `batchHyp` (P1ChkFinal.BatchLink), `lenHyp` (Sol fmt),
`hM` from the fit `hfit` (`cutDims_fixedLen_le`), `hS`, `hR` from `fx10` (Fix.lean), and the two format facts of the
cut dims (`Fmt10CutTarget`, `Size10CutTarget`, Sol P1-sol-fmt10) as hypotheses until they are delivered. The converter
`P1ProgDir.famProg_of_task` (Sol famtask) gives the family form of the integration (as `P1ChkFinal.FamFinal.famC11`).
For `|x| ≥ n₀` the family is C10 at the genuine dims (`cutDims_of_le`).
-/

namespace P1C10

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int

/-- **Family 9 (C10) as `FamProg`** at the cut genuine dims, from the fit and the two format facts. -/
theorem famC10 {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias n₀ : ℕ) {s : ℝ} (hs : s ≤ 1) (hb : 1 ≤ b)
    (hfit : ∀ n, n₀ ≤ n → (genD Bt Kc V aM a b d bigBias termBias n).fixedLen ≤ lpM2 s a b n)
    (hF : Fmt10CutTarget) (hZ : Size10CutTarget) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C10w (fx10 Bt) (cutDims n₀ (genD Bt Kc V aM a b d bigBias termBias)) x u i))
      s a b cc n₂ := by
  obtain ⟨c, T⟩ := progC10_proved (fx10 Bt) (cutDims n₀ (genD Bt Kc V aM a b d bigBias termBias)) (lpM2 s a b)
    (fun n => lpK2 a b n - 4) P1ChkFinal.batchHyp P1SolFmt.SolLength.lenHyp
    (cutDims_fixedLen_le n₀ _ _ hfit) (hF Bt Kc V aM a b d bigBias termBias n₀)
    (hZ Bt Kc V aM a b d bigBias termBias n₀) (fx10_rcS_poly Bt) (fx10_rcR_poly Bt)
  exact P1ProgDir.famProg_of_task hs hb _ c T

end P1C10

#print axioms P1C10.famC10
