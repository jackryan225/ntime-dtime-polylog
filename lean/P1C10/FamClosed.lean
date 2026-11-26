import P1C10.Fam
import P1SolC10F.Fmt10Cut
import P1SolC10F.Size10Cut

/-!
# P1C10.FamClosed: family 9 (check C10) of the dispatcher, closed up to the witness fit (lane P1-lean-c10wire)

Sol P1-sol-fmt10 (DONE 14:05Z, runner check round 1) proved the two format facts; its files are compiled UNCHANGED
(research/p1/lean/C10/accepted/P1SolC10F.sha256: Fmt10Cut.lean c30d9ebf.., Size10Cut.lean 5f209cfc..).
`famC10_closed`: family 9 as `FamProg` with the ONLY input `hfit` (the witness fit for `n ≥ n₀`, the same Prop as the
`hfit` of `P1ProgDir.FamDir.famC2`; `genD = DirFinal.gD` by `rfl`).
-/

namespace P1C10

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int

/-- Statement checks: the delivered theorems have exactly the target types. -/
example : Fmt10CutTarget := P1SolC10F.fmt10Cut
example : Size10CutTarget := P1SolC10F.size10Cut

/-- **Family 9 (C10) as `FamProg`**, closed up to the witness fit. -/
theorem famC10_closed {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias n₀ : ℕ) {s : ℝ} (hs : s ≤ 1) (hb : 1 ≤ b)
    (hfit : ∀ n, n₀ ≤ n → (genD Bt Kc V aM a b d bigBias termBias n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C10w (fx10 Bt) (cutDims n₀ (genD Bt Kc V aM a b d bigBias termBias)) x u i))
      s a b cc n₂ :=
  famC10 Bt Kc V aM a b d bigBias termBias n₀ hs hb hfit P1SolC10F.fmt10Cut P1SolC10F.size10Cut

/-- `genD` is the dims function of the ProgDir families (`P1ProgDir.DirFinal.gD`), so one fit lemma serves both. -/
example {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias n : ℕ) :
    genD Bt Kc V aM a b d bigBias termBias n = P1ProgDir.DirFinal.gD Bt Kc V aM a b d bigBias termBias n := rfl

end P1C10

#print axioms P1C10.famC10_closed
