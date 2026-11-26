import P1ChkFinal.FamC7R
import P1ProgDir.FamDirReal
import P1SolFmt.FamAnd
import P1SolFmt.DirFit
import P1SolGreedy.GreedyStepShrink

/-!
# P1ChkFinal.FamClosed: family programs with NO open input at the real / genuine parameters (lane P1-lean-greedy)

Sol/Astra files copied UNCHANGED (runner LEAN CHECK passed, each read): P1SolFmt/FamAnd.lean (Sol famand, sha256 69b9947d..),
P1SolFmt/DirFit.lean (Sol dirfit, 2dab97f0..), P1SolGreedy/GreedyStepShrink.lean (Astra grshrink, fe633eda..).
* family 6 = `C7all` (D15): `famC7all_genuine` (conjunction of `famC7_genuine` and `c7rProg` by `famProg_and`);
* families 0, 1, 2, 14: `famC1_closed` .. `famC14_closed` (FamDirReal with the fit `dirFit`);
* the greedy stage at shrinking levels: `greedyShrinkStage` (type check below).
-/

namespace P1ChkFinal.FamClosed

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1Int P1Int.P11 P1ChkFinal.C7R P1ChkFinal.FmtAgTarget P1ChkFinal.FamGreedy P1ProgDir.DirFit

open Classical in
/-- **Family 6 (C7 at shrinking and refresh levels) as `FamProg` at the genuine dims, NO open input.** -/
theorem famC7all_genuine {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)
    {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C7all S.graph (Nat.two_pow_pos S.expanderExponent)
        (S.port_bound.connected_and_pos S.port_order).1 A.refresh B (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC7all_of_and P1SolFamAnd.famProg_and A Kc V aM a b d bigBias termBias B hs hb

open Classical

section

universe u v

variable {k : Type u} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {R : Type v}
  [CommRing R] (κ : Bt.Entry → R) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
  (hs : (2 : ℝ) ^ (-((portConsts Bt).j : ℤ)) ≤ 1) (hb : 1 ≤ b)

include κ hκ hs hb in
/-- **Family of C1 as `FamProg` at the real parameters, NO open input.** -/
theorem famC1_closed : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C1F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ :=
  famC1_real P1SolDirFit.dirFit.{u, v} Bt κ hκ V a b d bigBias termBias hs hb

include κ hκ hs hb in
/-- **Family of C2 as `FamProg` at the real parameters, NO open input.** -/
theorem famC2_closed : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C2F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ :=
  famC2_real P1SolDirFit.dirFit.{u, v} Bt κ hκ V a b d bigBias termBias hs hb

include κ hκ hs hb in
/-- **Family of C3 as `FamProg` at the real parameters, NO open input.** -/
theorem famC3_closed : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C3F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ :=
  famC3_real P1SolDirFit.dirFit.{u, v} Bt κ hκ V a b d bigBias termBias hs hb

include κ hκ hs hb in
/-- **Family of C14 as `FamProg` at the real parameters, NO open input.** -/
theorem famC14_closed : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C14F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K)
      (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ :=
  famC14_real P1SolDirFit.dirFit.{u, v} Bt κ hκ V a b d bigBias termBias hs hb


end

/-- Type check of the Astra delivery: the shrinking-level stage. -/
example {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor) :
    P1ChkFinal.GreedyStep.ShrinkStageTarget B :=
  P1SolGreedy.greedyShrinkStage B

end P1ChkFinal.FamClosed

#print axioms P1ChkFinal.FamClosed.famC7all_genuine
#print axioms P1ChkFinal.FamClosed.famC1_closed
#print axioms P1ChkFinal.FamClosed.famC14_closed
