import P1ChkFinal.FamGreedy
import P1SolFmt.FmtG
import P1Int.WitnessFit

/-!
# P1ChkFinal.FamGreedyGenuine: C5 and C9 as `FamProg` at the genuine dims (format input discharged)

Lane P1-lean-checks (2026-11-25). `FamGreedy.famC5`, `famC9` need `FmtHypGreedy dims (lpM2 s a b)`; Sol P1-sol-fmtg proved
it at the genuine dims with the witness length `Params.m Kc (lpTime a b n)` (`P1SolFmt.fmtHypGreedy_genuine`, file
ChkFinal/P1SolFmt/FmtG.lean, copied unchanged; runner LEAN CHECK passed), and `P1Int.P11.m_eq_lpM2` turns that length
into `lpM2 (2^-Kc.j) a b n`.
-/

namespace P1ChkFinal.FamGreedy

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1Int P1SolGreedy P1SolGreedy.SolDemand

open Classical

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
  (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)

theorem fmtHypGreedy_lpM2 :
    FmtHypGreedy
      (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b) := by
  have e : (fun n => P1Wrap.Params.m Kc (lpTime a b n)) = lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b :=
    funext fun n => P11.m_eq_lpM2 Kc a b n
  rw [← e]
  exact P1SolFmt.fmtHypGreedy_genuine A Kc V aM a b d bigBias termBias

/-- **C5 (family 4) as `FamProg` at the genuine dims**, `s = 2^-Kc.j`. -/
theorem famC5_genuine (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C5fam (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d
        bigBias termBias) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC5 _ hs hb (fmtHypGreedy_lpM2 A Kc V aM a b d bigBias termBias)

/-- **C9 (family 8) as `FamProg` at the genuine dims**, `s = 2^-Kc.j`. -/
theorem famC9_genuine (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C9fam (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d
        bigBias termBias) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC9 _ hs hb (fmtHypGreedy_lpM2 A Kc V aM a b d bigBias termBias)

end P1ChkFinal.FamGreedy

#print axioms P1ChkFinal.FamGreedy.famC5_genuine
#print axioms P1ChkFinal.FamGreedy.famC9_genuine
