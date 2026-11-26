import P1ChkFinal.ProgClosed
import P1ProgDir.FamTask

/-!
# P1ChkFinal.FamFinal: the programs of C11, C12, C13ends at the genuine dims in the form `P1Int.P11.FamProg`

Lane P1-lean-checks (2026-11-25). `ProgClosed.lean` gives the Task forms on `QDom M K` at the genuine dims with no open
input; with `M := lpM2 s a b`, `K := fun n => lpK2 a b n - 4` the converter `P1ProgDir.famProg_of_task` (Sol
P1-sol-famtask, ProgDir/P1ProgDir/FamTask.lean, sha256 630b6102...) gives the family form of the integration
(ComposeFam.lean), with `ck := fun x u i => decide (Ckw (genuine dims) x u i)`.
-/

namespace P1ChkFinal.FamFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int

open scoped Classical

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
  (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)

/-- Family 11 (C12) as `FamProg`, genuine dims, no input. -/
theorem famC12 {s : ℝ} (hs : s ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C12w (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d
        bigBias termBias) x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := progC12_genuine A Kc V aM a b d bigBias termBias (lpM2 s a b) (fun n => lpK2 a b n - 4)
  exact P1ProgDir.famProg_of_task hs hb _ c T

/-- Family 10 (C11) as `FamProg`, genuine dims, no input. -/
theorem famC11 {s : ℝ} (hs : s ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C11w (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d
        bigBias termBias) x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := progC11_genuine A Kc V aM a b d bigBias termBias (lpM2 s a b) (fun n => lpK2 a b n - 4)
  exact P1ProgDir.famProg_of_task hs hb _ c T

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- Family 13 (C13ends) as `FamProg`, genuine dims, no input. -/
theorem famC13ends (bs : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {s : ℝ} (hs : s ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C13endsw bs l (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d
        bigBias termBias) x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := progC13ends_genuine bs l A Kc V aM a b d bigBias termBias (lpM2 s a b) (fun n => lpK2 a b n - 4)
  exact P1ProgDir.famProg_of_task hs hb _ c T

end P1ChkFinal.FamFinal

#print axioms P1ChkFinal.FamFinal.famC12
#print axioms P1ChkFinal.FamFinal.famC11
#print axioms P1ChkFinal.FamFinal.famC13ends
