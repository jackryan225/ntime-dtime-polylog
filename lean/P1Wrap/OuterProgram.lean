import P1Wrap.OuterTask
import P1Wrap.ParamTask
import P1Wrap.TaskProg
import P1Hier.UTSplit
import P1Hier.CheckAssembly

/-! # The outer task and its raw-input stack program -/

namespace P1Wrap.W3

open OAI.Computability.IntegerMultiplication.Code
open PT (ParamPad)

open Classical in
theorem outerTask_of {j a b : ℕ} (hu : Easy P1Hier.UM.unGuess)
    (hW1 : Task P1Hier.checkBudget send (fun i : P1Hier.MCode × List Bool × ℕ × List P1Hier.Entry =>
      send (decide (P1Hier.Check i.1 i.2.1 i.2.2.1 i.2.2.2)))) : OuterTask j a b :=
  fun M => AstraOuter.outer_task M (PT.paramPad j a b) hu hW1

open Classical in
theorem outerImpl_of {j a b : ℕ} (hP : ParamPad j a b) (hu : Easy P1Hier.UM.unGuess)
    (hW1 : Task P1Hier.checkBudget send (fun i : P1Hier.MCode × List Bool × ℕ × List P1Hier.Entry =>
      send (decide (P1Hier.Check i.1 i.2.1 i.2.2.1 i.2.2.2)))) : OuterImpl j a b :=
  outerImpl_of_task (fun M => AstraOuter.outer_task M hP hu hW1)

/-- The parameter task, input splitter and universal checker supply every input. -/
theorem outerTask_all (j a b : ℕ) : OuterTask j a b :=
  outerTask_of (j := j) (a := a) (b := b) P1Hier.UM.easy_unGuess P1Hier.check_task_of_phases

theorem outerImpl_all (j a b : ℕ) : OuterImpl j a b :=
  outerImpl_of_task (outerTask_all j a b)

end P1Wrap.W3

#print axioms P1Wrap.W3.outerImpl_of
#print axioms P1Wrap.W3.outerTask_all
#print axioms P1Wrap.W3.outerImpl_all
