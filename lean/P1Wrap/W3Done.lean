import P1Wrap.W3Final
import P1Wrap.OuterProgram

/-!
# W3 PROVED: `P1Wrap.W3.port_wrapper : P1Int.PortWrapper`

* piece A (parameters): `P1Wrap/ParamTask.lean`;
* piece B (`InnerImpl`): `P1Wrap/Inner*.lean`, with `Easy Inner.unG` from lane hier B's `P1Hier.UM.easy_unGuess`
  (`Inner.unG` and `P1Hier.UM.unGuess` have the same text; `unG_eq` below);
* piece C (`OuterTask`): `P1Wrap/Outer{Decode,Task,Program}.lean` (prover P1-astra-outer, two repairs by
  P1-lean-wrap), with W1 = `P1Hier.check_task_of_phases` (lane hier, hier-53).
-/

namespace P1Wrap.W3

theorem unG_eq : ∀ l : List Bool, Inner.unG l = P1Hier.UM.unGuess l
  | [] => rfl
  | [true] => rfl
  | false :: r => rfl
  | true :: b :: r => by
      simp only [Inner.unG, P1Hier.UM.unGuess, unG_eq r]

theorem easy_unG : OAI.Computability.IntegerMultiplication.Code.Easy Inner.unG := by
  have e : Inner.unG = P1Hier.UM.unGuess := funext unG_eq
  rw [e]
  exact P1Hier.UM.easy_unGuess

/-- **W3** (task W3 of the P1 plan): Lemma P with a dyadic constant and the parity hierarchy give the
conclusion of `C1Challenge.c1`. -/
theorem port_wrapper : P1Int.PortWrapper :=
  port_wrapper_of_outer easy_unG outerTask_all

end P1Wrap.W3
