import P1Wrap.Main
import P1Wrap.InnerImpl

/-!
# W3 with piece B (InnerImpl) proved

`port_wrapper_of_outer`: `P1Int.PortWrapper` from two inputs only:
* `Easy Inner.unG` (splitting `withGuess w x` into `(w, x)`; text of `P1Hier.UM.unGuess`, input h1 of lane hier B);
* `∀ j a b, OuterTask j a b` (piece C: the outer verifier `V*` as an OpenAI task, `P1Wrap/TaskProg.lean`).
-/

namespace P1Wrap.W3

theorem port_wrapper_of_outer (hUG : OAI.Computability.IntegerMultiplication.Code.Easy Inner.unG)
    (hO : ∀ j a b, OuterTask j a b) : P1Int.PortWrapper :=
  port_wrapper_of_impls (fun j a b => Inner.innerImpl_of hUG j a b)
    (fun j a b => outerImpl_of_task (hO j a b))

end P1Wrap.W3
