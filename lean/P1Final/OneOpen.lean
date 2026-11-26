import P1Final.W2Closed
import P1Wrap.W3Done

/-!
# P1Final.OneOpen: W2 and W3 are closed; C1 from the ONE remaining open part, P11 (owner: P1-lean-integ)

Lane wrap closed W3 at 11:33Z (2026-11-25): `P1Wrap.W3.port_wrapper : P1Int.PortWrapper`
(research/p1/lean/Wrap/P1Wrap/W3Done.lean, job p1w-55). The lane files are used UNCHANGED (copies of
research/p1/lean/Wrap/P1Wrap and of the P1Hier files they import; 8 OpenAI files of openai/math@3344da5 that
were not yet in this project: IntegerMultiplication/Carry/{Shrink,Small,Wide}, Toom/{Evaluate,Model,Recursive,Use},
Bits/Multiply).
So `C1Challenge.c1` now follows from ONE open Prop: P11, in either form
`P1Int.LemmaPOfPort PortTwo` or `PortTwo → ∃ j, P1Int.P11.CountHyp (2^-j)`.
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- **W3, closed** (lane wrap). -/
theorem w3_closed : P1Int.PortWrapper := P1Wrap.W3.port_wrapper

/-- **C1 from Lemma P** (the one open part of Case 2). -/
theorem c1_of_lemmaP (p11 : P1Int.LemmaPOfPort PortTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_open_parts p11 w3_closed w2_closed

/-- **C1 from the count hypothesis of P11** (`CountHyp` at a dyadic `s` from the port). -/
theorem c1_of_countHyp
    (p11 : PortTwo → ∃ j : ℕ, P1Int.P11.CountHyp ((2 : ℝ) ^ (-(j : ℤ)))) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_count_parts p11 w3_closed w2_closed

end P1Final
