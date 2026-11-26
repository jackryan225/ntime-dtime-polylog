import P1Final.P11Link
import P1Hier.W2Link
import P1Hier.UTFinal

/-!
# P1Final.W2Closed: W2 is closed; C1 from the TWO remaining open parts (owner: P1-lean-integ)

Lanes hier (copy A) and hierB closed the parity hierarchy at 11:31Z (2026-11-25): `P1Hier.parityHierarchy`
(P1Hier/W2Link.lean, route `Hierarchy.parity_hierarchy_of`) and `P1Hier.UM.parityHierarchy_closed`
(P1Hier/UTFinal.lean), two terms of the shared Prop `P1Int.ParityHierarchy`. The lane files are used UNCHANGED
(copies of research/p1/lean/Hier/P1Hier). So `C1Challenge.c1` now follows from two open Props:
P11 (`LemmaPOfPort PortTwo`, or `CountHyp` at a dyadic `s` from the port) and W3 (`PortWrapper`).
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- **W2, closed** (lane hier, copy A's route). -/
theorem w2_closed : P1Int.ParityHierarchy := P1Hier.parityHierarchy

/-- **W2, closed**, second term (lane hierB's route). -/
theorem w2_closed' : P1Int.ParityHierarchy := P1Hier.UM.parityHierarchy_closed

/-- **C1 from the two open parts of Case 2** (P11 and W3). -/
theorem c1_of_two_parts (p11 : P1Int.LemmaPOfPort PortTwo) (w3 : P1Int.PortWrapper) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_open_parts p11 w3 w2_closed

/-- **C1 from W3 and the count hypothesis of P11** (`CountHyp` at a dyadic `s` from the port). -/
theorem c1_of_count_two
    (p11 : PortTwo → ∃ j : ℕ, P1Int.P11.CountHyp ((2 : ℝ) ^ (-(j : ℤ))))
    (w3 : P1Int.PortWrapper) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_count_parts p11 w3 w2_closed

end P1Final
