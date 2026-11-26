import P1Final.Assembly
import P1Int.LemmaP

/-!
# P1Final.Case2: the port case from P11, W3 and W2 (parts as hypotheses)
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- Case 2 from its three parts: P11 (`PortTwo → LemmaP s`, dyadic `s`), W3 and W2. -/
theorem case2_of_parts (p11 : P1Int.LemmaPOfPort PortTwo) (w3 : P1Int.PortWrapper)
    (w2 : P1Int.ParityHierarchy) (port : PortTwo) : P1Int.C1Conclusion := by
  obtain ⟨s, j, -, hs, hP⟩ := p11 port
  exact w3 s j hs hP w2

/-- **C1 from all open parts.** Case 1 enters as one implication (lane case1); Case 2 as P11, W3, W2. -/
theorem c1_of_parts (case1 : PriceTwo → P1Int.C1Conclusion) (p11 : P1Int.LemmaPOfPort PortTwo)
    (w3 : P1Int.PortWrapper) (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_cases case1 (case2_of_parts p11 w3 w2)

end P1Final
