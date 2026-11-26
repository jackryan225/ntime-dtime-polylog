import P1Final.Case1Final
import P1Final.Case2

/-!
# P1Final.Open3: C1 from the THREE remaining open parts (owner: copy B; G3-chief 09:40:16Z)

Case 1 is closed (`c1_of_priceTwo_final`). Open: P11 (`LemmaPOfPort PortTwo`), W3 (`PortWrapper`),
W2 (`ParityHierarchy`). Copy A's `c1_of_open_parts` (five hypotheses) is kept unchanged in P1Final.Case1.
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- **C1 from the three open parts of Case 2.** -/
theorem c1_of_case2_parts (p11 : P1Int.LemmaPOfPort PortTwo) (w3 : P1Int.PortWrapper)
    (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_parts c1_of_priceTwo_final p11 w3 w2

end P1Final
