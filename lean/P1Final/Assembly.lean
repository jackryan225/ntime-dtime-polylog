import P1Int.Interfaces
import OAI.Computability.MultitapeWeakETH.Price

/-!
# P1Final.Assembly: `C1Challenge.c1` from the two cases (skeleton, parts as hypotheses)

Owner: P1-lean-integ. The proof splits on `PortTwo = PortOver (AlgebraicClosure (ZMod 2))` (patched
OpenAI `Price.lean`, field-uniform.patch + port-over.patch).
* Case 1 (`PriceTwo = ¬ PortTwo`): lane case1, `P1Case1.c1_of_priceTwo_of_parts` and successors.
* Case 2 (`PortTwo`): P11 (`PortTwo → LemmaP s`) + W3 (`port_wrapper`) + W2 (`parity_hierarchy`),
  see `P1Final.Case2` (needs `P1Int.LemmaP`).
When every part is proved, `P1Final.c1` has no hypotheses and `Check/SameStatement` compares its type with
`C1Challenge.c1` of the Challenge file.
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- `C1Conclusion` unfolds to the type of `C1Challenge.c1`. -/
theorem c1Conclusion_iff : P1Int.C1Conclusion ↔ ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  Iff.rfl

/-- **W4.** The case split. -/
theorem c1_of_cases (case1 : PriceTwo → P1Int.C1Conclusion) (case2 : PortTwo → P1Int.C1Conclusion) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  by_cases h : PortTwo
  · exact case2 h
  · exact case1 h

end P1Final
