import P1Final.Open3
import P1Case1.Table

/-!
# P1Final.Case1: Case 1 and C1 from the open parts (owner: P1-lean-integ, one copy since the restart of 2026-11-25)

Update of the restart (2026-11-25, P1-lean-integ): Case 1 is CLOSED (`P1Final.c1_of_priceTwo_final`, from
`P1Case1.c1_of_priceTwo` and `P1Case1.ntime_coTRANS`; lean4lean 61,566 declarations, p1intB-13). So
`c1_of_open_parts` now takes ONLY the three Case 2 Props: P11 (`LemmaPOfPort PortTwo`), W3 (`PortWrapper`),
W2 (`ParityHierarchy`). The five-hypothesis form of copy A (09:11Z) is kept as `c1_of_open_parts_five`, and
`case1_of_parts` as before; their two Case 1 inputs are now theorems (`P1Case1.Entropy.transEntropyBound`,
`P1Case1.ntime_coTRANS`), see `c1_of_open_parts_eq`.
The lane files are used UNCHANGED (copies of research/p1/lean/Case1/P1Case1, without CoTransRefute.lean).
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- Case 1 from its two inputs (copy A, 09:11Z). -/
theorem case1_of_parts (ent : P1Case1.TransEntropyBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog P1Case1.coTRANS) : PriceTwo → P1Int.C1Conclusion :=
  P1Case1.c1_of_priceTwo_of_entropy ent upper

/-- Case 1, closed: no hypothesis besides `PriceTwo`. -/
theorem case1_closed : PriceTwo → P1Int.C1Conclusion := c1_of_priceTwo_final

/-- **C1 from the three open parts of Case 2** (P11, W3, W2). The final theorem is
`c1_of_open_parts p11 w3 w2` once the three lane theorems exist. -/
theorem c1_of_open_parts (p11 : P1Int.LemmaPOfPort PortTwo) (w3 : P1Int.PortWrapper)
    (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_case2_parts p11 w3 w2

/-- The five-hypothesis form of copy A (09:11Z), kept for the record. -/
theorem c1_of_open_parts_five (ent : P1Case1.TransEntropyBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog P1Case1.coTRANS) (p11 : P1Int.LemmaPOfPort PortTwo)
    (w3 : P1Int.PortWrapper) (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_parts (case1_of_parts ent upper) p11 w3 w2

/-- The two Case 1 inputs of the five-hypothesis form are theorems: the old form, applied to them, is
the new one. -/
theorem c1_of_open_parts_eq (p11 : P1Int.LemmaPOfPort PortTwo) (w3 : P1Int.PortWrapper)
    (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_open_parts_five (P1Case1.Entropy.transEntropyBound _) P1Case1.ntime_coTRANS p11 w3 w2

end P1Final
