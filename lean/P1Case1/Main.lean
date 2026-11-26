import P1Case1.Display

/-!
# P1, Case 1: the main conditional theorem (milestone 3)

The TRANS trace bound is now a theorem (`transTraceBound`, from the display machine of
`P1Case1.Display`). Case 1 of C1 depends only on:
* the TRANS table bound over the algebraic closure of `ZMod 2` from `PriceTwo` (tasks G3 + G4),
* the NTIME upper bound for coTRANS (task C1).
-/

namespace P1Case1

open OAI.Computability.MultitapeWeakETH (PriceTwo PriceOver)

/-- **The TRANS trace bound (tasks G1 + G2), proved.** -/
theorem transTraceBound : TransTraceBound :=
  transTraceBound_of_display Display.transDisplayBound

/-- The TRANS lower bound for OpenAI's machines from the table bound alone. -/
theorem transLowerBoundOAI_of_table (table : TransTableBound) : TransLowerBoundOAI :=
  transLowerBoundOAI_of_bounds transTraceBound table

/-- The Challenge-model TRANS lower bound from the field table bound over any infinite field. -/
theorem transLowerBound_of_fieldTable {K : Type*} [Field K] [Infinite K]
    (h : TransFieldTableBound K) : TransLowerBound :=
  transLowerBound_of_oai (transLowerBoundOAI_of_table (transTableBound_of_field h))

/-- **Case 1, milestone 3, any infinite field.** -/
theorem c1_of_price_over_of_table (k : Type) [Field k] [Infinite k]
    (fieldTable : PriceOver k → TransFieldTableBound k)
    (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceOver k) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_price_over_of_parts k transTraceBound fieldTable upper price

/-- **Case 1, milestone 3, characteristic two.** The statement of `C1Challenge.c1` from `PriceTwo`, the
TRANS field table bound over the algebraic closure of `ZMod 2`, and the NTIME upper bound of coTRANS. -/
theorem c1_of_priceTwo_of_table
    (fieldTable : PriceTwo → TransFieldTableBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_priceTwo_of_parts transTraceBound fieldTable upper price

/-- Every exponent below `1/2`, one language. -/
theorem coTRANS_separates_of_table
    (fieldTable : PriceTwo → TransFieldTableBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceTwo) :
    C1Challenge.NTIMELinLog coTRANS ∧ ∀ σ : ℝ, 0 ≤ σ → σ < 1/2 →
      ¬ C1Challenge.DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  coTRANS_separates (transLowerBound_of_fieldTable (fieldTable price)) upper

end P1Case1
