import P1Case1.Entropy

/-!
# P1, Case 1: the conditional theorem with only the NTIME upper bound left open (milestone 5)

`PriceTwo` (no ports over the algebraic closure of `ZMod 2`) and `NTIMELinLog coTRANS` give the statement of
`C1Challenge.c1` with `σ = 1/4` and `L = coTRANS`. The TRANS lower bound (trace side, table side, entropy
side) is fully proved from `PriceTwo`.
-/

namespace P1Case1

open OAI.Computability.MultitapeWeakETH (PriceTwo PriceOver)

/-- **The TRANS decision lower bound from the absence of ports over any infinite field** (Challenge
machine model): every deterministic multitape machine deciding TRANS at side `N` within `T` steps has
`T ≥ c_M · 2N² √(log₂ 2N²)` for all large `N`. -/
theorem transLowerBound_of_price_over (k : Type) [Field k] [Infinite k] (price : PriceOver k) :
    TransLowerBound :=
  transLowerBound_of_fieldTable (transFieldTableBound_of_entropy price (Entropy.transEntropyBound k))

/-- **The TRANS decision lower bound in characteristic two.** -/
theorem transLowerBound_of_priceTwo (price : PriceTwo) : TransLowerBound :=
  transLowerBound_of_price_over (AlgebraicClosure (ZMod 2)) price

/-- **Case 1 of C1.** -/
theorem c1_of_priceTwo (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_priceTwo_of_entropy (Entropy.transEntropyBound _) upper price

/-- Case 1, every exponent below `1/2`, one language. -/
theorem coTRANS_separates_of_priceTwo (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceTwo) :
    C1Challenge.NTIMELinLog coTRANS ∧ ∀ σ : ℝ, 0 ≤ σ → σ < 1/2 →
      ¬ C1Challenge.DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  coTRANS_separates (transLowerBound_of_priceTwo price) upper

/-- Without the upper bound: coTRANS is not in `DTIME(n (log n)^σ)` for any `0 ≤ σ < 1/2`. -/
theorem coTRANS_not_dtime_of_priceTwo (price : PriceTwo) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1/2) :
    ¬ C1Challenge.DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  not_dtimeIn_coTRANS_of_lt (transLowerBound_of_priceTwo price) h0 h1

end P1Case1
