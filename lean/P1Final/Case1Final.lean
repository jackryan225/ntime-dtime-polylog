import P1Case1.Case1
import P1Case1.CoTransDone

/-!
# P1Final.Case1Final: the first complete Lean theorem of P1 (owner: P1-lean-integ copy B)

Assigned by G3-chief (board 09:40:16Z). Lane files used UNCHANGED: research/p1/lean/Case1/P1Case1
(lanes case1 and case1b; CoTransRefute.lean not imported). Challenge: research/p1/lean/Challenge/C1Challenge/
Statement.lean (sha256 7f00493145c53b33b79ed358c17aebcedf21ae22b557293af8fcf10102890bd4).

In words: if characteristic 2 has no ports (`PriceTwo` = no port inequality over the algebraic closure of
`ZMod 2`, OpenAI's `PortOver` patched to an arbitrary field), then some language in linear nondeterministic
time with `⌊2 log₂ n⌋` guess bits is not in deterministic time `O(n (log₂ n)^{1/4})`; the language is the
complement of matrix transposition.
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- **Case 1, closed.** No ports in characteristic two implies the statement of `C1Challenge.c1`. -/
theorem c1_of_priceTwo_final (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  P1Case1.c1_of_priceTwo P1Case1.ntime_coTRANS price

/-- **Case 1, explicit witness.** `σ = 1/4`, `L = coTRANS`. -/
theorem coTRANS_separates_of_priceTwo_final (price : PriceTwo) :
    C1Challenge.NTIMELinLog P1Case1.coTRANS ∧
      ¬ C1Challenge.DTIMEIn P1Case1.coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ (1/4 : ℝ)) :=
  ⟨P1Case1.ntime_coTRANS, P1Case1.not_dtimeIn_coTRANS (P1Case1.transLowerBound_of_priceTwo price)⟩

end P1Final
