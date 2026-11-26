import P1Wit.Layout
import Mathlib.Data.List.OfFn

namespace P1SolFmt.SolFormat

open P1Wit

theorem offAt_ofFn (c w : ℕ → ℕ) (s : ℕ) :
    (List.ofFn (fun i : Fin s => c i.val * w i.val)).sum = offAt c w s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.sum_append, List.sum_singleton, offAt]
    exact congrArg (· + c s * w s) ih

end P1SolFmt.SolFormat
