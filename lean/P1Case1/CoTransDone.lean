import P1Case1.CoTransVerifier
import P1Case1.CoTransLoops

/-!
# P1, Case 1, task C1: `NTIMELinLog coTRANS` (lane case1b, copies A and B)

The verifier `verifier rest` (`CoTransVerifier.lean`, copy A: read the guess, decode `i` and `k`) with the
part `rest` of copy B (`CoTransLoops.lean`: compute `N` from `|x| = 2N²`, check `i, k < N`, compare
`x[N i + k]` with `x[N² + N k + i]`), compiled by OpenAI's `compile_program` and copied into the Challenge
machine model (`CoTransMain.lean`, `CoTransBridge.lean`).
-/

namespace P1Case1.CoTransV

open OAI.Computability.IntegerMultiplication C1Challenge

/-- **C1: coTRANS is in `NTIMELinLog`** (the canonical text of `C1Challenge.Statement`). -/
theorem ntime_coTRANS : NTIMELinLog coTRANS :=
  ntime_coTRANS_of_rest P1Case1.CoTrans.rest 300 (fun Γ r x i k h0 h5 h6 hz => by
    classical
    obtain ⟨r', hr, hv⟩ := P1Case1.CoTrans.run_rest Γ x i k r h0 h5 h6 hz
    exact ⟨r', _, hr, hv, by simp [P1Case1.CoTrans.VerdictIK]⟩)

end P1Case1.CoTransV

namespace P1Case1

/-- The name of the target in the lane brief. -/
theorem ntime_coTRANS : C1Challenge.NTIMELinLog coTRANS := CoTransV.ntime_coTRANS

end P1Case1

#print axioms P1Case1.ntime_coTRANS
