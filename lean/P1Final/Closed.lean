import C1Challenge.Statement
import P1Final.NetP4
import P1Int.FinalClose5
import P1ChkFinal.GreedyBridgeCheck

/-!
# The time separation theorem, closed (P1-lean-integ)

`P1Final.openChecksRec_closed : P1Int.P11.OpenChecksRec`: `openChecksRec_of_inputs5` with its one input `GreedyIn` given
by the two bridges `P1SolGreedy.bridgeShrinkE`, `P1SolGreedy.bridgeRefreshE` (Astra P1-astra-grbridge, lane P1-lean-greedy).
`P1Final.c1_closed`: the text of `C1Challenge.c1`, from `P1Final.c1_of_checksRec`.
The check below compares the type of `c1_closed` with the type of `C1Challenge.c1` as terms.
-/

/-- **The one open statement of the final theorem, proved.** -/
theorem P1Final.openChecksRec_closed : P1Int.P11.OpenChecksRec :=
  P1Int.P11.openChecksRec_of_inputs5 (fun _S Bt _F _ _ _ _ κ hκ D V a b x bigBias termBias hH hE =>
    ⟨P1SolGreedy.bridgeShrinkE Bt κ hκ V a b x D bigBias termBias hH hE,
      P1SolGreedy.bridgeRefreshE Bt κ hκ V a b x D bigBias termBias hH hE⟩)

/-- **The time separation theorem** (the text of `C1Challenge.c1`), with no hypothesis. -/
theorem P1Final.c1_closed :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  P1Final.c1_of_checksRec P1Final.openChecksRec_closed

open Lean in
run_meta do
  let env ← getEnv
  let some x := env.find? `C1Challenge.c1 | throwError "C1Challenge.c1 not found"
  let some y := env.find? `P1Final.c1_closed | throwError "P1Final.c1_closed not found"
  unless y.type == x.type do throwError "the type of P1Final.c1_closed differs from the type of C1Challenge.c1"
  let some z := env.find? `P1Final.openChecksRec_closed | throwError "openChecksRec_closed not found"
  unless z.type == mkConst ``P1Int.P11.OpenChecksRec do throwError "openChecksRec_closed does not have type OpenChecksRec"
  logInfo m!"P1Final.c1_closed has exactly the type of C1Challenge.c1 (as terms); openChecksRec_closed : OpenChecksRec"

/-- The statement of `C1Challenge.c1`, as an `example`. -/
example : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := P1Final.c1_closed

#print axioms P1Final.openChecksRec_closed
#print axioms P1Final.c1_closed
