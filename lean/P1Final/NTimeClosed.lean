import C1Challenge.NTime
import P1Final.Closed
import P1NTime.Inclusion

/-!
# P1Final.NTimeClosed: both sentences of the paper's main theorem (P1-lean-integ, 2026-11-25)

`P1Final.c1_closed` (the first sentence, `C1Challenge.c1`) and `P1NTime.ntime_of_ntimeLinLog` (NTIME[n; 2 log n] ⊆
NTIME(n), Astra worker P1-astra-ntime, runner-clean round 6) give the text of `C1Challenge.c1_ntime`
(Challenge/C1Challenge/NTime.lean): one sigma, one language, in NTIME[n; 2 log n] and in NTIME(n), not in
DTIME(n (log n)^sigma).
-/

theorem P1Final.c1_ntime_closed :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ C1Challenge.NTIMEIn L (fun n => (n : ℝ)) ∧
        ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  obtain ⟨σ, hσ, L, h1, h2⟩ := P1Final.c1_closed
  exact ⟨σ, hσ, L, h1, P1NTime.ntime_of_ntimeLinLog h1, h2⟩

open Lean in
run_meta do
  let env ← getEnv
  let some x := env.find? ``C1Challenge.c1_ntime | throwError "C1Challenge.c1_ntime not found"
  let some y := env.find? ``P1Final.c1_ntime_closed | throwError "P1Final.c1_ntime_closed not found"
  unless x.type == y.type do throwError "TYPES DIFFER"
  logInfo "P1Final.c1_ntime_closed has exactly the type of C1Challenge.c1_ntime (as terms)"

example : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    C1Challenge.NTIMELinLog L ∧ C1Challenge.NTIMEIn L (fun n => (n : ℝ)) ∧
      ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  P1Final.c1_ntime_closed

#print axioms P1NTime.ntime_of_ntimeLinLog
#print axioms P1Final.c1_ntime_closed
