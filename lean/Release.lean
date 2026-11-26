import C1Challenge.Statement
import C1Challenge.NTime
import C1Challenge.C1U
import C1Challenge.UTime
import C1Challenge.UTimeGuards
import P1Final.Closed
import P1Final.NTimeClosed
import P1Final.C1UClosed
import P1Final.UTimeClosed

/-!
# Release check

The four theorems of this release. Each closed file already compares the type of its theorem with the type of the
target in the Mathlib-only statement files (`C1Challenge/*.lean`) by a `run_meta` check. The same comparison is repeated
here, and the axioms are printed. Expected: `[propext, Classical.choice, Quot.sound]` for each, no `sorryAx`.
-/

open Lean in
run_meta do
  let env ← getEnv
  for (target, proved) in [(``C1Challenge.c1, ``P1Final.c1_closed),
      (``C1Challenge.c1_ntime, ``P1Final.c1_ntime_closed),
      (``C1Challenge.c1u, ``P1Final.c1u_closed),
      (``C1Challenge.c1u_utime, ``P1Final.c1u_utime_closed)] do
    let some x := env.find? target | throwError "{target} not found"
    let some y := env.find? proved | throwError "{proved} not found"
    unless x.type == y.type do throwError "the type of {proved} differs from the type of {target}"
    logInfo m!"{proved} has exactly the type of {target} (as terms)"

#print axioms P1Final.c1_closed
#print axioms P1Final.c1_ntime_closed
#print axioms P1Final.c1u_closed
#print axioms P1Final.c1u_utime_closed
