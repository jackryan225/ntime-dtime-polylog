import P1Final.Main
import P1Int.Assembly

/-!
# P1Final.TwoInputs: `C1Challenge.c1` from the two lane-level inputs (owner: P1-lean-integ)

`P1Int.P11.OpenP11` is split by `P1Int.P11.openP11_of_parts` into
* `P1Int.P11.OpenNetP4` (lane net + P1-astra-contract): the routed network count, and
* `P1Int.P11.OpenChecks` (check lanes, P5, Sol provers, Sol witfill): programs, totality, witness code, and
  "all checks accept `u` iff `u` is the code of a valid tuple", at the FIXED parameters of `P1Int.Assembly`.
FINAL STEP: `theorem P1Final.c1 := c1_of_net_and_checks <net theorem> <checks theorem>`.
-/

namespace P1Final

/-- **C1 from the two lane-level inputs.** -/
theorem c1_of_net_and_checks (hnet : P1Int.P11.OpenNetP4) (hchk : P1Int.P11.OpenChecks) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_openP11 (P1Int.P11.openP11_of_parts hnet hchk)

end P1Final
