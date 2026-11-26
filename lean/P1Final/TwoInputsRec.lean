import P1Final.TwoInputs
import P1Int.WitfillGlue

/-!
# P1Final.TwoInputsRec: `C1Challenge.c1` from the network count and the checks in witfill form (owner: P1-lean-integ)

`P1Int.P11.OpenChecks` follows from `P1Int.P11.OpenChecksRec` (`P1Int.P11.openChecks_of_rec`): the order of the
final sites, the witness code and its injectivity are Sol witfill's (`P1Int.WitfillLink`). Left open:
`OpenNetP4` (lane net) and `OpenChecksRec` (programs, totality, the true records, `hchecks` for witfill's code).
-/

namespace P1Final

/-- **C1 from the network count and the checks in witfill form.** -/
theorem c1_of_net_and_checksRec (hnet : P1Int.P11.OpenNetP4) (hchk : P1Int.P11.OpenChecksRec) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_net_and_checks hnet (P1Int.P11.openChecks_of_rec hchk)

end P1Final
