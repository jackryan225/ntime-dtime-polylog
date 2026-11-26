import P1Final.C1UAssembly
import P1C1U.CaseA
import P1C1U.CaseB

/-!
# P1Final.C1UClosed: C1-U (paper, Theorem "Uplus", without H1-H12) closed (P1-lean-integ, 2026-11-25)

`P1Final.c1u_of_cases` (case split on PortTwo, with `P1Final.lemmaP_port_closed`) and the two cases of the Astra worker
P1-astra-c1u (runner-clean round 9): `P1C1U.caseA` (no ports: L = TRANS, Lemma A for nondeterministic machines) and
`P1C1U.caseB` (ports: the parity wrapper).
-/

theorem P1Final.c1u_closed :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ (C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
        C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) :=
  P1Final.c1u_of_cases (fun price => P1C1U.caseA price) (fun p11 port => P1C1U.caseB p11 port)

open Lean in
run_meta do
  let env ← getEnv
  let some x := env.find? ``C1Challenge.c1u | throwError "C1Challenge.c1u not found"
  let some y := env.find? ``P1Final.c1u_closed | throwError "P1Final.c1u_closed not found"
  unless x.type == y.type do throwError "TYPES DIFFER"
  logInfo "P1Final.c1u_closed has exactly the type of C1Challenge.c1u (as terms)"

example : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
    ¬ (C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) := P1Final.c1u_closed

#print axioms P1C1U.caseA
#print axioms P1C1U.caseB
#print axioms P1Final.c1u_closed
