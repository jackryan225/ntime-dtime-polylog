import C1Challenge.C1U
import P1Final.LemmaPClosed

/-!
# P1Final.C1UAssembly: C1-U from the two case targets of the worker P1-astra-c1u (P1-lean-integ, 2026-11-25)
-/

open OAI.Computability.MultitapeWeakETH (PortTwo PriceTwo)

/-- Target of `P1C1U.caseA` (no ports in characteristic two). -/
def P1Final.C1UCaseA : Prop := ∀ (_price : PriceTwo),
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)

/-- Target of `P1C1U.caseB` (ports). -/
def P1Final.C1UCaseB : Prop := ∀ (_p11 : P1Int.LemmaPOfPort PortTwo) (_port : PortTwo),
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)

theorem P1Final.c1u_of_cases (hA : P1Final.C1UCaseA) (hB : P1Final.C1UCaseB) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ (C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
        C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) := by
  by_cases h : PortTwo
  · obtain ⟨σ, hσ, L, hL, hnot⟩ := hB P1Final.lemmaP_port_closed h
    exact ⟨σ, hσ, L, hL, fun hboth => hnot hboth.2⟩
  · obtain ⟨σ, hσ, L, hL, hnot⟩ := hA h
    exact ⟨σ, hσ, L, hL, fun hboth => hnot hboth.1⟩

open Lean in
run_meta do
  let env ← getEnv
  let some x := env.find? ``C1Challenge.c1u | throwError "C1Challenge.c1u not found"
  let some y := env.find? ``P1Final.c1u_of_cases | throwError "c1u_of_cases not found"
  let .forallE _ _ (.forallE _ _ body _) _ := y.type | throwError "unexpected shape"
  unless x.type == body do throwError "CONCLUSION DIFFERS FROM C1Challenge.c1u"
  logInfo "the conclusion of P1Final.c1u_of_cases is exactly the type of C1Challenge.c1u (as terms)"

#print axioms P1Final.c1u_of_cases
