import C1Challenge.C1U

/-!
# UTIME and the second sentence of Theorem "Uplus" (statement; P1-lean-integ, 2026-11-25)

NEW file; Statement.lean, NTime.lean, C1U.lean unchanged. Paper, Definition "Classes", item 5: "UTIME(f): languages A for
which some NTM M runs in time O(f), has acc(M,x) ≤ 1 on every input, and x ∈ A ⇔ acc(M,x) = 1." Theorem "Uplus":
"... L ∉ NTIME(n (log n)^σ) ∩ ⊕TIME(n (log n)^σ). In particular coNTIME[n; 2 log n] ⊄ UTIME(n (log n)^σ)."
-/

namespace C1Challenge

/-- `L ∈ UTIME(C (f n + 1))`: every computation halts within `T ≤ C (f |x| + 1)` steps, there is at most one accepting
computation, and `L x = true` iff there is exactly one. -/
def UTIMEIn (L : List Bool → Bool) (f : ℕ → ℝ) : Prop :=
  ∃ (M : NMachine) (C : ℝ), ∀ x : List Bool, ∃ T : ℕ, (T : ℝ) ≤ C * (f x.length + 1) ∧
    (∀ c, ¬ M.Reach (M.init x) (T + 1) c) ∧ M.acc x ≤ 1 ∧ (L x = true ↔ M.acc x = 1)

/-- **Theorem "Uplus", both sentences, one σ, one L** (without H1-H12). TARGET. -/
theorem c1u_utime : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, coNTIMELinLog L ∧
    ¬ (NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) ∧
    ¬ UTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  sorry

end C1Challenge
