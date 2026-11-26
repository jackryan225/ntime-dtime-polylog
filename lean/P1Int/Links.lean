import P1Int.Interfaces
import P1Hier.Defs

/-!
# P1Int.Links: lane copies of the interface definitions are the same definitions (owner: copy B)

Lane hier keeps its own copies (P1Hier.Defs) of `ParDecidesFrom`, `rootLog`, `G`. The final assembly needs
them to agree with `P1Int` by `Iff.rfl` / `rfl`. Checked here against the pushed copy of
research/p1/lean/Hier/P1Hier/Defs.lean.
-/

namespace P1Int

theorem parDecidesFrom_hier (V : C1Challenge.Machine) (L : List Bool → Bool) (g τ : ℕ → ℕ) (n₀ : ℕ) :
    P1Hier.ParDecidesFrom V L g τ n₀ ↔ ParDecidesFrom V L g τ n₀ := Iff.rfl

theorem rootLog_hier : P1Hier.rootLog = rootLog := rfl

theorem G_hier : P1Hier.G = G := rfl

/-- The hier target `P1Hier.parity_hierarchy` (two-constant form), as a Prop, is `ParityHierarchy`. -/
theorem parityHierarchy_hier :
    (∀ q : ℕ, 1 ≤ q → ∃ D : List Bool → Bool,
      (∃ (U : C1Challenge.Machine) (a b : ℕ),
        P1Hier.ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
      ∀ (V : C1Challenge.Machine) (c n₀ : ℕ),
        ¬ P1Hier.ParDecidesFrom V D (P1Hier.G q) (fun n => c * P1Hier.G q n) n₀) ↔
    ParityHierarchy := Iff.rfl

end P1Int
