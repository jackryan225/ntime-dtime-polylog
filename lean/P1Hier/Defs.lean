import C1Challenge.Statement

/-!
# P1Hier.Defs: interface definitions of the parity hierarchy (W2)

Copied from `research/g3/leanplan/PLAN.md` section 3 (P1-lean-hier, 2026-11-25). Integration moves them
to the shared interface file. Machine model, `HaltsWithin` and `withGuess`: `research/p1/lean/Challenge/C1Challenge/Statement.lean` (module `C1Challenge.Statement`).

`rootLog q n`: PLAN.md gives it informally as "least r with ⌊log₂ n⌋ + 1 ≤ r^q". For `q = 0` no such `r`
need exist; the definition below uses the exponent `max q 1`, so it is total and equal to the informal
definition for every `q ≥ 1` (the only case used: W2 quantifies over `q ≥ 1`).
-/

namespace P1Hier

open C1Challenge

open Classical in
/-- Guess length exactly `g n`, time bound `τ n` PLUS the length of the verifier's input
`withGuess w x` (fixed form, G3-chief 09:12Z, PLAN.md section 9), parity of the number of
accepting guesses. -/
noncomputable def ParDecidesFrom (V : Machine) (L : List Bool → Bool) (g τ : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∀ x : List Bool, n₀ ≤ x.length →
    (∀ w : Fin (g x.length) → Bool, ∃ b, HaltsWithin V (withGuess (List.ofFn w) x) b
        (τ x.length + (withGuess (List.ofFn w) x).length)) ∧
    (L x = true ↔ Odd (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true
          (τ x.length + (withGuess (List.ofFn w) x).length)).card)

theorem exists_rootLog (q n : ℕ) : ∃ r : ℕ, Nat.log 2 n + 1 ≤ r ^ (max q 1) :=
  ⟨Nat.log 2 n + 1, by
    have h1 : 1 ≤ max q 1 := le_max_right _ _
    calc Nat.log 2 n + 1 = (Nat.log 2 n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (Nat.log 2 n + 1) ^ (max q 1) := Nat.pow_le_pow_right (Nat.succ_pos _) h1⟩

/-- `rootLog q n` = least `r` with `⌊log₂ n⌋ + 1 ≤ r ^ q` (for `q ≥ 1`), i.e.
`⌈(⌊log₂ n⌋ + 1) ^ (1/q)⌉`. -/
def rootLog (q n : ℕ) : ℕ := Nat.find (exists_rootLog q n)

/-- Slow guess length of the hierarchy: `G q n = n² / rootLog q n`. -/
def G (q n : ℕ) : ℕ := n ^ 2 / rootLog q n

theorem rootLog_spec (q n : ℕ) : Nat.log 2 n + 1 ≤ rootLog q n ^ (max q 1) :=
  Nat.find_spec (exists_rootLog q n)

theorem rootLog_pos (q n : ℕ) : 0 < rootLog q n := by
  rcases Nat.eq_zero_or_pos (rootLog q n) with h | h
  · have := rootLog_spec q n
    rw [h, zero_pow (by omega)] at this
    omega
  · exact h

theorem rootLog_le (q n : ℕ) : rootLog q n ≤ Nat.log 2 n + 1 :=
  Nat.find_min' (exists_rootLog q n) (by
    have h1 : 1 ≤ max q 1 := le_max_right _ _
    calc Nat.log 2 n + 1 = (Nat.log 2 n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (Nat.log 2 n + 1) ^ (max q 1) := Nat.pow_le_pow_right (Nat.succ_pos _) h1)

end P1Hier
