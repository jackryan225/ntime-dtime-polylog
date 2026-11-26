import C1Challenge.NTime

/-!
# C1-U: coNTIME[n; 2 log n] ⊄ NTIME(n (log n)^σ) ∩ ⊕TIME(n (log n)^σ) (statement; P1-lean-integ, 2026-11-25)

NEW file. `Statement.lean` and `NTime.lean` are NOT changed; this file reuses `NMachine`, `Reach`, `Halted`, `NTIMEIn`.

The paper (research/release/time-separation-public/ntime-dtime-polylog.tex), Theorem "Uplus": "Assume H1--H12. There are
σ > 0 (not effective) and a language L ∈ coNTIME[n; 2 log n] such that L ∉ NTIME(n (log n)^σ) ∩ ⊕TIME(n (log n)^σ)."
Definition "Classes": item 2, coNTIME[f; g] "is the same with ∀"; item 4, ⊕TIME(f): "some NTM M runs in time O(f) and
x ∈ A ⇔ acc(M,x) is odd"; Section "Machines": a computation is a finite sequence of configurations, each obtained from the
previous one by one transition, ending in a halting state; acc(M,x) is the number of accepting computations.

Here:
* `NMachine.Run`, `NMachine.after`: a computation is given by its sequence of transitions (see `AccComp`).
* `NMachine.AccComp`, `NMachine.acc`: the accepting computations and their number (`Nat.card`; finite whenever every
  computation halts within a bound, which `ParTIMEIn` requires).
* `ParTIMEIn L f`: ⊕TIME with the clock `C (f n + 1)` of `NTIMEIn` and `DTIMEIn`.
* `coNTIMELinLog L`: `NTIMELinLog` with "for all guesses of length `guessLen |x|`" in place of "for some guess".
* `c1u`: the conclusion of Theorem "Uplus" (without H1-H12).
-/

namespace C1Challenge

namespace NMachine

variable (M : NMachine)

/-- `M.Run c os`: the transitions `os` can be applied one after the other from `c`, each one possible in the
configuration it is applied to. -/
def Run : Cfg M.K M.Γ M.Q → List (M.Q × (M.K → M.Γ) × (M.K → HeadMove)) → Prop
  | _, [] => True
  | c, o :: os => o ∈ M.code c.q (M.scanned c) ∧ Run (M.apply c o) os

/-- The configuration after applying the transitions `os` from `c`. -/
def after : Cfg M.K M.Γ M.Q → List (M.Q × (M.K → M.Γ) × (M.K → HeadMove)) → Cfg M.K M.Γ M.Q
  | c, [] => c
  | c, o :: os => after (M.apply c o) os

/-- The accepting computations on `x`, each given by its sequence of transitions: applicable one after the other from
`M.init x`, ending in a halted configuration whose state accepts. (In the paper's model a configuration records the
absolute head positions, so different transitions give different configurations and a computation is the same as its
sequence of transitions. Mathlib tapes do not record the absolute head position, so a list of configurations could
merge two computations; hence the count is over transition sequences. A transition is an element of the list
`M.code q s`; repeated entries do not count twice.) -/
abbrev AccComp (x : List Bool) : Type :=
  {os : List (M.Q × (M.K → M.Γ) × (M.K → HeadMove)) // M.Run (M.init x) os ∧
    M.Halted (M.after (M.init x) os) ∧ M.accept (M.after (M.init x) os).q = true}

/-- `acc(M, x)`: the number of accepting computations. -/
noncomputable def acc (x : List Bool) : ℕ := Nat.card (M.AccComp x)

end NMachine

/-- `L ∈ ⊕TIME(C (f n + 1))`: on every input `x` every computation halts within `T ≤ C (f |x| + 1)` steps, and
`L x = true` iff the number of accepting computations is odd. -/
def ParTIMEIn (L : List Bool → Bool) (f : ℕ → ℝ) : Prop :=
  ∃ (M : NMachine) (C : ℝ), ∀ x : List Bool, ∃ T : ℕ, (T : ℝ) ≤ C * (f x.length + 1) ∧
    (∀ c, ¬ M.Reach (M.init x) (T + 1) c) ∧ (L x = true ↔ Odd (M.acc x))

/-- `L ∈ coNTIME[n; ⌊2 log₂ n⌋]`: as `NTIMELinLog`, but `L x = true` iff EVERY guess of length `guessLen |x|` is
accepted. -/
def coNTIMELinLog (L : List Bool → Bool) : Prop :=
  ∃ (V : Machine) (c : ℕ), ∀ x : List Bool,
    (∀ w : List Bool, w.length = guessLen x.length →
      ∃ b, HaltsWithin V (withGuess w x) b (c * ((withGuess w x).length + 1))) ∧
    (L x = true ↔ ∀ w : List Bool, w.length = guessLen x.length →
      HaltsWithin V (withGuess w x) true (c * ((withGuess w x).length + 1)))

/-- **C1-U** (paper, Theorem "Uplus", without H1-H12): some σ > 0 and some L ∈ coNTIME[n; 2 log n] with
L ∉ NTIME(n (log n)^σ) ∩ ⊕TIME(n (log n)^σ). TARGET. -/
theorem c1u : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, coNTIMELinLog L ∧
    ¬ (NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) := by
  sorry

end C1Challenge
