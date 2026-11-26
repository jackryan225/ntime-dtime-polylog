import C1Challenge.Statement

/-!
# NTIME(n) on the machine model of `C1Challenge`: the second sentence of the paper's main theorem

NEW file (P1-lean-integ, 2026-11-25). `Statement.lean` is NOT changed; its sha256 stays the reference.

The paper (Section "Machines" and Definition "Classes", item 3): a nondeterministic machine has finitely many transitions
for each state and scanned tuple; a computation on `x` is a finite sequence of configurations, each obtained from the
previous one by one transition, ending in a halting state; it is accepting if this state is accepting; a machine runs in
time `f` if on every input of length `n` every computation halts within `max(f(n),1)` steps; `NTIME(f)`: some NTM runs in
time `O(f)` and `x ∈ A ↔ acc(M,x) ≥ 1`. Main theorem: "There is σ > 0 such that NTIME[n; 2 log n] ⊄ DTIME(n (log n)^σ)
... Consequently NTIME(n) ⊄ DTIME(n (log n)^σ)."

Here:
* `NMachine`: the fields of `Machine` (same tapes, alphabet, states, input convention); only `code` differs: it LISTS the
  possible transitions for a state and the scanned symbols; the empty list means halt.
* `NMachine.Reach M c t c'`: some computation leads from `c` to `c'` in exactly `t` steps.
* `NTIMEIn L f`: one machine and one real `C`; on every input `x` NO computation has `T + 1` steps for some
  `T ≤ C (f |x| + 1)` (so every computation halts within `T` steps: a configuration that has not halted has a next one),
  and `L x = true` iff some computation reaches a halted configuration whose state accepts. The clock `C (f n + 1)` is the
  clock of `DTIMEIn`.
* `c1_ntime`: both sentences of the main theorem with ONE σ and ONE language.
-/

namespace C1Challenge

/-- A nondeterministic multitape machine: the fields of `Machine`, but `code` lists the possible transitions for a state
and the scanned symbols (finitely many); the empty list means halt. -/
structure NMachine where
  K : Type
  [tapeFinite : Fintype K]
  [tapeDecidableEq : DecidableEq K]
  inputTape : K
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Q : Type
  [stateFinite : Fintype Q]
  initialState : Q
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  /-- The possible transitions: next state, symbol written on each tape, move of each head. `[]`: halt. -/
  code : Q → (K → Γ) → List (Q × (K → Γ) × (K → HeadMove))
  accept : Q → Bool

attribute [instance] NMachine.tapeFinite NMachine.tapeDecidableEq NMachine.alphabetInhabited
  NMachine.alphabetFinite NMachine.stateFinite

namespace NMachine

variable (M : NMachine)

/-- The scanned symbols. -/
def scanned (c : Cfg M.K M.Γ M.Q) : M.K → M.Γ := fun k => (c.tapes k).head

/-- One transition: write on every tape, then move every head (as in `Machine.step`). -/
def apply (c : Cfg M.K M.Γ M.Q) (out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)) : Cfg M.K M.Γ M.Q :=
  ⟨out.1, fun k => (out.2.2 k).apply ((c.tapes k).write (out.2.1 k))⟩

/-- `c'` follows from `c` by one of the possible transitions. -/
def Next (c c' : Cfg M.K M.Γ M.Q) : Prop :=
  ∃ out ∈ M.code c.q (M.scanned c), M.apply c out = c'

/-- `M.Reach c t c'`: some computation leads from `c` to `c'` in exactly `t` steps. -/
def Reach : Cfg M.K M.Γ M.Q → ℕ → Cfg M.K M.Γ M.Q → Prop
  | c, 0, c' => c' = c
  | c, t + 1, c' => ∃ c₁, M.Next c c₁ ∧ Reach c₁ t c'

/-- `c` is halted: no transition is possible. -/
def Halted (c : Cfg M.K M.Γ M.Q) : Prop := M.code c.q (M.scanned c) = []

/-- Input on the input tape, head on its first letter; all other tapes blank (as `Machine.init`). -/
def init (input : List Bool) : Cfg M.K M.Γ M.Q :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol) else Turing.Tape.mk₁ []⟩

end NMachine

/-- `L ∈ NTIME(f)` on nondeterministic multitape machines, with the clock `C (f n + 1)`: on every input `x` every
computation halts within `T ≤ C (f |x| + 1)` steps (no computation has `T + 1` steps), and `L x = true` iff some
computation ends in a halted configuration whose state accepts. -/
def NTIMEIn (L : List Bool → Bool) (f : ℕ → ℝ) : Prop :=
  ∃ (M : NMachine) (C : ℝ), ∀ x : List Bool, ∃ T : ℕ, (T : ℝ) ≤ C * (f x.length + 1) ∧
    (∀ c, ¬ M.Reach (M.init x) (T + 1) c) ∧
    (L x = true ↔ ∃ t c, M.Reach (M.init x) t c ∧ M.Halted c ∧ M.accept c.q = true)

/-- **Both sentences of the paper's main theorem, one σ, one language**: `L ∈ NTIME[n; 2 log n]` (the class of `c1`),
`L ∈ NTIME(n)`, and `L ∉ DTIME(n (log n)^σ)`. TARGET; the proof is to come from `P1Final.c1_closed`. -/
theorem c1_ntime : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    NTIMELinLog L ∧ NTIMEIn L (fun n => (n : ℝ)) ∧
      ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  sorry

end C1Challenge
