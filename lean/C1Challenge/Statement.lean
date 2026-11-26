import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# Challenge statement for C1 (canonical copy, research/p1/lean/Challenge; fixed 2026-11-25 09:10Z)

Mathlib only. No definition of OpenAI or of ours is imported. The machine model is OpenAI's
`OAI.DepthThreeLowerBound.FiniteMultiTapeMachine` (file `OAI/Computability/DepthThree/Model.lean`, which
itself imports only Mathlib), copied field for field, so that the bridge to OpenAI's model is a structure
copy (task W0 of `research/g3/leanplan/PLAN.md`).

Machine model. A deterministic multitape Turing machine has a finite set `K` of two-way infinite tapes
(Mathlib `Turing.Tape`), a finite alphabet `Γ` whose blank is `default`, and a finite state set `Q`. In one
step it reads the symbols under all heads, and the partial transition function `code` either halts (`none`)
or gives the next state, one symbol to write on each tape and one move (left, stay, right) for each head.
At the start the input word is on tape `inputTape`, written with `symbol`, with the head on its first
letter; every other tape is blank. `HaltsWithin M input b T`: the machine halts after some `t ≤ T` steps
and `accept` of its final state is `b`.

Resource bounds, written out (FIXED 2026-11-25 09:10Z; see FIDELITY.md and the bug record below).
* `guessLen n = Nat.log 2 (n^2) = ⌊2 log₂ n⌋`: the guess budget of the paper's `NTIME[n; ⌊2 log n⌋]`
  (research/papers/ntime-dtime-polylog.tex, Definition def:classes).
* `NTIMELinLog L`: there are a verifier `V` and a number `c` such that, for every word `x` and every guess
  `w` of length exactly `guessLen |x|`, `V` halts on `withGuess w x` within `c * (|withGuess w x| + 1)`
  steps; and `L x = true` iff some such guess makes `V` halt within that bound with answer `true`.
  `withGuess w x` writes each guess bit `b` as the pair `true, b`, then `false`, then `x` (a self-delimiting
  prefix of length `2 g + 1`). The time bound COUNTS THE PREFIX: it is `c (n + 2g + 2) = O(n)`.
  (Bug record: the draft bound `c * (n + 1)` did not count the prefix; then the `n = 0` clause forces `V`
  to halt within `c` steps while reading only the prefix, so every such `L` is constant and `c1` is false.
  Found by agent P1-lean-case1b; proof in research/p1/lean/Case1/P1Case1/CoTransRefute.lean.)
* `DTIMEIn L f`: there are a machine `M` and a real `C` such that on every word `x` the machine halts
  within `C * (f |x| + 1)` steps with answer `L x`. (No prefix; the head starts on the first letter of `x`.
  Not vacuous: see NonVacuity.lean.)

C1: there is `σ > 0` and a language `L` with `L ∈ NTIME[O(n); ⌊2 log₂ n⌋ guess bits]` and
`L ∉ DTIME(O(n (log₂ n)^σ))`. The `σ` is not effective (it depends on constants that exist by a
case distinction on ports in characteristic two).
-/

namespace C1Challenge

/-- Head moves (as in OpenAI's `HeadMove`). -/
inductive HeadMove
  | left
  | stay
  | right

def HeadMove.apply {Γ : Type} [Inhabited Γ] : HeadMove → Turing.Tape Γ → Turing.Tape Γ
  | .left, t => t.move Turing.Dir.left
  | .stay, t => t
  | .right, t => t.move Turing.Dir.right

/-- A configuration: control state and the contents of every tape (with its head). -/
structure Cfg (K Γ Q : Type) [Inhabited Γ] where
  q : Q
  tapes : K → Turing.Tape Γ

/-- Deterministic multitape Turing machine (field for field OpenAI's `FiniteMultiTapeMachine`). -/
structure Machine where
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
  /-- `none`: halt. Otherwise: next state, symbol written on each tape, move of each head. -/
  code : Q → (K → Γ) → Option (Q × (K → Γ) × (K → HeadMove))
  accept : Q → Bool

attribute [instance] Machine.tapeFinite Machine.tapeDecidableEq Machine.alphabetInhabited
  Machine.alphabetFinite Machine.stateFinite

namespace Machine

/-- One step: write on every tape, then move every head. -/
def step (M : Machine) (c : Cfg M.K M.Γ M.Q) : Option (Cfg M.K M.Γ M.Q) :=
  (M.code c.q (fun k => (c.tapes k).head)).map fun out =>
    ⟨out.1, fun k => (out.2.2 k).apply ((c.tapes k).write (out.2.1 k))⟩

/-- Input on the input tape, head on its first letter; all other tapes blank. -/
def init (M : Machine) (input : List Bool) : Cfg M.K M.Γ M.Q :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol) else Turing.Tape.mk₁ []⟩

end Machine

/-- `M` halts on `input` after at most `T` steps, and the final state answers `b`. -/
def HaltsWithin (M : Machine) (input : List Bool) (b : Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, ∃ c : Cfg M.K M.Γ M.Q,
    (fun oc => Option.bind oc M.step)^[t] (some (M.init input)) = some c ∧
    M.step c = none ∧ M.accept c.q = b

/-- The verifier's input: each guess bit `b` as `true, b`, then `false`, then `x`. -/
def withGuess (w x : List Bool) : List Bool :=
  (w.flatMap fun b => [true, b]) ++ false :: x

/-- The paper's guess budget `⌊2 log₂ n⌋`. -/
def guessLen (n : ℕ) : ℕ := Nat.log 2 (n ^ 2)

/-- `L ∈ NTIME[O(n); ⌊2 log₂ n⌋ guess bits]` on multitape machines; the time bound counts the guess prefix. -/
def NTIMELinLog (L : List Bool → Bool) : Prop :=
  ∃ (V : Machine) (c : ℕ), ∀ x : List Bool,
    (∀ w : List Bool, w.length = guessLen x.length →
      ∃ b, HaltsWithin V (withGuess w x) b (c * ((withGuess w x).length + 1))) ∧
    (L x = true ↔ ∃ w : List Bool, w.length = guessLen x.length ∧
      HaltsWithin V (withGuess w x) true (c * ((withGuess w x).length + 1)))

/-- `L ∈ DTIME(C (f n + 1))` for some real `C`, on multitape machines. -/
def DTIMEIn (L : List Bool → Bool) (f : ℕ → ℝ) : Prop :=
  ∃ (M : Machine) (C : ℝ), ∀ x : List Bool,
    ∃ T : ℕ, (T : ℝ) ≤ C * (f x.length + 1) ∧ HaltsWithin M x (L x) T

/-- **C1.** Some language with linear nondeterministic time and logarithmically many guess bits
is not in deterministic time `O(n (log₂ n)^σ)`, for some `σ > 0`. -/
theorem c1 : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    NTIMELinLog L ∧ ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  sorry

end C1Challenge
