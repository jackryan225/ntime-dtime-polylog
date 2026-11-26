# The Lean statements, and how faithful they are to the paper

The theorems are stated in four short files in `lean/C1Challenge/`. **These files import only Mathlib.** No definition of
OpenAI's library or of our proof is used in a statement, so a reader can check what is proved by reading these files only.
Each file states its theorem as a TARGET that ends in `sorry`; the proved theorem is a separate declaration, and the build checks
that the two types are the same Lean term (a `run_meta` check in each closed file, repeated in `lean/Release.lean`). The `sorry`
of a target is never used: the axioms of the proved theorems contain no `sorryAx`.

| File | Lines | sha256 | Target | Proved as |
|---|---|---|---|---|
| `Statement.lean` | 128 | `7f00493145c53b33b79ed358c17aebcedf21ae22b557293af8fcf10102890bd4` | `C1Challenge.c1` | `P1Final.c1_closed` |
| `NTime.lean` | 96 | `04c548116c4fb1cc28bab24493cc23ce974af850a6b66512f1201ae13f5bac45` | `C1Challenge.c1_ntime` | `P1Final.c1_ntime_closed` |
| `C1U.lean` | 77 | `a98d5f5b874df9673c9600aca81091a2b317d45cffcce4d71433b31fdb542492` | `C1Challenge.c1u` | `P1Final.c1u_closed` |
| `UTime.lean` | 26 | `7e56d68ae9f369a52749e39891e79c9e7bc72a7ea9834a5676767a9add3ba9f4` | `C1Challenge.c1u_utime` | `P1Final.c1u_utime_closed` |

Each file imports the one above it (`Statement.lean` imports four Mathlib modules). Guard files with small theorems about the
definitions (81 theorems and examples, none with `sorry`, all built by `lake build`): `NonVacuity.lean`, `NTimeGuards.lean`,
`C1UGuards.lean`, `UTimeGuards.lean`. For example: both classes contain a language that depends on its input; every language in deterministic
linear time is in the guessing class; a machine with two accepting computations and one rejecting one behaves as expected.

## 1. The four theorems, as Lean text

```lean
-- Statement.lean: the first sentence of the main theorem
theorem c1 : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    NTIMELinLog L ∧ ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)

-- NTime.lean: both sentences of the main theorem, one σ and one language
theorem c1_ntime : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    NTIMELinLog L ∧ NTIMEIn L (fun n => (n : ℝ)) ∧
      ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)

-- C1U.lean: the stronger form (paper, Section 8, Theorem "Uplus")
theorem c1u : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, coNTIMELinLog L ∧
    ¬ (NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ))

-- UTime.lean: the stronger form with its corollary for unambiguous time, one σ and one language
theorem c1u_utime : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, coNTIMELinLog L ∧
    ¬ (NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) ∧
    ¬ UTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)
```

## 2. The definitions, in words (the files have every definition in full)

- **Machine.** A deterministic multitape Turing machine: a finite set of two-way infinite tapes (Mathlib `Turing.Tape`), a finite
  alphabet with a blank, a finite set of states, a start state, and a partial transition function (no value = halt). One step
  reads the symbols under all heads, writes one symbol on every tape and moves every head left, not at all, or right. The input
  is on one tape with the head on its first letter; the other tapes are blank. The structure is a field-for-field copy of
  OpenAI's `FiniteMultiTapeMachine` (that copy is written out in `Statement.lean`; it is not imported).
- **`HaltsWithin M input b T`**: M halts after at most T steps, and its final state answers b.
- **`NTIMELinLog L`** (the class NTIME[n; floor(2 log n)]): there are a verifier V and a number c such that, for every word x and
  every guess w of length exactly `Nat.log 2 (n^2)` = floor(2 log2 n) (n = |x|), V halts on the input "w, then x" within
  c (length + 1) steps, and x is in L exactly when some such guess makes V answer true. The guess is written as a
  self-delimiting prefix of the input (each guess bit b as the pair true, b; then false; then x), and the time bound counts the
  prefix: it is c (n + 2g + 2) = O(n).
- **`DTIMEIn L f`**: some machine and some real C: on every x it halts within C (f(|x|) + 1) steps with the answer L x.
- **`NTIMEIn L f`**: the same for a nondeterministic machine (the transition function lists the possible transitions; the empty
  list means halt): every computation halts within C (f(|x|) + 1) steps, and x is in L exactly when some computation ends in an
  accepting halted state.
- **`ParTIMEIn L f`** (parity time): the same clock; x is in L exactly when the number of accepting computations is odd.
  Computations are counted as sequences of transitions (Mathlib tapes do not record the absolute head position, so a list of
  configurations could merge two computations).
- **`UTIMEIn L f`** (unambiguous time): the same clock, at most one accepting computation, and x is in L exactly when there is one.
- **`coNTIMELinLog L`**: as `NTIMELinLog`, but x is in L exactly when EVERY guess of the right length is accepted.
- `Real.logb 2 n` is log2 n; Lean gives `Real.logb 2 0 = Real.logb 2 1 = 0`, and `0 ^ σ = 0` for σ > 0, so for n = 0, 1 the
  deterministic clock is C.

## 3. What the statements do not say

- No value of sigma. The proof splits, by excluded middle, on one Lean proposition (`PortTwo`: whether the algebraic closure of
  the field with two elements "has ports" in the sense of OpenAI's library). Each case gives its own sigma and its own language.
  Nobody knows which case holds, so the theorem is not effective.
- Nothing about P versus NP, polynomial time, random-access machines or circuits. The statements are about multitape Turing
  machines and almost-linear time.
- The language L is built inside the proof and is different in the two cases (the complement of matrix transposition if there
  are no ports; a padded language from the parity time hierarchy if there are). It is not claimed to be a natural problem.
- "Not in DTIME" means: for every machine that decides L and every constant C, the bound fails on some input. It is not an
  "almost everywhere" lower bound.

## 4. Fidelity to the paper

The paper's machines have one-way tapes with an end marker and the guess on a second tape; the Lean machines have two-way tapes
and take the guess as a prefix of the input. The two models give the same classes, since each simulates the other in O(n + g)
extra steps (g = guess length). **This equivalence is argued in words, not in Lean.**

Blind reads. Each statement file was given, with the relevant definitions and theorem of the paper copied verbatim and nothing
else, to models of two other families in one call each. They did not see our proof.

| Statement | Reads | Verdict |
|---|---|---|
| `c1` | a Claude lane; blind: GPT-6.2 Astra (OpenAI), Gemini 4 Neon (Google) | the conclusion of `c1` is the conclusion of the paper's main theorem; the Lean theorem is STRONGER because it drops H1 to H12; no difference makes it weaker; no reason for a trivial truth found |
| `c1_ntime` | blind: Gemini 4 Neon, GPT-6.2 Astra | `NTIMEIn` is the paper's NTIME(f); one sigma and one language for both sentences is the paper's conclusion; stronger only by dropping H1 to H12 |
| `c1u` | blind: GPT-6.2 Astra, Gemini 4 Neon | faithful up to the harmless differences listed below; the count of accepting computations over transition sequences is the paper's count |
| `c1u_utime` | not sent to a blind read | `UTIMEIn` is a two-line definition on top of the definitions read for `c1u` |

Harmless differences named by the reads (each checked):
- Guess length at n = 0 and n = 1: Lean gives 0 guess bits, the paper's "log max(n, 2)" gives 2. The classes are the same (three
  words can be hardwired).
- Clocks: Lean uses c (n + 2g + 2) and C (f + 1) where the paper uses c max(n, 1) and C max(f, 1). These give the same classes,
  since n + 1 <= n + 2g + 2 <= 5 (n + 1). Lean allows c = 0 and a real C; harmless. For a negative f the two clocks differ; the
  bounds used here are not negative.
- Lean reads the paper's time bound for nondeterministic machines as "every computation halts within the bound"; for f = n this
  gives the same class.
- Two of the blind reads end with the label "NOT FAITHFUL". Their only reasons are the dropped hypotheses H1 to H12 (which make
  the Lean theorem stronger) and, for `c1` alone, the paper's second sentence (NTIME(n)), which is the separate theorem `c1_ntime`.
- A comment in `Statement.lean` (lines 30-31) describes an early bug of the first draft (a time bound that did not count the guess
  prefix made `c1` false). One read says the comment is incomplete: the false draft also had a different guess length. The comment
  is not changed, because the sha256 of the file is the reference.

Not done: no human has read the statement files. Not every reasonable guard is in Lean; for example, a guard that a broken time
bound in `NTIMEIn` would change the class is not formalized.
