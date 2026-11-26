import C1Challenge.Statement
import Mathlib.Data.Nat.Find

/-!
# P1Int.Interfaces: the shared definitions of the C1 Lean proof (Mathlib + Challenge only)

Owner: P1-lean-integ copy B (board 09:04:57Z split). Source: research/g3/leanplan/PLAN.md section 3, with
the fixes of section 9 and board 1368 (G3-chief): the time bound of `ParDecidesFrom` counts the verifier's
input, and W2 / Lemma P use two constants (guess `a (n² + 1)`, time `b (n² + 1)`).
Every lane that needs these notions imports this file (or copies the text VERBATIM; the final assembly
checks copies by `Iff.rfl`). The Prog-based `LemmaP` is in `P1Int.LemmaP` (copy A).

* `C1Conclusion`: the body of `C1Challenge.c1` (exact text).
* `ParDecidesFrom`, `rootLog`, `G`: the text of research/p1/lean/Hier/P1Hier/Defs.lean (fixed form, 09:02Z).
* `ParityHierarchy`: target W2 of lane hier (`P1Hier.parity_hierarchy`), two-constant form (board 1368).

Fidelity note for wave 2 (G3-chief, PLAN.md section 9, H9-H11 reader research/p1/h911-reader/NOTES.md):
OpenAI's Lean numbers the slots and orders the CD demands of a bundle by a lane-0 mixed-radix key
(type, source base index, tag, out-slot, U, h, subdivision; SlotBundleNumbering.lean:145,
RegularizedMotifs.lean:123), not by EG's xor-relative identifiers. The checks C7 and C10 of P6/P8 must use
the Lean key; P7 keys terms by the wire's source base. Radii and the uniqueness induction are unchanged.
-/

namespace P1Int

open C1Challenge

/-- The statement of `C1Challenge.c1`, as a `Prop` (exact text). -/
def C1Conclusion : Prop := ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
    NTIMELinLog L ∧ ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)

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

/-- **W2** (lane hier, `P1Hier.parity_hierarchy`), two-constant form (board 1368): for every `q ≥ 1` a
language `D` with a parity verifier of `a (n² + 1)` guess bits and time `b (n² + 1)` (plus the input
length), but with no parity verifier of exactly `G q n` guess bits and time `c · G q n` (plus the input
length) from any length `n₀` on. -/
def ParityHierarchy : Prop := ∀ q : ℕ, 1 ≤ q → ∃ D : List Bool → Bool,
    (∃ (U : Machine) (a b : ℕ),
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
    ∀ (V : Machine) (c n₀ : ℕ), ¬ ParDecidesFrom V D (G q) (fun n => c * G q n) n₀

end P1Int
