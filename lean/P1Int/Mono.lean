import P1Int.LemmaP
import C1Challenge.NonVacuity

/-!
# P1Int.Mono: `ParDecidesFrom` is monotone in the clock; Lemma P at any clock (D7)

Owner: P1-lean-integ (second restart, 2026-11-25). D7 (G3-chief, board 11:01Z, 11:09Z) added the hypothesis
`1 ≤ b` to `P1Int.LemmaP`. A parity verifier with clock constant `b` is also one with clock constant `b + 1`
(every guess already halts within the smaller clock, and a machine gives one answer), so Lemma P applies to
EVERY two-constant parity verifier at the constants `(a, b + 1)`. Lane wrap (`P1Wrap.port_wrapper`) uses
`lemmaP_succ`.
-/

namespace P1Int

open C1Challenge

open Classical in
/-- **Clock monotonicity.** A parity verifier with clock `τ` is a parity verifier with any larger clock `τ'`
(same machine, same guess length, same threshold). -/
theorem parDecidesFrom_mono_clock {V : Machine} {L : List Bool → Bool} {g τ τ' : ℕ → ℕ} {n₀ : ℕ}
    (h : ParDecidesFrom V L g τ n₀) (hτ : ∀ n, τ n ≤ τ' n) : ParDecidesFrom V L g τ' n₀ := by
  intro x hx
  obtain ⟨hhalt, hpar⟩ := h x hx
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hhalt w
    exact ⟨b, hb.mono (Nat.add_le_add_right (hτ _) _)⟩
  · rw [hpar]
    have hfilter : (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true
          (τ x.length + (withGuess (List.ofFn w) x).length)) =
        (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
          HaltsWithin V (withGuess (List.ofFn w) x) true
            (τ' x.length + (withGuess (List.ofFn w) x).length)) := by
      apply Finset.filter_congr
      intro w _
      constructor
      · intro hw
        exact hw.mono (Nat.add_le_add_right (hτ _) _)
      · intro hw
        obtain ⟨b, hb⟩ := hhalt w
        have hbt : b = true := halts_unique V hb hw
        rw [hbt] at hb
        exact hb
    rw [hfilter]

/-- The two-constant form: clock constant `b` to `b + 1`. -/
theorem parDecidesFrom_succ_clock {V : Machine} {L : List Bool → Bool} {a b n₀ : ℕ}
    (h : ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀) :
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => (b + 1) * (n ^ 2 + 1)) n₀ :=
  parDecidesFrom_mono_clock h fun _ => Nat.mul_le_mul_right _ (Nat.le_succ b)

open Classical in
/-- **Lemma P for every two-constant parity verifier** (the way W3 uses `LemmaP` after D7): the conclusion of
`LemmaP s` at the constants `(a, b + 1)`, with no condition on `b`. -/
theorem lemmaP_succ {s : ℝ} (h : LemmaP s) (L : List Bool → Bool) (V : Machine) (a b n₀ : ℕ)
    (hV : ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀) :
    ∃ (A : Type) (_ : Fintype A) (R : OAI.Computability.IntegerMultiplication.Prog A) (letter : Bool → A)
      (_ : Function.Injective letter) (answer : Option A → Bool) (c n₁ : ℕ),
      ∀ x : List Bool, n₁ ≤ x.length →
      (∀ u : Fin (lpM2 s a (b + 1) x.length) → Bool, ∀ γ : Fin (lpK2 a (b + 1) x.length) → Bool,
        ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
          (lpCost2 c s a (b + 1) x.length)) ∧
      (L x = true ↔ Odd (Finset.univ.filter fun u : Fin (lpM2 s a (b + 1) x.length) → Bool =>
        ∀ γ : Fin (lpK2 a (b + 1) x.length) → Bool,
          ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true
            (lpCost2 c s a (b + 1) x.length)).card) :=
  h L V a (b + 1) n₀ (Nat.succ_le_succ (Nat.zero_le b)) (parDecidesFrom_succ_clock hV)

end P1Int
