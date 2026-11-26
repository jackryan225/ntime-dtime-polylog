import P1Int.LemmaP

/-!
# Determinism of OpenAI's stack-program runs, and consequences for `ProgAnswers`

`Prog.Run` (OAI/Computability/IntegerMultiplication/TMProgram.lean) is a relation; every constructor is
syntax-directed, so a run is unique: same cost, same final registers (`run_det`). Hence a program that answers
within a budget answers one value only (`progAnswers_unique`), and "not `true`" means "`false`"
(`progAnswers_false_of_not_true`). Used by the inner verifier of W3 (machine lemma A): `∃ γ, ¬ R accepts` is
`∃ γ, R answers false`.
-/

namespace P1Wrap

open OAI.Computability.IntegerMultiplication P1Int

theorem run_det {A : Type} {Γ : Scope A} {p : Prog A} {r : Reg A} {n n' : ℕ} {s s' : Reg A}
    (h : Prog.Run Γ p r n s) (h' : Prog.Run Γ p r n' s') : n = n' ∧ s = s' := by
  induction h generalizing n' s' with
  | pass => cases h'; exact ⟨rfl, rfl⟩
  | push => cases h'; exact ⟨rfl, rfl⟩
  | pop => cases h'; exact ⟨rfl, rfl⟩
  | look _ ih =>
    cases h' with
    | look h2 => obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩
  | join _ _ ih1 ih2 =>
    cases h' with
    | join h1' h2' =>
      obtain ⟨rfl, rfl⟩ := ih1 h1'
      obtain ⟨rfl, rfl⟩ := ih2 h2'
      exact ⟨rfl, rfl⟩
  | tie _ ih =>
    cases h' with
    | tie h2 => obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩
  | again hc _ ih =>
    cases h' with
    | again hc' h2 =>
      rw [hc] at hc'
      cases hc'
      obtain ⟨rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl⟩

theorem progAnswers_unique {A : Type} {R : Prog A} {answer : Option A → Bool} {regs : Reg A}
    {v v' : Bool} {B B' : ℕ} (h : ProgAnswers R answer regs v B) (h' : ProgAnswers R answer regs v' B') :
    v = v' := by
  obtain ⟨n, -, r, hr, hv⟩ := h
  obtain ⟨n', -, r', hr', hv'⟩ := h'
  obtain ⟨-, rfl⟩ := run_det hr hr'
  rw [← hv, ← hv']

theorem progAnswers_false_of_not_true {A : Type} {R : Prog A} {answer : Option A → Bool} {regs : Reg A}
    {B : ℕ} (h : ∃ v, ProgAnswers R answer regs v B) (hn : ¬ ProgAnswers R answer regs true B) :
    ProgAnswers R answer regs false B := by
  obtain ⟨v, hv⟩ := h
  cases v
  · exact hv
  · exact absurd hv hn

theorem not_true_iff_false {A : Type} {R : Prog A} {answer : Option A → Bool} {regs : Reg A}
    {B : ℕ} (h : ∃ v, ProgAnswers R answer regs v B) :
    ¬ ProgAnswers R answer regs true B ↔ ProgAnswers R answer regs false B :=
  ⟨progAnswers_false_of_not_true h, fun hf ht => Bool.false_ne_true (progAnswers_unique hf ht)⟩

end P1Wrap
