import P1Wrap.MachineGlue
import P1Wrap.W3Support

/-!
# The inner verifier at the functional level

`innerVerdict` is what the inner verifier computes on the guess `w` and the word `y`: reject exactly when `y` is a
padded `1^n 0 x u 0^{(p+1) m}` with `n ≥ n₁`, `|u| = m`, and `R` accepts `(x, u, γ)` within the Lemma P budget,
where `γ` = the first `k` guess bits.

`inner_spec`: these verdicts describe `Lin` with the guess length `guessLen |y|` of `NTIMELinLog` (uses
`padIn_inj` and `lpK2_le_guessLen`).

`innerProg_of_impl`: `InnerProg` follows from `InnerImpl` (a stack program computes `innerVerdict` in time
`K (|input| + 1)`, for checkers `R` that return within their budget), a pure implementation task.
-/

namespace P1Wrap.W3

open P1Int C1Challenge OAI.Computability.IntegerMultiplication

noncomputable section

open Classical in
/-- What the inner verifier computes. -/
def innerVerdict {A : Type} (j a b : ℕ) (R : Prog A) (letter : Bool → A) (answer : Option A → Bool) (c n₁ : ℕ)
    (w y : List Bool) : Bool :=
  decide (¬ ∃ x u : List Bool, n₁ ≤ x.length ∧ u.length = lpM2 (sOf j) a b x.length ∧ y = padIn j a b x u ∧
    ProgAnswers R answer (inputRegs letter x u (w.take (lpK2 a b x.length))) true (lpCost2 c (sOf j) a b x.length))

theorem inner_spec {A : Type} (j a b : ℕ) (R : Prog A) (letter : Bool → A) (answer : Option A → Bool)
    (c n₁ : ℕ) (y : List Bool) :
    Lin j a b R letter answer c n₁ y = true ↔
      ∃ w : List Bool, w.length = guessLen y.length ∧ innerVerdict j a b R letter answer c n₁ w y = true := by
  classical
  constructor
  · intro hL
    unfold Lin at hL
    rw [decide_eq_true_iff] at hL
    by_cases hy : ∃ x u : List Bool, n₁ ≤ x.length ∧ u.length = lpM2 (sOf j) a b x.length ∧ y = padIn j a b x u
    · obtain ⟨x, u, hx, hu, rfl⟩ := hy
      -- some selector makes R not accept
      have hna : ¬ AllAccept R letter answer j a b c x u := fun hacc => hL ⟨x, u, hx, hu, rfl, hacc⟩
      unfold AllAccept at hna
      push_neg at hna
      obtain ⟨γ, hγ⟩ := hna
      have hk : lpK2 a b x.length ≤ guessLen (padIn j a b x u).length := by
        rw [length_padIn j a b x u hu]; exact lpK2_le_guessLen j a b x.length
      refine ⟨List.ofFn γ ++ List.replicate (guessLen (padIn j a b x u).length - lpK2 a b x.length) false,
        by simp; omega, ?_⟩
      unfold innerVerdict
      rw [decide_eq_true_iff]
      rintro ⟨x', u', -, hu', heq, hans⟩
      obtain ⟨rfl, rfl⟩ := padIn_inj hu hu' heq
      rw [List.take_left' (List.length_ofFn)] at hans
      exact hγ hans
    · refine ⟨List.replicate (guessLen y.length) false, by simp, ?_⟩
      unfold innerVerdict
      rw [decide_eq_true_iff]
      rintro ⟨x, u, hx, hu, heq, -⟩
      exact hy ⟨x, u, hx, hu, heq⟩
  · rintro ⟨w, hw, hv⟩
    unfold Lin
    rw [decide_eq_true_iff]
    rintro ⟨x, u, hx, hu, rfl, hacc⟩
    unfold innerVerdict at hv
    rw [decide_eq_true_iff] at hv
    apply hv
    refine ⟨x, u, hx, hu, rfl, ?_⟩
    have hk : lpK2 a b x.length ≤ w.length := by
      rw [hw, length_padIn j a b x u hu]; exact lpK2_le_guessLen j a b x.length
    have hlen : (w.take (lpK2 a b x.length)).length = lpK2 a b x.length := by simp; omega
    have h1 := hacc (fun i => (w.take (lpK2 a b x.length))[(i : ℕ)]'(by rw [hlen]; exact i.isLt))
    have h2 : List.ofFn (fun i : Fin (lpK2 a b x.length) =>
        (w.take (lpK2 a b x.length))[(i : ℕ)]'(by rw [hlen]; exact i.isLt)) = w.take (lpK2 a b x.length) := by
      apply List.ext_getElem
      · simp [hlen]
      · intro k h1 h2; simp
    rw [h2] at h1
    exact h1

/-- **Machine lemma A, implementation form**: for a checker `R` that returns within its budget on every branch, a
stack program computes `innerVerdict` in time `K (|withGuess w y| + 1)` on every word `y` and guess `w` of length
`guessLen |y|`. -/
def InnerImpl (j a b : ℕ) : Prop :=
  ∀ (A : Type) (_ : Fintype A) (R : Prog A) (letter : Bool → A), Function.Injective letter →
    ∀ (answer : Option A → Bool) (c n₁ : ℕ),
    (∀ x : List Bool, n₁ ≤ x.length → ∀ u : Fin (lpM2 (sOf j) a b x.length) → Bool,
      ∀ γ : Fin (lpK2 a b x.length) → Bool,
      ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
        (lpCost2 c (sOf j) a b x.length)) →
    ∃ (B : Type) (_ : Fintype B) (P : Prog B) (letB : Bool → B) (_ : Function.Injective letB)
      (ans : Option B → Bool) (K : ℕ), ∀ y w : List Bool, w.length = guessLen y.length →
        ∃ n r, Prog.Run [] P (initRegs letB (withGuess w y)) n r ∧
          n ≤ K * ((withGuess w y).length + 1) ∧
          ans (r 0).head? = innerVerdict j a b R letter answer c n₁ w y

theorem innerProg_of_impl {j a b : ℕ} (h : InnerImpl j a b) : InnerProg j a b := by
  intro A hA R letter hlet answer c n₁ hR
  obtain ⟨B, hB, P, letB, hinj, ans, K, hP⟩ := h A hA R letter hlet answer c n₁ hR
  exact ⟨B, hB, P, letB, hinj, ans, fun w y => innerVerdict j a b R letter answer c n₁ w y, K, hP,
    fun y => inner_spec j a b R letter answer c n₁ y⟩

end

end P1Wrap.W3
