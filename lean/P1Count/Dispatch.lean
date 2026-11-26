import P1Int.LemmaP

/-!
# P1Count.Dispatch: the dispatcher program `R` (task P9, target (1), lane P1-lean-W2-count)

Problem P1, Case 2, Lemma P in the verifier form of `P1Int.LemmaP`: the checker is an OpenAI stack
program `Prog A`; registers 0, 1, 2 hold `x`, `u`, `γ` (first bit on top), `answer` reads the top of
register 0 when the program returns.

The dispatcher reads the first `d` bits of the selector `γ` from register 2 (it pops them), takes the
family number `c = bval p` of these bits (LSB first, the P1Batch convention), and runs the check program
`chk c` of that family on the same registers, where register 2 now holds the remaining `k - d` index bits.
A family number without a check (`chk c = none`) accepts: it pushes `letter true` onto register 0.

* `disp_run`, `disp_run_inv`: the run of `disp` is the run of the selected program, plus exactly `4 d` steps.
* `R_answers_iff`: one selector `p ++ ρ` (`p` of length `d`).
* `R_forall_iff_fam` (target (1)): `R` answers `true` for every selector of length `k` iff every check
  `chk c` (`c < 2 ^ d`) answers `true` for every index `ρ` of length `k - d`. Cost: `4 d` plus the cost
  bound of the checks.
* `R_total`: if every check returns within `bnd` steps on every index, `R` returns within `4 d + bnd`.

Plan for the families (PROVISIONAL, d = 4): 0..11 = C1..C12, 12 = C13 (one link per final site),
13 = the two chain ends, 14 = C14, 15 = accept.
-/

namespace P1Count

open OAI.Computability.IntegerMultiplication P1Int

variable {A : Type}

/-- LSB-first value of a bit list (P1Batch convention `bval`). -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bval l

theorem bval_lt : ∀ p : List Bool, bval p < 2 ^ p.length
  | [] => by simp [bval]
  | b :: l => by
    have h := bval_lt l
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [bval, List.length_cons, pow_succ]
    omega

theorem exists_bval : ∀ (d c : ℕ), c < 2 ^ d → ∃ p : List Bool, p.length = d ∧ bval p = c
  | 0, c, h => ⟨[], rfl, by simp at h; simp [bval, h]⟩
  | d + 1, c, h => by
    obtain ⟨p, hp, hv⟩ := exists_bval d (c / 2) (by rw [pow_succ] at h; omega)
    refine ⟨(c % 2 == 1) :: p, by simp [hp], ?_⟩
    simp only [bval, hv]
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · simp [h0]; omega
    · simp [h1]; omega

/-- **The dispatcher.** Reads `d` bits of register 2 (popping each one) and runs `f p`, where `p` is the
list of the bits read (first bit first). `bit` decodes a letter. -/
def disp (bit : Option A → Bool) : ℕ → (List Bool → Prog A) → Prog A
  | 0, f => f []
  | d + 1, f => .look 2 (fun v => .join (.pop 2) (disp bit d (fun p => f (bit v :: p))))

section Run

variable (bit : Option A → Bool) (letter : Bool → A) (hbit : ∀ b, bit (some (letter b)) = b)
include hbit

/-- A run of the selected program gives a run of the dispatcher, `4 d` steps longer. -/
theorem disp_run (Γ : Scope A) : ∀ (d : ℕ) (f : List Bool → Prog A) (p : List Bool)
    (rest : List A) (r : Reg A) (n : ℕ) (r' : Reg A), p.length = d → r 2 = p.map letter ++ rest →
    Prog.Run Γ (f p) (Function.update r 2 rest) n r' → Prog.Run Γ (disp bit d f) r (4 * d + n) r'
  | 0, f, p, rest, r, n, r', hp, hr, h => by
    rw [List.length_eq_zero_iff] at hp
    subst hp
    simp only [List.map_nil, List.nil_append] at hr
    rw [← hr, Function.update_eq_self] at h
    simpa [disp] using h
  | d + 1, f, p, rest, r, n, r', hp, hr, h => by
    obtain ⟨b, p', rfl⟩ : ∃ b p', p = b :: p' := by
      cases p with
      | nil => simp at hp
      | cons b p' => exact ⟨b, p', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hp
    simp only [List.map_cons, List.cons_append] at hr
    have hs : (Function.update r 2 (r 2).tail) 2 = p'.map letter ++ rest := by
      rw [Function.update_self, hr, List.tail_cons]
    have hu : Function.update (Function.update r 2 (r 2).tail) 2 rest = Function.update r 2 rest :=
      Function.update_idem _ _ _
    have ih := disp_run Γ d (fun q => f (b :: q)) p' rest (Function.update r 2 (r 2).tail) n r' hp hs
      (by rw [hu]; exact h)
    have hc : 4 * (d + 1) + n = 1 + (1 + 1 + 1 + (4 * d + n)) := by ring
    rw [hc, disp]
    refine Prog.Run.look ?_
    rw [hr, List.head?_cons, hbit]
    exact Prog.Run.join Prog.Run.pop ih

/-- Every run of the dispatcher is a run of the selected program, `4 d` steps longer. -/
theorem disp_run_inv (Γ : Scope A) : ∀ (d : ℕ) (f : List Bool → Prog A) (p : List Bool)
    (rest : List A) (r : Reg A) (N : ℕ) (r' : Reg A), p.length = d → r 2 = p.map letter ++ rest →
    Prog.Run Γ (disp bit d f) r N r' →
      ∃ n, N = 4 * d + n ∧ Prog.Run Γ (f p) (Function.update r 2 rest) n r'
  | 0, f, p, rest, r, N, r', hp, hr, h => by
    rw [List.length_eq_zero_iff] at hp
    subst hp
    simp only [List.map_nil, List.nil_append] at hr
    refine ⟨N, by ring, ?_⟩
    rw [← hr, Function.update_eq_self]
    simpa [disp] using h
  | d + 1, f, p, rest, r, N, r', hp, hr, h => by
    obtain ⟨b, p', rfl⟩ : ∃ b p', p = b :: p' := by
      cases p with
      | nil => simp at hp
      | cons b p' => exact ⟨b, p', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hp
    simp only [List.map_cons, List.cons_append] at hr
    rw [disp] at h
    cases h with
    | look h1 =>
      simp only [hr, List.head?_cons, hbit] at h1
      cases h1 with
      | join hpop hrest =>
        cases hpop
        have hs : (Function.update r 2 (r 2).tail) 2 = p'.map letter ++ rest := by
          rw [Function.update_self, hr, List.tail_cons]
        obtain ⟨n, hn, hrun⟩ := disp_run_inv Γ d (fun q => f (b :: q)) p' rest _ _ r' hp hs hrest
        refine ⟨n, by omega, ?_⟩
        rw [Function.update_idem] at hrun
        exact hrun

end Run

/-- The accepting program: push `letter true` onto register 0. -/
def acceptProg (letter : Bool → A) : Prog A := .push 0 (letter true)

/-- **`P1Count.R`, the dispatcher program of Lemma P.** `chk c` is the check program of family `c`
(`none`: accept). -/
def R (bit : Option A → Bool) (letter : Bool → A) (d : ℕ) (chk : ℕ → Option (Prog A)) : Prog A :=
  disp bit d (fun p => (chk (bval p)).getD (acceptProg letter))

theorem inputRegs_two (letter : Bool → A) (x u γ : List Bool) :
    inputRegs letter x u γ 2 = γ.map letter := by
  simp [inputRegs]

theorem inputRegs_update (letter : Bool → A) (x u p ρ : List Bool) :
    Function.update (inputRegs letter x u (p ++ ρ)) 2 (ρ.map letter) = inputRegs letter x u ρ := by
  funext i
  by_cases h : i = 2
  · subst h; simp [inputRegs]
  · rw [Function.update_of_ne h]
    simp [inputRegs, h]

theorem acceptProg_answers (letter : Bool → A) (answer : Option A → Bool) (regs : Reg A)
    {bnd : ℕ} (hb : 1 ≤ bnd) :
    ProgAnswers (acceptProg letter) answer regs (answer (some (letter true))) bnd :=
  ⟨1, hb, _, Prog.Run.push, by simp⟩

section Answers

variable (bit : Option A → Bool) (letter : Bool → A) (hbit : ∀ b, bit (some (letter b)) = b)
  (answer : Option A → Bool) (d : ℕ) (chk : ℕ → Option (Prog A)) (x u : List Bool)
include hbit

/-- **One selector.** `R` answers `v` on the selector `p ++ ρ` (`p` of length `d`) within `4 d + bnd` steps
iff the program of family `bval p` answers `v` on the index `ρ` within `bnd` steps. -/
theorem R_answers_iff (p ρ : List Bool) (hp : p.length = d) (v : Bool) (bnd : ℕ) :
    ProgAnswers (R bit letter d chk) answer (inputRegs letter x u (p ++ ρ)) v (4 * d + bnd) ↔
      ProgAnswers ((chk (bval p)).getD (acceptProg letter)) answer (inputRegs letter x u ρ) v bnd := by
  have hr : inputRegs letter x u (p ++ ρ) 2 = p.map letter ++ ρ.map letter := by
    rw [inputRegs_two, List.map_append]
  constructor
  · rintro ⟨N, hN, r', hrun, hans⟩
    obtain ⟨n, rfl, hrun'⟩ := disp_run_inv bit letter hbit [] d
      (fun p => (chk (bval p)).getD (acceptProg letter)) p (ρ.map letter) _ N r' hp hr hrun
    rw [inputRegs_update] at hrun'
    exact ⟨n, by omega, r', hrun', hans⟩
  · rintro ⟨n, hn, r', hrun, hans⟩
    refine ⟨4 * d + n, by omega, r', ?_, hans⟩
    refine disp_run bit letter hbit [] d (fun p => (chk (bval p)).getD (acceptProg letter)) p
      (ρ.map letter) _ n r' hp hr ?_
    rw [inputRegs_update]
    exact hrun

/-- `R` answers `true` on every selector of length `k` iff every family answers `true` on every index of
length `k - d`. -/
theorem R_forall_iff (k : ℕ) (hk : d ≤ k) (bnd : ℕ) :
    (∀ γ : List Bool, γ.length = k →
        ProgAnswers (R bit letter d chk) answer (inputRegs letter x u γ) true (4 * d + bnd)) ↔
      ∀ p : List Bool, p.length = d → ∀ ρ : List Bool, ρ.length = k - d →
        ProgAnswers ((chk (bval p)).getD (acceptProg letter)) answer (inputRegs letter x u ρ) true
          bnd := by
  constructor
  · intro h p hp ρ hρ
    have := h (p ++ ρ) (by rw [List.length_append]; omega)
    exact (R_answers_iff bit letter hbit answer d chk x u p ρ hp true bnd).1 this
  · intro h γ hγ
    have hsplit : γ = γ.take d ++ γ.drop d := (List.take_append_drop d γ).symm
    rw [hsplit]
    refine (R_answers_iff bit letter hbit answer d chk x u _ _ ?_ true bnd).2
      (h _ ?_ _ ?_)
    · rw [List.length_take]; omega
    · rw [List.length_take]; omega
    · rw [List.length_drop]; omega

/-- **P9 (1), the dispatcher, family form.** If the accept letter reads as `true` and `1 ≤ bnd`, then `R`
answers `true` on every selector of length `k` (within `4 d + bnd` steps) iff every check program
`chk c = some Rc` (`c < 2 ^ d`) answers `true` on every index of length `k - d` within `bnd` steps. -/
theorem R_forall_iff_fam (k : ℕ) (hk : d ≤ k) (bnd : ℕ) (hb : 1 ≤ bnd)
    (hacc : answer (some (letter true)) = true) :
    (∀ γ : List Bool, γ.length = k →
        ProgAnswers (R bit letter d chk) answer (inputRegs letter x u γ) true (4 * d + bnd)) ↔
      ∀ c < 2 ^ d, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
        ProgAnswers Rc answer (inputRegs letter x u ρ) true bnd := by
  rw [R_forall_iff bit letter hbit answer d chk x u k hk bnd]
  constructor
  · intro h c hc Rc hR ρ hρ
    obtain ⟨p, hp, rfl⟩ := exists_bval d c hc
    have := h p hp ρ hρ
    rwa [hR, Option.getD_some] at this
  · intro h p hp ρ hρ
    cases hR : chk (bval p) with
    | none =>
      rw [Option.getD_none, ← hacc]
      exact acceptProg_answers letter answer _ hb
    | some Rc =>
      rw [Option.getD_some]
      exact h (bval p) ((bval_lt p).trans_eq (by rw [hp])) Rc hR ρ hρ

/-- **Totality and cost.** If every check program returns within `bnd` steps on every index of length
`k - d`, then `R` returns within `4 d + bnd` steps on every selector of length `k`. -/
theorem R_total (k : ℕ) (hk : d ≤ k) (bnd : ℕ) (hb : 1 ≤ bnd)
    (h : ∀ c < 2 ^ d, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
      ∃ v, ProgAnswers Rc answer (inputRegs letter x u ρ) v bnd)
    (γ : List Bool) (hγ : γ.length = k) :
    ∃ v, ProgAnswers (R bit letter d chk) answer (inputRegs letter x u γ) v (4 * d + bnd) := by
  have hsplit : γ = γ.take d ++ γ.drop d := (List.take_append_drop d γ).symm
  have hp : (γ.take d).length = d := by rw [List.length_take]; omega
  have hρ : (γ.drop d).length = k - d := by rw [List.length_drop]; omega
  rw [hsplit]
  cases hR : chk (bval (γ.take d)) with
  | none =>
    refine ⟨answer (some (letter true)), ?_⟩
    rw [R_answers_iff bit letter hbit answer d chk x u _ _ hp _ bnd, hR, Option.getD_none]
    exact acceptProg_answers letter answer _ hb
  | some Rc =>
    obtain ⟨v, hv⟩ := h _ ((bval_lt _).trans_eq (by rw [hp])) Rc hR _ hρ
    refine ⟨v, ?_⟩
    rw [R_answers_iff bit letter hbit answer d chk x u _ _ hp _ bnd, hR, Option.getD_some]
    exact hv

end Answers

/-- Selectors as functions (the form of `P1Int.LemmaP`) and as lists of length `k`. -/
theorem forall_ofFn_iff {k : ℕ} (Q : List Bool → Prop) :
    (∀ γ : Fin k → Bool, Q (List.ofFn γ)) ↔ ∀ γ : List Bool, γ.length = k → Q γ := by
  constructor
  · intro h γ hγ
    subst hγ
    have := h γ.get
    rwa [List.ofFn_get] at this
  · intro h γ
    exact h _ (List.length_ofFn)

end P1Count
