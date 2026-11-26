import P1Count.Dispatch
import P1Count.Bookkeeping
import P1Wrap.ProgDet

/-!
# P1Count.Correct: the dispatcher at the budget of Lemma P (lane P1-lean-W2-count)

The two dispatcher clauses of `P1Int.P11.SetupHyp`, for `R = P1Count.R` at any budget `B ≥ 4 d + bnd`
(for P11: `B = lpCost2 c s a b |x|`):
* `R_cost`: on every selector `γ : Fin k → Bool`, `R` returns within `B` steps (DISPATCH COST);
* `R_correct`: `R` answers `true` on every selector within `B` steps iff every stage `j < K` passes, where
  stage `j` = all checks `(c, ρ)` in the group `grp j` (DISPATCH CORRECT, with `S.Stage j u` := the right
  side). The groups may follow any stage order (D5); `hcover`: every check lies in some group.
Determinism of `Prog.Run` (`P1Wrap.run_det`, `P1Wrap.progAnswers_unique`) moves answers between budgets.
-/

namespace P1Count

open OAI.Computability.IntegerMultiplication P1Int

variable {A : Type}

theorem progAnswers_mono {R : Prog A} {answer : Option A → Bool} {regs : Reg A} {v : Bool}
    {B₁ B₂ : ℕ} (h : ProgAnswers R answer regs v B₁) (hB : B₁ ≤ B₂) :
    ProgAnswers R answer regs v B₂ := by
  obtain ⟨n, hn, r, hr, hv⟩ := h
  exact ⟨n, le_trans hn hB, r, hr, hv⟩

/-- A program that returns within `B₁` answers `true` within `B₂ ≥ B₁` iff it does within `B₁`. -/
theorem progAnswers_true_iff_of_total {R : Prog A} {answer : Option A → Bool} {regs : Reg A}
    {B₁ B₂ : ℕ} (htot : ∃ v, ProgAnswers R answer regs v B₁) (hB : B₁ ≤ B₂) :
    ProgAnswers R answer regs true B₂ ↔ ProgAnswers R answer regs true B₁ := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := htot
    have hvt : v = true := P1Wrap.progAnswers_unique hv h
    rw [← hvt]
    exact hv
  · intro h
    exact progAnswers_mono h hB

section Correct

variable (bit : Option A → Bool) (letter : Bool → A) (hbit : ∀ b, bit (some (letter b)) = b)
  (answer : Option A → Bool) (hacc : answer (some (letter true)) = true)
  (d : ℕ) (chk : ℕ → Option (Prog A)) (k : ℕ) (hk : d ≤ k) (bnd : ℕ) (hb : 1 ≤ bnd)
  (x u : List Bool)
  (htot : ∀ c < 2 ^ d, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
    ∃ v, ProgAnswers Rc answer (inputRegs letter x u ρ) v bnd)
  (B : ℕ) (hB : 4 * d + bnd ≤ B)
include hbit hk hb htot hB

/-- **DISPATCH COST.** -/
theorem R_cost (γ : Fin k → Bool) :
    ∃ v, ProgAnswers (R bit letter d chk) answer (inputRegs letter x u (List.ofFn γ)) v B := by
  obtain ⟨v, hv⟩ := R_total bit letter hbit answer d chk x u k hk bnd hb htot (List.ofFn γ)
    (List.length_ofFn)
  exact ⟨v, progAnswers_mono hv hB⟩

include hacc in
/-- **DISPATCH CORRECT.** -/
theorem R_correct (grp : ℕ → ℕ × List Bool → Prop) (K : ℕ) (hcover : ∀ p, ∃ j < K, grp j p) :
    (∀ γ : Fin k → Bool,
        ProgAnswers (R bit letter d chk) answer (inputRegs letter x u (List.ofFn γ)) true B) ↔
      ∀ j < K, ∀ p, grp j p → p.1 < 2 ^ d → p.2.length = k - d → ∀ Rc, chk p.1 = some Rc →
        ProgAnswers Rc answer (inputRegs letter x u p.2) true bnd := by
  have h1 : (∀ γ : Fin k → Bool,
        ProgAnswers (R bit letter d chk) answer (inputRegs letter x u (List.ofFn γ)) true B) ↔
      ∀ γ : Fin k → Bool, ProgAnswers (R bit letter d chk) answer
        (inputRegs letter x u (List.ofFn γ)) true (4 * d + bnd) := by
    refine forall_congr' fun γ => progAnswers_true_iff_of_total ?_ hB
    exact R_total bit letter hbit answer d chk x u k hk bnd hb htot (List.ofFn γ) (List.length_ofFn)
  rw [h1, forall_ofFn_iff (fun γ => ProgAnswers (R bit letter d chk) answer
      (inputRegs letter x u γ) true (4 * d + bnd)),
    R_forall_iff_fam bit letter hbit answer d chk x u k hk bnd hb hacc]
  rw [← forall_iff_groups (fun (p : ℕ × List Bool) (_ : Unit) => p.1 < 2 ^ d → p.2.length = k - d →
      ∀ Rc, chk p.1 = some Rc → ProgAnswers Rc answer (inputRegs letter x u p.2) true bnd)
      grp K hcover ()]
  constructor
  · intro h p hc hρ Rc hR
    exact h p.1 hc Rc hR p.2 hρ
  · intro h c hc Rc hR ρ hρ
    exact h (c, ρ) hc hρ Rc hR

end Correct

end P1Count
