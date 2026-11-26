import P1Dispatch.Spec

namespace P1ProgDir.SolAdapter

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Int

abbrev Input (s : ℝ) (a b n₀ : ℕ) :=
  Σ x : {x : List Bool // n₀ ≤ x.length},
    (Fin (lpM2 s a b x.val.length) → Bool) ×
      {ρ : List Bool // ρ.length = lpK2 a b x.val.length - 4}

noncomputable def raw {s : ℝ} {a b n₀ : ℕ} (p : Input s a b n₀) :
    List Bool × List Bool × List Bool :=
  (p.1.val, List.ofFn p.2.1, p.2.2.val)

noncomputable def budget (s : ℝ) (a b n : ℕ) : ℕ :=
  lpM2 s a b n * (lpP2 a b n + 1)

open Classical in
theorem checkProgram {s : ℝ} {a b n₀ : ℕ}
    (Ck : List Bool → List Bool → ℕ → Prop)
    (h : Task (fun p : Input s a b n₀ => budget s a b p.1.val.length)
      (fun p => send (raw p))
      (fun p => send (decide (Ck (raw p).1 (raw p).2.1 (P1Batch.bval (raw p).2.2))))) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
        ∀ (u : Fin (lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (Ck x (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  obtain ⟨Rc, c, hr⟩ := P1Dispatch.ofTask_tight_proof raw
    (fun p : Input s a b n₀ => budget s a b p.1.val.length)
    (fun x u i => decide (Ck x u i)) h
  refine ⟨Rc, 2 * (c + 1) + 16, fun x hx => ?_⟩
  let B := budget s a b x.length
  have hM : 0 < lpM2 s a b x.length := by
    unfold lpM2
    apply Nat.mul_pos (Nat.pow_pos (by omega))
    have ht : 0 < lpTime a b x.length := by unfold lpTime; omega
    have hp : 0 < 2 ^ lpT2 s a b x.length := Nat.pow_pos (by decide)
    exact (Nat.le_div_iff_mul_le hp).2 (by omega)
  have hB : 1 ≤ B := by
    change 0 < lpM2 s a b x.length * (lpP2 a b x.length + 1)
    exact Nat.mul_pos hM (by omega)
  refine ⟨(c + 1) * (B + 1), Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · have hc : (c + 1) * (B + 1) ≤ (c + 1) * (2 * B) :=
      Nat.mul_le_mul_left _ (by omega)
    have h16 : 16 ≤ 16 * B := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 16 hB
    calc
      4 * 4 + (c + 1) * (B + 1) ≤ 16 * B + (c + 1) * (2 * B) :=
        Nat.add_le_add h16 hc
      _ = lpCost2 (2 * (c + 1) + 16) s a b x.length := by
        unfold lpCost2 B budget
        ring
  · intro u ρ hρ
    have hrun := hr ⟨⟨x, hx⟩, u, ⟨ρ, hρ⟩⟩
    exact P1Dispatch.progAnswers_mono hrun (Nat.mul_le_mul_right _ (by omega))

end P1ProgDir.SolAdapter
