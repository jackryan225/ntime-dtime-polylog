import P1ProgDir.C4ProgTask
import P1ProgDir.C4ProgBounds
import P1Dispatch.Spec
import P1Dispatch.BudgetBounds

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Int

variable {K : Type} [Fintype K] [DecidableEq K] {a : ℕ}

private theorem progAnswers_mono {R : Prog Ltr} {regs : Reg Ltr} {b : Bool} {c d : ℕ}
    (h : ProgAnswers R P1Dispatch.answer regs b c) (hc : c ≤ d) :
    ProgAnswers R P1Dispatch.answer regs b d := by
  obtain ⟨t, ht, v, hv, hb⟩ := h
  exact ⟨t, ht.trans hc, v, hv, hb⟩

open scoped Classical in
/-- D8 raw-register form, with the preparation of public format data as an
explicit polynomial-time hypothesis. Each budget covers every witness. -/
theorem progC4F_of_format (F : C4Format K) (ha : 4 ≤ 2 ^ a)
    (hFormat : Poly (F.prepare a))
    (hWidths : Dom size (fun q : C4Query => allFieldWidths (F.prepare a q)))
    (M : ℕ → ℕ) (aClock bClock : ℕ) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ (x : List Bool) (u : Fin (M x.length) → Bool) (ρ : List Bool),
      ρ.length = lpK2 aClock bClock x.length - 4 →
      ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
        (decide (F.check ha x.length (List.ofFn u) (P1Batch.bval ρ)))
        (c * (x.length + M x.length + lpK2 aClock bClock x.length + 1)) := by
  obtain ⟨k, C, h⟩ := taskC4_of_format F ha hFormat hWidths
  obtain ⟨Rc, c₀, hRc⟩ := P1Dispatch.ofTask_tight_proof id _
    (fun x u i => decide (F.check ha x.length u i)) h
  obtain ⟨C', hh⟩ := binary_overhead_linear aClock bClock k C
  refine ⟨Rc, c₀ * (C' + 8), fun x u ρ hρ => ?_⟩
  have hρ' : ρ.length ≤ lpK2 aClock bClock x.length := by
    rw [hρ]
    exact Nat.sub_le _ _
  let p : C4Query := (x, List.ofFn u, ρ)
  have hpX : p.1.length = x.length := rfl
  have hpU : p.2.1.length = M x.length := List.length_ofFn
  have hpR : p.2.2.length = ρ.length := rfl
  have hb : C * (size (compactQuery p) + 1) ^ k ≤ C' * (x.length + M x.length + 1) := by
    have hs := Nat.add_le_add_right (compactQuery_size p) 1
    rw [hpX, hpU, hpR] at hs
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs k)).trans (hh _ _ _ hρ')
  apply progAnswers_mono (hRc p)
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hSize : size p = 2 * (x.length + M x.length + ρ.length) + 5 := by
    simp only [size_prod, size_word, hpX, hpU, hpR]
    omega
  let Q := x.length + M x.length + lpK2 aClock bClock x.length + 1
  have hLinear : size p + p.2.1.length + 1 ≤ 8 * Q := by
    rw [hSize, hpU]
    unfold Q
    omega
  have hPoly : C * (size (compactQuery p) + 1) ^ k ≤ C' * Q :=
    hb.trans (Nat.mul_le_mul_left _ (by unfold Q; omega))
  calc
    _ ≤ 8 * Q + C' * Q := by
      rw [Nat.add_right_comm (size p + p.2.1.length)]
      exact Nat.add_le_add hLinear hPoly
    _ = (C' + 8) * Q := by ring

open scoped Classical in
/-- Family 3's D8 checker and a common per-input budget for all bit assignments. -/
theorem progC4F (F : C4Format K) (ha : 4 ≤ 2 ^ a)
    (hFormat : Poly (F.prepare a))
    (hWidths : Dom size (fun q : C4Query => allFieldWidths (F.prepare a q)))
    (s : ℝ) (hs : s ≤ 1) (aClock bClock : ℕ) (hb : 1 ≤ bClock) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, 16 ≤ x.length →
      ∃ bnd : ℕ, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s aClock bClock x.length ∧
        ∀ (u : Fin (lpM2 s aClock bClock x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 aClock bClock x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (F.check ha x.length (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  obtain ⟨Rc, c, hRc⟩ := progC4F_of_format F ha hFormat hWidths (lpM2 s aClock bClock) aClock bClock
  let C := max c 1
  have hC : 1 ≤ C := le_max_right _ _
  refine ⟨Rc, 10 * C + 16, fun x hx => ?_⟩
  let M := lpM2 s aClock bClock x.length
  let k := lpK2 aClock bClock x.length
  let bnd := C * (x.length + M + k + 1)
  have hPos : 1 ≤ bnd := by
    unfold bnd
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
  refine ⟨bnd, hPos, ?_, fun u ρ hρ => ?_⟩
  · have hh := P1Dispatch.cost_le' s hs aClock bClock hb C x.length hx
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by dsimp only [M, k]; omega)) _).trans hh
  · exact progAnswers_mono (hRc x u ρ hρ) (Nat.mul_le_mul_right _ (le_max_left _ _))

end P1ProgDir.SolC4

#print axioms P1ProgDir.SolC4.progC4F
