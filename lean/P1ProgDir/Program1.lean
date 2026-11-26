import P1ProgDir.C1
import P1ProgDir.Adapter
import P1ProgDir.Budget

namespace P1ProgDir.SolProgram1

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkDir P1Wit P1Int
open P1ProgDir.SolGeometry P1ProgDir.SolAdapter P1ProgDir.SolBatchCore
open P1ProgDir.SolC1 P1ProgDir.SolBudget

open Classical in
/-- Family 0 in D8: one program for all input lengths and all witnesses. -/
theorem _root_.P1ProgDir.progC1 {K : Type} (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
    (aM r n₀ : ℕ) (D : ℕ → Dims) (tape : ∀ n, K ≃ Fin (D n).r)
    (hI : ∀ n, n₀ ≤ n → (D n).I = bigCount a b aM n)
    (hN : ∀ n, n₀ ≤ n → (D n).N = laneCount a b n)
    (hr : ∀ n, n₀ ≤ n → (D n).r = r)
    (hfit : ∀ n, n₀ ≤ n → 2 * ((D n).I * (D n).N * (D n).r) ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
        ∀ (u : Fin (lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (C1F (D x.length) (tape x.length) (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  apply checkProgram (fun x u i => C1F (D x.length) (tape x.length) u i)
  let X := Input s a b n₀
  let n (p : X) := p.1.val.length
  let ρ (p : X) := p.2.2.val
  have hgeom (p : X) :
      (D (n p)).I * (D (n p)).N * (D (n p)).r = bigCount a b aM (n p) * laneCount a b (n p) * r := by
    have hh : n₀ ≤ n p := p.1.property
    rw [hI _ hh, hN _ hh, hr _ hh]
  have hwitness (p : X) : (raw p).2.1.length = lpM2 s a b (n p) := List.length_ofFn
  obtain ⟨β, hβ, ht⟩ := c1_task_polynomial (raw (s := s) (a := a) (b := b) (n₀ := n₀))
    a b aM r D tape hgeom (fun p => by rw [hwitness]; exact hfit _ p.1.property)
  have hρ (p : X) : (ρ p).length ≤ lpK2 a b (n p) := p.2.2.property ▸ Nat.sub_le _ _
  obtain ⟨C, hC⟩ := raw_poly_cost raw s hs a b hb hwitness hρ hβ
  exact ht.bound C hC

#print axioms P1ProgDir.progC1

end P1ProgDir.SolProgram1
