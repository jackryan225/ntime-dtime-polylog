import P1ChkFinal.FamC13link
import P1Dispatch.BudgetBounds

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Int

namespace P1ProgDir.SolFamConv

open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkFinal P1ChkFinal.FamC13

private theorem log_succ_le_born_length (n : ℕ) : Nat.log 2 (n + 1) ≤ (born n).length := by
  have hvalue := value_lt (born n)
  rw [birthValue] at hvalue
  have hpow : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 :=
    Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  by_contra h
  have hexp : (born n).length + 1 ≤ Nat.log 2 (n + 1) := by omega
  have hstep := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  rw [pow_succ] at hstep
  have hpos : 0 < (2 : ℕ) ^ (born n).length := Nat.pow_pos (by decide)
  omega

private theorem header_poly (c : ℕ) (q : Qry) :
    (Nat.log 2 (q.1.length + 1) + q.2.2.length + 1) ^ c ≤
      (size (SolGeometry.lengthHeader q).1 + 1) ^ c := by
  apply Nat.pow_le_pow_left _ c
  change _ ≤ size (born q.1.length, q.2.2) + 1
  simp only [size_prod, size_word]
  have h := log_succ_le_born_length q.1.length
  omega

/-- Charge the second linear scan to the single `lpP2 + 1` factor in the branch budget. -/
private theorem beta_cost (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b) (c cβ : ℕ)
    (βW : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) → ℕ)
    (hβW : ∀ p, βW p ≤ BetaBound a b cβ p.val) :
    ∃ C : ℕ, ∀ p, budget c p.val + βW p + 1 ≤
      C * (lpM2 s a b p.val.1.length * (lpP2 a b p.val.1.length + 1) + 1) := by
  let q (p : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4)) : Qry := p.val
  let base p := Nat.log 2 ((q p).1.length + 1) + (q p).2.2.length + 1
  let localCost p := 2 * base p ^ max c cβ
  have hlocal : Dom (fun p => size (SolGeometry.lengthHeader (q p)).1) localCost :=
    ⟨max c cβ, 2, fun p => Nat.mul_le_mul_left 2 (header_poly (max c cβ) (q p))⟩
  have hρ (p : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4)) :
      (q p).2.2.length ≤ lpK2 a b (q p).1.length := p.property.2.trans_le (Nat.sub_le _ _)
  obtain ⟨C₀, hC₀⟩ := SolBudget.raw_poly_cost q s hs a b hb (fun p => p.property.1) hρ hlocal
  obtain ⟨Cₘ, _, hCₘ⟩ := SolBudget.witness_dominates_input s hs a b hb
  let L := 4 * (b + 2 * a) + 4
  refine ⟨C₀ + cβ * (Cₘ + 1 + L * Cₘ), fun p => ?_⟩
  let n := (q p).1.length
  let m := lpM2 s a b n
  let k := lpP2 a b n + 1
  let len := n + (q p).2.1.length + (q p).2.2.length
  have hn : n ≤ Cₘ * m := (Nat.le_succ n).trans (hCₘ n)
  have hu : (q p).2.1.length = m := p.property.1
  have hsel : (q p).2.2.length ≤ L * (Cₘ * m) := by
    calc
      _ ≤ lpK2 a b n := hρ p
      _ ≤ L * ((born n).length + 1) := SolBudget.lambda_le a b n
      _ ≤ L * (n + 1) := Nat.mul_le_mul_left L (Nat.add_le_add_right (birthLen n) 1)
      _ ≤ _ := Nat.mul_le_mul_left L (hCₘ n)
  have hlen : len ≤ (Cₘ + 1 + L * Cₘ) * m := by
    calc
      len ≤ Cₘ * m + m + L * (Cₘ * m) := Nat.add_le_add (Nat.add_le_add hn hu.le) hsel
      _ = _ := by ring
  have hscan : cβ * k * len ≤ (cβ * (Cₘ + 1 + L * Cₘ)) * (m * k + 1) := by
    calc
      _ ≤ cβ * k * ((Cₘ + 1 + L * Cₘ) * m) := Nat.mul_le_mul_left _ hlen
      _ = (cβ * (Cₘ + 1 + L * Cₘ)) * (m * k) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hpoly : base p ^ c + base p ^ cβ ≤ localCost p := by
    have hpos : 0 < base p := by unfold base; omega
    have h₁ := Nat.pow_le_pow_right hpos (le_max_left c cβ)
    have h₂ := Nat.pow_le_pow_right hpos (le_max_right c cβ)
    unfold localCost
    omega
  have hbase : len + localCost p + 1 ≤ C₀ * (m * k + 1) := by
    apply le_trans _ (hC₀ p)
    simp only [size_prod, P1Dispatch.size_list]
    unfold len n
    omega
  have hcone := hβW p
  change βW p ≤ cβ * k * len + base p ^ cβ at hcone
  change len + base p ^ c + βW p + 1 ≤ (C₀ + cβ * (Cₘ + 1 + L * Cₘ)) * (m * k + 1)
  calc
    _ ≤ (len + localCost p + 1) + cβ * k * len := by omega
    _ ≤ _ := (Nat.add_le_add hbase hscan).trans_eq (Nat.add_mul ..).symm

end P1ProgDir.SolFamConv

theorem P1ProgDir.famProg_of_task_beta : P1ChkFinal.FamC13.FamProgBetaTarget := by
  intro s hs a b hb ck c cβ βW hβW T
  obtain ⟨C, hC⟩ := P1ProgDir.SolFamConv.beta_cost s hs a b hb c cβ βW hβW
  obtain ⟨Rc, A, hRc⟩ := P1Dispatch.ofTask_tight_proof Subtype.val _ ck T
  refine ⟨Rc, 2 * (A * C) + 16, 0, fun x _ => ?_⟩
  let B := lpM2 s a b x.length * (lpP2 a b x.length + 1)
  refine ⟨(A * C) * (B + 1), ?_, fun u ρ hρ => ?_⟩
  · exact (Nat.le_add_left _ _).trans (P1Dispatch.cost_le_tight' s a b (A * C) x.length)
  · let p : P1ChkFinal.QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) :=
      ⟨(x, List.ofFn u, ρ), List.length_ofFn, hρ⟩
    rw [P1ProgDir.FamDir.bval_count_eq, Nat.mul_assoc]
    exact P1Dispatch.progAnswers_mono (hRc p) (Nat.mul_le_mul_left A (hC p))

example : P1ChkFinal.FamC13.FamProgBetaTarget := P1ProgDir.famProg_of_task_beta

#print axioms P1ProgDir.famProg_of_task_beta
