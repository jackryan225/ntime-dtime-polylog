import P1P5.Factor0Target
import P1Wrap.Params

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open Filter
open P1Int P1Wrap

theorem lam_lpTime_le (a b n : ℕ) :
    Params.lam (lpTime a b n) ≤ Nat.clog 2 (b + 2 * a + 2) + 2 * (Nat.log 2 (n + 1) + 1) := by
  let C := b + 2 * a + 2
  let L := Nat.log 2 (n + 1) + 1
  have hpoly : lpTime a b n ≤ C * (n + 1) ^ 2 := by
    let q := (n + 1) ^ 2
    have h1 : n ^ 2 + 1 ≤ q := by
      calc
        n ^ 2 + 1 ≤ n ^ 2 + 1 + 2 * n := Nat.le_add_right _ _
        _ = q := by dsimp only [q]; ring
    have h2 : n + 1 ≤ q := by
      simpa only [q, pow_two, Nat.mul_one] using
        Nat.mul_le_mul_left (n + 1) (Nat.succ_pos n)
    have h3 : q ≤ 2 * q := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right q (show 1 ≤ 2 by decide)
    calc
      lpTime a b n = b * (n ^ 2 + 1) + (2 * a) * (n ^ 2 + 1) + (n + 1) := by unfold lpTime; ring
      _ ≤ b * q + (2 * a) * q + 2 * q := Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h1)) (h2.trans h3)
      _ = C * (n + 1) ^ 2 := by dsimp only [q, C]; ring
  have hC : C ≤ 2 ^ Nat.clog 2 C := Nat.le_pow_clog (by decide) C
  have hn : n + 1 ≤ 2 ^ L := (Nat.lt_pow_succ_log_self one_lt_two _).le
  unfold Params.lam
  apply (Nat.clog_le_iff_le_pow one_lt_two).mpr
  calc
    lpTime a b n ≤ C * (n + 1) ^ 2 := hpoly
    _ ≤ 2 ^ Nat.clog 2 C * (2 ^ L) ^ 2 := Nat.mul_le_mul hC (Nat.pow_le_pow_left hn _)
    _ = 2 ^ (Nat.clog 2 C + 2 * L) := by rw [← pow_mul, Nat.mul_comm L 2, ← pow_add]

theorem lam_lpTime_dom (a b : ℕ) :
    Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => Params.lam (lpTime a b n)) := by
  refine ⟨1, Nat.clog 2 (b + 2 * a + 2) + 2, fun n => (lam_lpTime_le a b n).trans ?_⟩
  change Nat.clog 2 (b + 2 * a + 2) + 2 * (Nat.log 2 (n + 1) + 1) ≤
    (Nat.clog 2 (b + 2 * a + 2) + 2) * (Nat.log 2 (n + 1) + 1) ^ 1
  rw [pow_one, Nat.add_mul]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) _

/-- The number of cells per big block is polynomial in the logarithm of the input length. -/
theorem block_dom (a b : ℕ) :
    Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => Params.bb (lpTime a b n)) := by
  apply (((lam_lpTime_dom a b).add (Dom.const _ 1)).pow 10).mono
  intro n
  by_cases ht : 2 ≤ lpTime a b n
  · exact (Params.bb_le_lam_pow ht).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  · have hone : lpTime a b n = 1 := by unfold lpTime at *; omega
    rw [hone]
    decide

/-- Polynomial work in a binary length can be charged to a linear scan of the corresponding list. -/
theorem witness_log_absorb (e : ℕ) :
    ∃ C : ℕ, ∀ u : ℕ, (Nat.log 2 (u + 1) + 1) ^ e ≤ C * (u + 1) := by
  obtain ⟨n, hn⟩ := eventually_atTop.1 (Params.lam_pow_lt_t e)
  refine ⟨max 2 ((Params.lam (2 * (n + 1))) ^ e), fun u => ?_⟩
  have hl : Nat.log 2 (u + 1) + 1 ≤ Params.lam (2 * (u + 1)) := by
    have he : 2 ^ Nat.log 2 (u + 1) ≤ u + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
    have hh : 2 ^ (Nat.log 2 (u + 1) + 1) ≤ 2 * (u + 1) := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left _ he
    have hpow := (Nat.le_pow_clog (b := 2) one_lt_two (2 * (u + 1)))
    by_contra h
    have hlt := Nat.pow_lt_pow_right one_lt_two (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge (hh.trans hpow)) hlt
  refine (Nat.pow_le_pow_left hl _).trans ?_
  by_cases hu : n ≤ 2 * (u + 1)
  · exact (hn _ hu).le.trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · have hmono : Params.lam (2 * (u + 1)) ≤ Params.lam (2 * (n + 1)) := by
      unfold Params.lam
      exact Nat.clog_mono_right 2 (by omega)
    refine (Nat.pow_le_pow_left hmono _).trans ((Nat.le_max_right 2 _).trans ?_)
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- The extra witness-length word in the clipping pass does not change the target budget. -/
theorem absorb_budget {X : Type*} (x u s t : X → ℕ)
    (ht : Dom (fun p => s p + Nat.log 2 (u p + 1)) t) :
    ∃ e C : ℕ, ∀ p, x p + u p + t p + 1 ≤ C * (x p + u p + (s p + 1) ^ e + 1) := by
  obtain ⟨e, A, hA⟩ := ht
  obtain ⟨B, hB⟩ := witness_log_absorb e
  refine ⟨e, 1 + A * 2 ^ e * (B + 1), fun p => ?_⟩
  let S := s p + 1
  let L := Nat.log 2 (u p + 1) + 1
  have hu : L ^ e ≤ B * (u p + 1) := hB (u p)
  have hq : (s p + Nat.log 2 (u p + 1) + 1) ^ e ≤ 2 ^ e * (S ^ e + L ^ e) := by
    by_cases h : L ≤ S
    · have hz : s p + Nat.log 2 (u p + 1) + 1 ≤ 2 * S := by dsimp [S, L] at *; omega
      exact (Nat.pow_le_pow_left hz _).trans (by rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    · have hz : s p + Nat.log 2 (u p + 1) + 1 ≤ 2 * L := by dsimp [S, L] at *; omega
      exact (Nat.pow_le_pow_left hz _).trans (by rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  change x p + u p + t p + 1 ≤ _ * (x p + u p + S ^ e + 1)
  have hmax : S ^ e + L ^ e ≤ (B + 1) * (x p + u p + S ^ e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    have hb := Nat.mul_le_mul_left B (show u p + 1 ≤ x p + u p + S ^ e + 1 by omega)
    omega
  have hout := (hA p).trans ((Nat.mul_le_mul_left A hq).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmax)))
  have hout' : t p ≤ A * 2 ^ e * (B + 1) * (x p + u p + S ^ e + 1) := by
    simpa only [Nat.mul_assoc] using hout
  rw [Nat.add_mul, Nat.one_mul]
  omega

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.absorb_budget
