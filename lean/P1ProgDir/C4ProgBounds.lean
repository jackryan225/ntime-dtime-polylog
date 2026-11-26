import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

namespace P1ProgDir.SolC4

open Filter

def verifierClock (a b n : ℕ) : ℕ :=
  b * (n ^ 2 + 1) + 2 * (a * (n ^ 2 + 1)) + n + 1

def selectorLength (a b n : ℕ) : ℕ := Nat.clog 2 (verifierClock a b n)

/-- The selector length is bounded by a fixed multiple of the binary input length. -/
theorem selector_le_log (a b n : ℕ) :
    selectorLength a b n ≤ (b + 2 * a + 2) + 2 * (Nat.log 2 (n + 1) + 1) := by
  let C := b + 2 * a + 2
  let p := Nat.log 2 (n + 1) + 1
  have hC : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have hp : n + 1 ≤ 2 ^ p := (Nat.lt_pow_succ_log_self (by decide) _).le
  have htime : verifierClock a b n ≤ C * (n + 1) ^ 2 := by
    have hi : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
    have hn : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    have hh := Nat.mul_le_mul_left (b + 2 * a) hi
    unfold C verifierClock
    nlinarith only [hh, hn]
  apply Nat.clog_le_of_le_pow
  calc
    verifierClock a b n ≤ C * (n + 1) ^ 2 := htime
    _ ≤ 2 ^ C * (2 ^ p) ^ 2 := Nat.mul_le_mul hC (Nat.pow_le_pow_left hp 2)
    _ = 2 ^ (C + 2 * p) := by rw [← pow_mul, ← pow_add, Nat.mul_comm p 2]

private theorem exp_eventually_linearizes (c k : ℕ) : ∀ᶠ r : ℕ in atTop, c * r ^ k ≤ 2 ^ r := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) one_lt_two
  have hc : (0 : ℝ) < 1 / ((c : ℝ) + 1) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
  have h : (c : ℝ) * n ^ k < (2 : ℝ) ^ n := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have ht : (n : ℝ) ^ k < (1 / ((c : ℝ) + 1)) * (2 : ℝ) ^ n :=
      (div_lt_iff₀ hpos).mp hn
    rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ (by positivity), mul_comm] at ht
    nlinarith only [ht, show (0 : ℝ) ≤ (n : ℝ) ^ k by positivity]
  exact (show c * n ^ k < 2 ^ n by exact_mod_cast h).le

/-- Any fixed-degree arithmetic cost in the binary word lengths can be paid
for by a linear term in the two input lists. -/
theorem binary_overhead_linear (a b k c : ℕ) :
    ∃ C : ℕ, ∀ n m sel : ℕ, sel ≤ selectorLength a b n →
      c * (2 * (Nat.log 2 (n + 1) + 1 + (Nat.log 2 (m + 1) + 1) + sel) + 6) ^ k ≤
        C * (n + m + 1) := by
  let A := 2 * (b + 2 * a + 2) + 14
  obtain ⟨R, hR⟩ := eventually_atTop.mp (exp_eventually_linearizes (c * A ^ k) k)
  let Q := 1 + c * A ^ k * R ^ k
  have hPoly (r : ℕ) : c * (A * r) ^ k ≤ Q * 2 ^ r := by
    rw [mul_pow, ← Nat.mul_assoc]
    by_cases hr : R ≤ r
    · have hQ : 1 ≤ Q := by unfold Q; omega
      have h := Nat.mul_le_mul_right (2 ^ r) hQ
      rw [Nat.one_mul] at h
      exact (hR r hr).trans h
    · have hb := Nat.mul_le_mul_left (c * A ^ k) (Nat.pow_le_pow_left (show r ≤ R by omega) k)
      exact hb.trans ((show c * A ^ k * R ^ k ≤ Q by unfold Q; omega).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q (Nat.one_le_two_pow : 1 ≤ 2 ^ r)))
  refine ⟨4 * Q, fun n m sel hsel => ?_⟩
  let q := Nat.log 2 (n + 1) + 1
  let t := Nat.log 2 (m + 1) + 1
  let r := max q t
  have hq : q ≤ r := le_max_left ..
  have ht : t ≤ r := le_max_right ..
  have hr : 1 ≤ r := (show 1 ≤ q by unfold q; omega).trans hq
  have hSig : sel ≤ b + 2 * a + 2 + 2 * q := hsel.trans (selector_le_log a b n)
  have hsum : 2 * (q + t + sel) + 6 ≤ A * r := by
    have hmul := Nat.mul_le_mul_left (2 * (b + 2 * a + 2) + 6) hr
    unfold A
    nlinarith only [hq, ht, hSig, hmul]
  have hp : 2 ^ r ≤ 4 * (n + m + 1) := by
    rcases le_total q t with h | h
    · rw [show r = t from max_eq_right h]
      unfold t
      rw [pow_succ]
      have := Nat.pow_log_le_self 2 (show m + 1 ≠ 0 by omega)
      omega
    · rw [show r = q from max_eq_left h]
      unfold q
      rw [pow_succ]
      have := Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega)
      omega
  calc
    c * (2 * (q + t + sel) + 6) ^ k ≤ c * (A * r) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum k)
    _ ≤ Q * 2 ^ r := hPoly r
    _ ≤ 4 * Q * (n + m + 1) := by
      simpa only [Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left Q hp

/-- A fixed polynomial in the binary length of an arbitrary witness costs at
most a constant times its length, including the empty witness. -/
theorem witness_log_linear (k c : ℕ) :
    ∃ D : ℕ, ∀ m : ℕ, c * (Nat.log 2 (m + 1) + 1) ^ k ≤ D * (m + 1) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (exp_eventually_linearizes c k)
  let Q := 1 + c * R ^ k
  have hQ : 1 ≤ Q := by unfold Q; omega
  have h (r : ℕ) : c * r ^ k ≤ Q * 2 ^ r := by
    by_cases hr : R ≤ r
    · have hu := Nat.mul_le_mul_right (2 ^ r) hQ
      rw [Nat.one_mul] at hu
      exact (hR r hr).trans hu
    · have hu := Nat.mul_le_mul_left Q (Nat.one_le_two_pow : 1 ≤ 2 ^ r)
      rw [Nat.mul_one] at hu
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : r ≤ R) k)).trans
        ((show c * R ^ k ≤ Q by unfold Q; omega).trans hu)
  refine ⟨2 * Q, fun m => ?_⟩
  have hp : 2 ^ (Nat.log 2 (m + 1) + 1) ≤ 2 * (m + 1) := by
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  exact (h _).trans (by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using Nat.mul_le_mul_left Q hp)

/-- Only the public input length and selector need to appear in the
polynomial term. The bound holds even when the witness length is arbitrary. -/
theorem arbitrary_binary_overhead (k c : ℕ) :
    ∃ D : ℕ, ∀ n m sel : ℕ,
      c * (2 * (Nat.log 2 (n + 1) + 1 + (Nat.log 2 (m + 1) + 1) + sel) + 6) ^ k ≤
        D * (m + 1 + (Nat.log 2 (n + 1) + sel + 1) ^ k) := by
  obtain ⟨D, hw⟩ := witness_log_linear k (c * 10 ^ k)
  refine ⟨D + c * 10 ^ k, fun n m sel => ?_⟩
  let A := Nat.log 2 (n + 1) + sel + 1
  let B := Nat.log 2 (m + 1) + 1
  let R := max A B
  have hA : A ≤ R := le_max_left ..
  have hB : B ≤ R := le_max_right ..
  have hR : 1 ≤ R := (show 1 ≤ B by unfold B; omega).trans hB
  have hmain : c * (2 * (Nat.log 2 (n + 1) + 1 + (Nat.log 2 (m + 1) + 1) + sel) + 6) ^ k ≤
      (c * 10 ^ k) * R ^ k := by
    have he : 2 * (Nat.log 2 (n + 1) + 1 + (Nat.log 2 (m + 1) + 1) + sel) + 6 ≤ 10 * R := by
      dsimp only [A, B] at hA hB
      omega
    simpa only [mul_pow, Nat.mul_assoc] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left he k)
  change _ ≤ (D + c * 10 ^ k) * (m + 1 + A ^ k)
  apply hmain.trans
  rcases le_total A B with hab | hba
  · rw [show R = B from max_eq_right hab]
    exact (hw m).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  · rw [show R = A from max_eq_left hba]
    exact Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_add_left _ _)

end P1ProgDir.SolC4
