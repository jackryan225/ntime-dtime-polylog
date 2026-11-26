import P1Dispatch.Defs

namespace P1Dispatch

open P1Int

namespace SolBudget

/-- Monotonicity against the rounded-up quotient used in the witness length. -/
private theorem le_ceiling_div {t d j : ℕ} (hd : 0 < d) (h : j * d ≤ t) :
    j ≤ (t + d - 1) / d :=
  (Nat.le_div_iff_mul_le hd).2 (h.trans (by omega))

private theorem le_witness {s : ℝ} {a b n j : ℕ}
    (h : j * 2 ^ lpT2 s a b n ≤ lpTime a b n) : j ≤ lpM2 s a b n := by
  let d := 2 ^ lpT2 s a b n
  let Q := (lpTime a b n + d - 1) / d
  have hQ : j ≤ Q := le_ceiling_div (by positivity) h
  have hp : 1 ≤ (lpP2 a b n + 1) ^ 6 := Nat.succ_le_iff.mpr (by positivity)
  exact hQ.trans (by simpa only [lpM2, Q, d, one_mul] using Nat.mul_le_mul_right Q hp)

private theorem witness_pos (s : ℝ) (a b n : ℕ) : 1 ≤ lpM2 s a b n := by
  let d := 2 ^ lpT2 s a b n
  have hd : 0 < d := by positivity
  have ht : 1 ≤ lpTime a b n := by unfold lpTime; omega
  have hQ : 1 ≤ (lpTime a b n + d - 1) / d :=
    (Nat.le_div_iff_mul_le hd).2 (by rw [one_mul]; omega)
  have hp : 1 ≤ (lpP2 a b n + 1) ^ 6 := Nat.succ_le_iff.mpr (by positivity)
  simpa only [lpM2, d, one_mul] using Nat.mul_le_mul hp hQ

private theorem exponent_le (s : ℝ) (hs : s ≤ 1) (a b n : ℕ)
    (hk : 0 < lpK2 a b n) : 2 ^ lpT2 s a b n ≤ lpK2 a b n := by
  have hT : lpT2 s a b n ≤ lpP2 a b n := by
    have hreal : s * (lpP2 a b n : ℝ) ≤ (lpP2 a b n : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
        (Nat.cast_nonneg (lpP2 a b n))
    simpa only [lpT2, Nat.floor_natCast] using Nat.floor_mono hreal
  exact (Nat.pow_le_pow_right (by decide) hT).trans
    (Nat.pow_log_le_self 2 hk.ne')

private theorem square_le_pred_power (k : ℕ) (hk : 8 ≤ k) : k ^ 2 ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hmul : 3 * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
    have hnext : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    calc
      (k + 1) ^ 2 ≤ 2 * k ^ 2 := hnext
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ ((k + 1) - 1) := by
        rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ, Nat.mul_comm]

private theorem input_le_witness (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
    (n : ℕ) (hn : 16 ≤ n) :
    n ≤ lpM2 s a b n ∧ lpK2 a b n ≤ lpM2 s a b n := by
  let t := lpTime a b n
  let k := lpK2 a b n
  have hn2 : n ^ 2 ≤ t := by
    have h := Nat.mul_le_mul_right (n ^ 2 + 1) hb
    unfold t lpTime
    simp only [one_mul] at h
    omega
  have ht : 2 ^ 7 < t := by
    have h := Nat.pow_le_pow_left hn 2
    norm_num at h ⊢
    omega
  have hk : 8 ≤ k :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).2 ht
  have hpred : 2 ^ (k - 1) < t :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).1 (by
      change k - 1 < k
      omega)
  have hk2 : k ^ 2 ≤ t := (square_le_pred_power k hk).trans hpred.le
  have hk0 : 0 < k := by omega
  have hd : 2 ^ lpT2 s a b n ≤ k := exponent_le s hs a b n hk0
  refine ⟨le_witness ?_, le_witness ?_⟩
  · calc
      n * 2 ^ lpT2 s a b n ≤ n * k := Nat.mul_le_mul_left _ hd
      _ ≤ t := by
        rcases le_total n k with h | h
        · exact (Nat.mul_le_mul_right k h).trans (by simpa only [pow_two] using hk2)
        · exact (Nat.mul_le_mul_left n h).trans (by simpa only [pow_two] using hn2)
  · exact (Nat.mul_le_mul_left k hd).trans (by simpa only [pow_two] using hk2)

private theorem witness_le_budget (s : ℝ) (a b n : ℕ) :
    lpM2 s a b n ≤ lpM2 s a b n * (lpP2 a b n + 1) := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (lpM2 s a b n)
    (show 1 ≤ lpP2 a b n + 1 by omega)

end SolBudget

open SolBudget

/-- **(2) `P1Dispatch.cost_le`, form of D8.** `n` = `|x|`, `k = lpK2`, `lpM2 (lpP2 + 1)` = the Task budget. -/
theorem cost_le' (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b) (c n : ℕ) (hn : 16 ≤ n) :
    4 * 4 + c * (lpM2 s a b n + n + lpK2 a b n + lpM2 s a b n * (lpP2 a b n + 1) + 1) ≤
      lpCost2 (10 * c + 16) s a b n := by
  obtain ⟨hnM, hkM⟩ := input_le_witness s hs a b hb n hn
  let M := lpM2 s a b n
  let B := M * (lpP2 a b n + 1)
  have hMB : M ≤ B := witness_le_budget s a b n
  have h1 : 1 ≤ B := (witness_pos s a b n).trans hMB
  have hsum : M + n + lpK2 a b n + B + 1 ≤ 10 * B := by
    change n ≤ M at hnM
    change lpK2 a b n ≤ M at hkM
    omega
  rw [lpCost2, Nat.mul_assoc]
  change 16 + c * (M + n + lpK2 a b n + B + 1) ≤ (10 * c + 16) * B
  calc
    _ ≤ 16 * B + c * (10 * B) :=
      Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 16 h1)
        (Nat.mul_le_mul_left c hsum)
    _ = _ := by ring

/-- **(2) tight form**: with `ofTask_tight` the dispatcher costs at most `4 · 4 + c (lpM2 (lpP2 + 1) + 1)`;
this fits for every `s, a, b, n`. -/
theorem cost_le_tight' (s : ℝ) (a b c n : ℕ) :
    4 * 4 + c * (lpM2 s a b n * (lpP2 a b n + 1) + 1) ≤ lpCost2 (2 * c + 16) s a b n := by
  let B := lpM2 s a b n * (lpP2 a b n + 1)
  have h1 : 1 ≤ B := (witness_pos s a b n).trans (witness_le_budget s a b n)
  rw [lpCost2, Nat.mul_assoc]
  change 16 + c * (B + 1) ≤ (2 * c + 16) * B
  calc
    _ ≤ 16 * B + c * (2 * B) :=
      Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 16 h1)
        (Nat.mul_le_mul_left c (by omega))
    _ = _ := by ring

end P1Dispatch

#print axioms P1Dispatch.cost_le'
#print axioms P1Dispatch.cost_le_tight'
