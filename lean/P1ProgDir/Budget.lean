import P1ProgDir.Geometry
import Mathlib.Analysis.SpecificLimits.Normed

namespace P1ProgDir.SolBudget

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Int P1ProgDir.SolGeometry Filter

theorem scale_length (k : ℕ) (w : Word) : (scale k w).length = k * (w.length + 1) := by
  induction k with
  | zero => simp only [scale, List.length_nil, Nat.zero_mul]
  | succ k hk =>
    simp only [scale, add_length, hk, Nat.succ_mul]
    omega

theorem clock_length (a b : ℕ) (w : Word) :
    (clockWord a b w).length = (b + 2 * a) * (4 * w.length + 3) + w.length + 3 := by
  simp only [clockWord, add_length, scale_length, length_prod, List.length_cons, List.length_nil]
  ring

theorem lambda_length_le (a b : ℕ) (w : Word) :
    lpK2 a b (value w) ≤ (b + 2 * a) * (4 * w.length + 3) + w.length + 3 := by
  rw [← clock_length]
  have h := value_lt (clockWord a b w)
  rw [clockWord_value] at h
  exact (Nat.clog_le_iff_le_pow (by decide)).mpr h.le

theorem lambda_le (a b n : ℕ) :
    lpK2 a b n ≤ (4 * (b + 2 * a) + 4) * ((born n).length + 1) := by
  have h := lambda_length_le a b (born n)
  rw [birthValue] at h
  apply h.trans
  nlinarith

theorem header_dom (a b : ℕ) {X : Type*} (n : X → ℕ) (ρ : X → Word)
    (hρ : ∀ x, (ρ x).length ≤ lpK2 a b (n x)) :
    Dom (fun x => size (born (n x))) (fun x => size (born (n x), ρ x)) := by
  refine ⟨1, 4 * (b + 2 * a) + 7, fun x => ?_⟩
  have h := (hρ x).trans (lambda_le a b (n x))
  simp only [size_prod, size_word, pow_one]
  nlinarith

theorem power_born_length (n : ℕ) : 2 ^ (born n).length ≤ 2 * n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [born0, List.length_nil, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
    · have hp : 0 < n := by omega
      by_cases h1 : n = 1
      · subst n
        rw [birth (by decide : 0 < (1 : ℕ)), List.length_cons, show 1 / 2 = 0 by decide, born0]
        decide
      · rw [birth hp, List.length_cons, pow_succ]
        have hl := ih (n / 2) (Nat.div_lt_self hp (by decide : 1 < 2))
        -- Use the positive-input bound in the recursive branch.
        have hpow : 2 ^ (born (n / 2)).length % 2 = 0 := by
          have hpos : 0 < n / 2 := by omega
          rw [birth hpos, List.length_cons, pow_succ]
          omega
        omega

theorem polynomial_lt_exponential (k : ℕ) :
    ∃ C : ℕ, ∀ l : ℕ, (2 * l + 2) ^ k ≤ C * 2 ^ l := by
  have htend := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) (by norm_num)
  have he : ∀ᶠ l : ℕ in atTop, (2 : ℝ) ^ k * (l : ℝ) ^ k / (2 : ℝ) ^ l < 1 := by
    have hprod := (tendsto_const_nhds (x := (2 : ℝ) ^ k)).mul htend
    simpa only [mul_zero, mul_div_assoc] using
      hprod.eventually (gt_mem_nhds (show (2 : ℝ) ^ k * 0 < 1 by simp))
  obtain ⟨L, hL⟩ := eventually_atTop.mp he
  refine ⟨(2 * (L + 1)) ^ k + 2, fun l => ?_⟩
  by_cases hl : L ≤ l + 1
  · have h := hL (l + 1) hl
    have hp : 0 < (2 : ℝ) ^ (l + 1) := by positivity
    have h' : (2 * (l + 1)) ^ k < (2 : ℕ) ^ (l + 1) := by
      rw [div_lt_iff₀ hp, one_mul, ← mul_pow] at h
      exact_mod_cast h
    rw [pow_succ] at h'
    refine (show (2 * l + 2) ^ k ≤ 2 * 2 ^ l by
      rw [show 2 * l + 2 = 2 * (l + 1) by omega]
      omega).trans ?_
    exact Nat.mul_le_mul_right _ (by omega)
  · apply (Nat.pow_le_pow_left (show 2 * l + 2 ≤ 2 * (L + 1) by omega) k).trans
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)) |>.trans
      (Nat.mul_le_mul_right _ (by omega))

theorem absorb_born {X : Type*} {n : X → ℕ} {β : X → ℕ}
    (h : Dom (fun x => size (born (n x))) β) :
    ∃ C : ℕ, ∀ x, β x ≤ C * (n x + 1) := by
  obtain ⟨k, A, hA⟩ := h
  obtain ⟨C, hC⟩ := polynomial_lt_exponential k
  refine ⟨2 * A * C, fun x => (hA x).trans ?_⟩
  change A * (size (born (n x)) + 1) ^ k ≤ _
  rw [size_word]
  calc
    _ ≤ A * (C * 2 ^ (born (n x)).length) := Nat.mul_le_mul_left _ (hC _)
    _ ≤ A * (C * (2 * n x + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (power_born_length _))
    _ ≤ 2 * A * C * (n x + 1) := by
      calc
        _ ≤ A * (C * (2 * (n x + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ = _ := by ring

theorem time_le_witness_mul (s : ℝ) (a b n : ℕ) :
    lpTime a b n ≤ lpM2 s a b n * 2 ^ lpT2 s a b n := by
  let t := lpTime a b n
  let d := 2 ^ lpT2 s a b n
  have hd : 0 < d := Nat.pow_pos (by decide)
  have hrem := Nat.mod_lt (t + d - 1) hd
  have hsum := Nat.div_add_mod (t + d - 1) d
  have hb : t ≤ ((t + d - 1) / d) * d := by
    rw [Nat.mul_comm] at hsum
    omega
  refine hb.trans ?_
  change _ ≤ ((lpP2 a b n + 1) ^ 6 * ((t + d - 1) / d)) * d
  rw [Nat.mul_assoc]
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))

theorem witness_dominates_input (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ n, n + 1 ≤ C * lpM2 s a b n := by
  let C := 4 * (b + 2 * a) + 4
  refine ⟨2 * C, by unfold C; omega, fun n => ?_⟩
  have htime : n ^ 2 + 1 ≤ lpTime a b n := by
    have h := Nat.mul_le_mul_right (n ^ 2 + 1) hb
    rw [Nat.one_mul] at h
    unfold lpTime
    omega
  have hlam : 0 < lpK2 a b n := by
    apply Nat.clog_pos (by decide : 1 < (2 : ℕ))
    unfold lpTime
    have h := Nat.mul_le_mul_right (n ^ 2 + 1) hb
    rw [Nat.one_mul] at h
    have := Nat.zero_le (n ^ 2)
    omega
  have hT : lpT2 s a b n ≤ lpP2 a b n := by
    unfold lpT2
    have h := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) (lpP2 a b n))
    rw [one_mul] at h
    simpa only [Nat.floor_natCast] using Nat.floor_mono h
  have hq : 2 ^ lpT2 s a b n ≤ lpK2 a b n := by
    refine (Nat.pow_le_pow_right (by decide) hT).trans ?_
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hlam)
  have hC : lpK2 a b n ≤ C * (n + 1) :=
    (lambda_le a b n).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (birthLen n) 1))
  have h2 : (n + 1) * (n + 1) ≤ 2 * (n ^ 2 + 1) := by
    zify
    nlinarith [sq_nonneg ((n : ℤ) - 1)]
  have h3 : 2 * (n ^ 2 + 1) ≤ (2 * C * lpM2 s a b n) * (n + 1) := by
    calc
      _ ≤ 2 * (lpM2 s a b n * 2 ^ lpT2 s a b n) :=
        Nat.mul_le_mul_left 2 (htime.trans (time_le_witness_mul s a b n))
      _ ≤ 2 * (lpM2 s a b n * (C * (n + 1))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (hq.trans hC))
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right (h2.trans h3) (by omega)

/-- Uniform conversion of the raw-input traversal and a polylogarithmic
local computation to the D8 task budget. -/
theorem raw_poly_cost {X : Type*} (q : X → List Bool × List Bool × List Bool)
    (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
    (hU : ∀ x, (q x).2.1.length = lpM2 s a b (q x).1.length)
    (hρ : ∀ x, (q x).2.2.length ≤ lpK2 a b (q x).1.length)
    {β : X → ℕ} (hβ : Dom (fun x => size (lengthHeader (q x)).1) β) :
    ∃ C : ℕ, ∀ x,
      size (q x) + (q x).2.1.length + β x + 1 ≤
        C * (lpM2 s a b (q x).1.length * (lpP2 a b (q x).1.length + 1) + 1) := by
  let n (x : X) := (q x).1.length
  let ρ (x : X) := (q x).2.2
  have hdom : Dom (fun x => size (born (n x))) β := hβ.sub (header_dom a b n ρ hρ)
  obtain ⟨Cβ, hCβ⟩ := absorb_born hdom
  obtain ⟨Cm, _, hm⟩ := witness_dominates_input s hs a b hb
  let L := 4 * (b + 2 * a) + 4
  let A := 2 * L + Cβ + 8
  refine ⟨A * Cm + 3, ?_⟩
  intro x
  let m := lpM2 s a b (n x)
  have hu' : (q x).2.1.length = m := hU x
  have hsize : size (q x) = 2 * (n x + m + (ρ x).length) + 5 := by
    simp only [size_prod, size_word, hu']
    unfold n ρ
    omega
  have hstep : size (q x) + (q x).2.1.length + β x + 1 ≤ A * (n x + 1) + 3 * m := by
    rw [hsize, hu']
    have hlen : (ρ x).length ≤ L * (n x + 1) :=
      (hρ x).trans ((lambda_le a b (n x)).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (birthLen (n x)) 1)))
    have hcost := hCβ x
    change 2 * (n x + m + (ρ x).length) + 5 + m + β x + 1 ≤ _
    dsimp only [A]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    omega
  refine hstep.trans ?_
  change A * (n x + 1) + 3 * m ≤ (A * Cm + 3) * (m * (lpP2 a b (n x) + 1) + 1)
  calc
    _ ≤ A * (Cm * m) + 3 * m := Nat.add_le_add_right (Nat.mul_le_mul_left A (hm (n x))) _
    _ = (A * Cm + 3) * m := by ring
    _ ≤ _ := by
      apply Nat.mul_le_mul_left
      have hh : m ≤ m * (lpP2 a b (n x) + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega

/-- Budget for a full start-directory scan with a linear-time word processor
per row. The square is slack for the per-row transport and fold bookkeeping. -/
theorem directory_scan_bound (s : ℝ) (hs : s ≤ 1) (a b aM : ℕ) (hb : 1 ≤ b) :
    ∃ C : ℕ, ∀ n : ℕ, bigCount a b aM n * (lpK2 a b n + 1)^2 ≤ C * lpM2 s a b n := by
  obtain ⟨C₀, h₀⟩ := polynomial_lt_exponential 10
  refine ⟨8 * (2 * aM + 2 * C₀), fun n => ?_⟩
  let t := lpTime a b n
  let lamN := lpK2 a b n
  let p := lpP2 a b n
  let j := p / 2 + 19 * p / 2
  let d := 2 ^ j
  have ht : 2 ≤ t := by
    have h := Nat.mul_le_mul_right (n ^ 2 + 1) hb
    rw [Nat.one_mul] at h
    unfold t lpTime
    omega
  have hlam : 0 < lamN := Nat.clog_pos (by decide : 1 < (2 : ℕ)) ht
  have hlamPow : 2 ^ p ≤ lamN := Nat.pow_log_le_self 2 hlam.ne'
  have hpowLam : lamN < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have h2t : 2 ^ lamN ≤ 2 * t := by
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (show 1 < t by omega)
    change 2 ^ (lamN - 1) < t at h
    calc
      2 ^ lamN = 2 * 2 ^ (lamN - 1) := by
        rw [← pow_succ', show lamN - 1 + 1 = lamN by omega]
      _ ≤ 2 * t := Nat.mul_le_mul_left _ h.le
  have hlo : (lamN + 1)^3 ≤ 8 * d := by
    calc
      _ ≤ (2 ^ (p + 1)) ^ 3 := Nat.pow_le_pow_left hpowLam _
      _ = 8 * 2 ^ (3 * p) := by
        rw [← pow_mul, show (p + 1) * 3 = 3 + 3 * p by omega, pow_add]
        rfl
      _ ≤ 8 * d := by
        have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
          (show 3 * p * 2 ≤ 19 * p by omega)
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (h.trans (Nat.le_add_left _ _)))
  have hhi : d ≤ 2 * C₀ * t := by
    calc
      _ ≤ 2 ^ (10 * p) := Nat.pow_le_pow_right (by decide) (show j ≤ 10 * p by unfold j; omega)
      _ = (2 ^ p) ^ 10 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ (2 * lamN + 2) ^ 10 := Nat.pow_le_pow_left (by omega) _
      _ ≤ C₀ * 2 ^ lamN := h₀ _
      _ ≤ _ := (Nat.mul_le_mul_left C₀ h2t).trans_eq (by ring)
  have hI : bigCount a b aM n * d ≤ (2 * aM + 2 * C₀) * t := by
    have hdef : bigCount a b aM n = (aM * 2 ^ lamN + d - 1) / d := by
      simp only [bigCount, d, j, p, lamN, pow_add]
    rw [hdef]
    calc
      _ ≤ aM * 2 ^ lamN + d - 1 := Nat.div_mul_le_self _ _
      _ ≤ aM * (2 * t) + 2 * C₀ * t := by
        exact (Nat.sub_le _ _).trans (Nat.add_le_add (Nat.mul_le_mul_left _ h2t) hhi)
      _ = _ := by ring
  have hT : lpT2 s a b n ≤ p := by
    unfold lpT2
    have h := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) (lpP2 a b n))
    rw [one_mul] at h
    simpa only [Nat.floor_natCast] using Nat.floor_mono h
  have hq : 2 ^ lpT2 s a b n ≤ lamN :=
    (Nat.pow_le_pow_right (by decide) hT).trans hlamPow
  have hd : 0 < 2 ^ lpT2 s a b n := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_right _ hd
  calc
    _ ≤ bigCount a b aM n * (lamN + 1)^3 := by
      rw [show (lamN + 1)^3 = (lamN + 1)^2 * (lamN + 1) from pow_succ _ _,
        Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hq.trans (Nat.le_succ _)))
    _ ≤ bigCount a b aM n * (8 * d) := Nat.mul_le_mul_left _ hlo
    _ = 8 * (bigCount a b aM n * d) := by ring
    _ ≤ 8 * ((2 * aM + 2 * C₀) * t) := Nat.mul_le_mul_left _ hI
    _ = (8 * (2 * aM + 2 * C₀)) * t := by ring
    _ ≤ (8 * (2 * aM + 2 * C₀)) * (lpM2 s a b n * 2 ^ lpT2 s a b n) :=
      Nat.mul_le_mul_left _ (time_le_witness_mul s a b n)
    _ = _ := by ring

end P1ProgDir.SolBudget
