import P1Case1.Flip

/-!
# P1, Case 1, task G5 (arithmetic core, Mathlib only)

The arithmetic that turns the TRANS trace bound and the TRANS table bound into the TRANS lower bound
(the analogue of `Reduction.retained_lower_bound` in OpenAI's `MultitapeWeakETH`). With
`s = √(log₂ N)`:
* if `T > N² s` then `κ · scale (2N²) ≤ T` directly;
* if `T ≤ N² s` then the trace loss `A (1 + N + T/N)` is at most `N²/100`, and a network with
  `V · N ≤ A (N + T + N²)` vertices-times-width and `c · N s ≤ V` forces `κ · scale (2N²) ≤ T`.
-/

namespace P1Case1

theorem g5_arith (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ T : ℕ,
      ((T : ℝ) ≤ N * N * Real.sqrt (Real.logb 2 N) →
        -(1/100 : ℝ) * (N * N) ≤ -A * (1 + N + (T : ℝ) / N) ∧
        ∀ V : ℝ, V * N ≤ A * (N + T + N * N) → c * scale N ≤ V → κ * scale (2 * N * N) ≤ T) ∧
      (¬ (T : ℝ) ≤ N * N * Real.sqrt (Real.logb 2 N) → κ * scale (2 * N * N) ≤ T) := by
  set κ : ℝ := min (1/8) (c / (8 * A)) with hκ
  have hκpos : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ1 : κ ≤ 1/8 := min_le_left _ _
  have hκ2 : κ ≤ c / (8 * A) := min_le_right _ _
  refine ⟨κ, hκpos, max 2 (max (⌈300 * A⌉₊ ^ 2) (2 ^ ⌈(4 * A / c) ^ 2⌉₊)), ?_⟩
  intro N hN T
  have hN2 : 2 ≤ N := le_of_max_le_left hN
  have hNA : ⌈300 * A⌉₊ ^ 2 ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hNm : 2 ^ ⌈(4 * A / c) ^ 2⌉₊ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hn2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hL1 : 1 ≤ Real.logb 2 (N : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by norm_num : (0:ℝ) < 2) hn2
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  have hLn : Real.logb 2 (N : ℝ) ≤ (N : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) hnpos, Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self.le
  have hs1 : 1 ≤ Real.sqrt (Real.logb 2 (N : ℝ)) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1
  have hsn : Real.sqrt (Real.logb 2 (N : ℝ)) ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hLn
  have h300 : 300 * A ≤ Real.sqrt (N : ℝ) := by
    have h1 : (300 * A) ^ 2 ≤ (N : ℝ) := by
      have h2 : 300 * A ≤ (⌈300 * A⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈300 * A⌉₊ ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNA
      push_cast at h3
      nlinarith
    calc 300 * A = Real.sqrt ((300 * A) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt h1
  have hsc : 4 * A / c ≤ Real.sqrt (Real.logb 2 (N : ℝ)) := by
    have hm : ((⌈(4 * A / c) ^ 2⌉₊ : ℕ) : ℝ) ≤ Real.logb 2 (N : ℝ) := by
      have h1 : ((2 ^ ⌈(4 * A / c) ^ 2⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNm
      have h2 := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) h1
      rwa [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
        mul_one] at h2
    have h1 : (4 * A / c) ^ 2 ≤ Real.logb 2 (N : ℝ) := (Nat.le_ceil _).trans hm
    calc 4 * A / c = Real.sqrt ((4 * A / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.logb 2 (N : ℝ)) := Real.sqrt_le_sqrt h1
  -- abbreviations
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (N : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (Real.logb 2 (N : ℝ)) := ⟨_, rfl⟩
  rw [← hs] at hs1 hsn hsc
  rw [← hn] at hn2 hnpos hsn h300
  have hs0 : 0 ≤ s := by linarith
  have hAs : 300 * A * s ≤ n := by
    have h1 : 300 * A * s ≤ Real.sqrt n * Real.sqrt n :=
      mul_le_mul h300 hsn hs0 (Real.sqrt_nonneg _)
    rwa [Real.mul_self_sqrt hnpos.le] at h1
  have hscale2 : scale (2 * N * N) ≤ 4 * (n * n) * s := by
    unfold scale
    have hcast : ((2 * N * N : ℕ) : ℝ) = 2 * (n * n) := by rw [hn]; push_cast; ring
    rw [hcast]
    have hlog : Real.logb 2 (2 * (n * n)) = 1 + 2 * Real.logb 2 n := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul hnpos.ne' hnpos.ne',
        Real.logb_self_eq_one (by norm_num)]
      ring
    rw [hlog]
    have hL1' : 1 ≤ Real.logb 2 n := by rw [hn]; exact hL1
    have h1 : Real.sqrt (1 + 2 * Real.logb 2 n) ≤ 2 * s := by
      have h2 : 1 + 2 * Real.logb 2 n ≤ 4 * Real.logb 2 n := by linarith
      calc Real.sqrt (1 + 2 * Real.logb 2 n) ≤ Real.sqrt (4 * Real.logb 2 n) := Real.sqrt_le_sqrt h2
        _ = 2 * s := by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)], hs, hn]
    have h3 : 0 ≤ 2 * (n * n) := by positivity
    calc 2 * (n * n) * Real.sqrt (1 + 2 * Real.logb 2 n) ≤ 2 * (n * n) * (2 * s) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = 4 * (n * n) * s := by ring
  have hscale2nn : 0 ≤ scale (2 * N * N) := by unfold scale; positivity
  have hscaleN : scale N = n * s := by rw [hn, hs]; rfl
  rw [← hs, ← hn]
  constructor
  · intro hT
    constructor
    · have hTn : (T : ℝ) / n ≤ n * s := by
        rw [div_le_iff₀ hnpos]; nlinarith
      have hns : 1 ≤ n * s := by nlinarith
      have hns2 : n ≤ n * s := by nlinarith
      have h1 : 1 + n + (T : ℝ) / n ≤ 3 * (n * s) := by linarith
      have h2 : A * (1 + n + (T : ℝ) / n) ≤ A * (3 * (n * s)) :=
        mul_le_mul_of_nonneg_left h1 hA.le
      have h3 : A * (3 * (n * s)) ≤ n * n / 100 := by nlinarith
      linarith
    · intro V hV hcV
      rw [hscaleN] at hcV
      have h1 : c * (n * s) * n ≤ A * (n + T + n * n) := by
        have := mul_le_mul_of_nonneg_right hcV hnpos.le
        linarith
      have h2 : n ≤ n * n := by nlinarith
      have hcs : 4 * A ≤ c * s := by
        rw [div_le_iff₀ hc] at hsc; linarith
      have h3 : c * (n * n) * s / 2 ≤ A * T := by nlinarith
      have h4 : κ * scale (2 * N * N) ≤ c / (8 * A) * (4 * (n * n) * s) := by
        calc κ * scale (2 * N * N) ≤ c / (8 * A) * scale (2 * N * N) :=
              mul_le_mul_of_nonneg_right hκ2 hscale2nn
          _ ≤ c / (8 * A) * (4 * (n * n) * s) :=
              mul_le_mul_of_nonneg_left hscale2 (by positivity)
      have h5 : c / (8 * A) * (4 * (n * n) * s) = c * (n * n) * s / 2 / A := by
        field_simp; ring
      rw [h5] at h4
      have h6 : c * (n * n) * s / 2 / A ≤ T := by
        rw [div_le_iff₀ hA]; linarith
      linarith
  · intro hT'
    have hT : n * n * s < (T : ℝ) := not_le.mp hT'
    have hnn : 0 ≤ n * n * s := by positivity
    calc κ * scale (2 * N * N) ≤ 1/8 * scale (2 * N * N) :=
          mul_le_mul_of_nonneg_right hκ1 hscale2nn
      _ ≤ 1/8 * (4 * (n * n) * s) := mul_le_mul_of_nonneg_left hscale2 (by norm_num)
      _ ≤ n * n * s := by nlinarith
      _ ≤ T := hT.le

end P1Case1
