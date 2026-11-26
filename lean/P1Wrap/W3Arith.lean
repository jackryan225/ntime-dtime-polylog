import P1Int.LemmaP
import P1Wrap.Params

/-!
# W3 arithmetic: the guessed transcript fits into the slow guess length `G q n`

Paper: prop:case2 (research/papers/ntime-dtime-polylog.tex l.1120-1150). With `s = 2^-j`, `σ = s/2 = 2^-(j+1)` and
`q = 4/s = 2^(j+2)`, and the padded input length `ν = 2n + 1 + (p+2) m` (input `1^n 0 x u 0^{(p+1) m}`), for every
constant `K` (transcript bits per step) and every real `C` (the DTIME constant):
`m + K (⌊C (ν (log₂ ν)^σ + 1)⌋₊ + 1) + ν + n + 1 ≤ G q n` for all large `n` (`fits`).

Method: every real power is removed by raising to the power `e = q`: `((log ν)^σ)^e ≤ (clog ν)^2`,
`rootLog^e ≤ 2^e (log n + 1)`, `(2^T)^e 2^e > λ^4`; what remains is polylog(λ) ≤ λ and λ^4 ≤ n.
-/

namespace P1Wrap.W3

open P1Int Filter

noncomputable section

/-- `s = 2^-j`. -/
def sOf (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))
/-- `σ = s / 2 = 2^-(j+1)`. -/
def sigmaOf (j : ℕ) : ℝ := (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ))
/-- `q = 4 / s = 2^(j+2)`. -/
def qOf (j : ℕ) : ℕ := 2 ^ (j + 2)

/-- padding length `(p+1) m` (paper: `R(n) = (p+1) m(n)`). -/
def padLen (j a b n : ℕ) : ℕ := (lpP2 a b n + 1) * lpM2 (sOf j) a b n
/-- length of the padded input `1^n 0 x u 0^{padLen}` for `|x| = n`, `|u| = m`. -/
def nuOf (j a b n : ℕ) : ℕ := 2 * n + 1 + lpM2 (sOf j) a b n + padLen j a b n

theorem sigmaOf_pos (j : ℕ) : 0 < sigmaOf j := by unfold sigmaOf; positivity

theorem sOf_pos (j : ℕ) : 0 < sOf j := by unfold sOf; positivity

theorem one_le_qOf (j : ℕ) : 1 ≤ qOf j := Nat.one_le_two_pow

theorem sigma_mul_q (j : ℕ) : sigmaOf j * (qOf j : ℝ) = 2 := by
  unfold sigmaOf qOf
  rw [zpow_neg, zpow_natCast]
  push_cast
  have h : (2 : ℝ) ^ (j + 2) = 2 ^ (j + 1) * 2 := by ring
  rw [h, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem sigmaOf_eq (j : ℕ) : sigmaOf j = sOf j / 2 := by
  unfold sigmaOf sOf
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
  field_simp

theorem lpT2_sOf (j a b n : ℕ) : lpT2 (sOf j) a b n = lpP2 a b n / 2 ^ j := by
  unfold lpT2 sOf
  have : ((2 : ℝ) ^ (-(j : ℤ))) * (lpP2 a b n : ℝ) = ((lpP2 a b n : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
    rw [zpow_neg, zpow_natCast]; push_cast; ring
  rw [this, Nat.floor_div_eq_div]

/-! ## Elementary facts -/

theorem lt_lpTime (a b n : ℕ) : n < lpTime a b n := by
  unfold lpTime
  omega

theorem lpTime_le (a b n : ℕ) (hn : 1 ≤ n) : lpTime a b n ≤ 2 * (2 * a + b + 1) * n ^ 2 := by
  unfold lpTime
  have h1 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : b ≤ b * n ^ 2 := Nat.le_mul_of_pos_right _ h2
  have h4 : a ≤ a * n ^ 2 := Nat.le_mul_of_pos_right _ h2
  have e1 : b * (n ^ 2 + 1) + 2 * (a * (n ^ 2 + 1)) + n + 1 =
      b * n ^ 2 + b + 2 * (a * n ^ 2) + 2 * a + n + 1 := by ring
  have e2 : 2 * (2 * a + b + 1) * n ^ 2 = 4 * (a * n ^ 2) + 2 * (b * n ^ 2) + 2 * n ^ 2 := by ring
  rw [e1, e2]
  omega

theorem tendsto_lpTime (a b : ℕ) : Tendsto (lpTime a b) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro c
  exact ⟨c, fun n hn => le_trans hn (lt_lpTime a b n).le⟩

theorem eventually_lpTime {a b : ℕ} {P : ℕ → Prop} (hP : ∀ᶠ t in atTop, P t) :
    ∀ᶠ n in atTop, P (lpTime a b n) := (tendsto_lpTime a b).eventually hP

/-- `rootLog q n ^ q ≤ 2^q (⌊log₂ n⌋ + 1)` (minimality of `rootLog`). -/
theorem rootLog_pow_le (q n : ℕ) (hq : 1 ≤ q) : rootLog q n ^ q ≤ 2 ^ q * (Nat.log 2 n + 1) := by
  have hmax : max q 1 = q := max_eq_left hq
  set r := rootLog q n with hr
  rcases Nat.lt_or_ge r 2 with h | h
  · have : r ^ q ≤ 1 ^ q := Nat.pow_le_pow_left (by omega) q
    rw [one_pow] at this
    have : 1 ≤ 2 ^ q * (Nat.log 2 n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  · have hmin : ¬ (Nat.log 2 n + 1 ≤ (r - 1) ^ (max q 1)) :=
      Nat.find_min (exists_rootLog q n) (show r - 1 < Nat.find (exists_rootLog q n) by
        rw [← rootLog]; omega)
    rw [hmax] at hmin
    have h2 : r ≤ 2 * (r - 1) := by omega
    calc r ^ q ≤ (2 * (r - 1)) ^ q := Nat.pow_le_pow_left h2 q
      _ = 2 ^ q * (r - 1) ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (Nat.log 2 n + 1) := Nat.mul_le_mul_left _ (by omega)

theorem rootLog_pos' (q n : ℕ) (hq : 1 ≤ q) : 0 < rootLog q n := by
  have h : Nat.log 2 n + 1 ≤ rootLog q n ^ (max q 1) := Nat.find_spec (exists_rootLog q n)
  rw [max_eq_left hq] at h
  rcases Nat.eq_zero_or_pos (rootLog q n) with h0 | h0
  · rw [h0, zero_pow (by omega)] at h; omega
  · exact h0

/-- `⌊log₂ n⌋ + 1 ≤ λ`. -/
theorem log_succ_le_lam (a b n : ℕ) (hn : 1 ≤ n) : Nat.log 2 n + 1 ≤ lpLam2 a b n := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 := lt_lpTime a b n
  have h3 : lpTime a b n ≤ 2 ^ lpLam2 a b n := Nat.le_pow_clog one_lt_two _
  by_contra hc
  have h4 : 2 ^ lpLam2 a b n ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `c (p+2)^k ≤ 2^p` for large `p`. -/
theorem eventually_poly_le (c k : ℕ) : ∀ᶠ q : ℕ in atTop, c * (q + 2) ^ k ≤ 2 ^ q := by
  filter_upwards [Params.eventually_mul_pow_lt_two_pow (c * 2 ^ k) k, eventually_ge_atTop 2]
    with q h1 h2
  have h3 : (q + 2) ^ k ≤ (2 * q) ^ k := Nat.pow_le_pow_left (by omega) k
  calc c * (q + 2) ^ k ≤ c * (2 * q) ^ k := Nat.mul_le_mul_left _ h3
    _ = c * 2 ^ k * q ^ k := by rw [mul_pow]; ring
    _ ≤ 2 ^ q := h1.le

/-- The e-th power trick: `A^e Λ^2 ≤ B^e` gives `A Λ^σ ≤ B` when `σ e = 2`. -/
theorem rpow_trick {A B Λ e : ℕ} {σ : ℝ} (hσe : σ * (e : ℝ) = 2) (he : e ≠ 0)
    (h : A ^ e * Λ ^ 2 ≤ B ^ e) : (A : ℝ) * (Λ : ℝ) ^ σ ≤ B := by
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Nat.cast_nonneg _
  have hX : (0 : ℝ) ≤ (Λ : ℝ) ^ σ := Real.rpow_nonneg hΛ σ
  have hpow : ((Λ : ℝ) ^ σ) ^ e = (Λ : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ, hσe, Real.rpow_two]
  have h' : ((A : ℝ) * (Λ : ℝ) ^ σ) ^ e ≤ (B : ℝ) ^ e := by
    rw [mul_pow, hpow]
    exact_mod_cast h
  exact (pow_le_pow_iff_left₀ (mul_nonneg (Nat.cast_nonneg _) hX) (Nat.cast_nonneg _) he).1 h'

/-! ## The fitting inequality -/

set_option maxHeartbeats 4000000 in
/-- **W3 arithmetic.** For every `K` and real `C`, for large `n`,
`m + K (⌊C (ν (log₂ ν)^σ + 1)⌋₊ + 1) + ν + n + 1 ≤ G q n`. -/
theorem fits (j a b K : ℕ) (C : ℝ) : ∀ᶠ n in atTop,
    lpM2 (sOf j) a b n
      + K * (⌊C * ((nuOf j a b n : ℝ) * Real.logb 2 (nuOf j a b n) ^ sigmaOf j + 1)⌋₊ + 1)
      + nuOf j a b n + n + 1 ≤ G (qOf j) n := by
  -- constants
  set e := qOf j with he_def
  have he1 : 1 ≤ e := one_le_qOf j
  have hej : e = 4 * 2 ^ j := by rw [he_def, qOf, pow_add]; ring
  set C' : ℕ := ⌈max C 0⌉₊ with hC'
  set K₁ : ℕ := 2 * K * C' + K + 4 with hK₁
  set C₀ : ℕ := 2 * (2 * a + b + 1) with hC₀
  set D₁ : ℕ := 9 * (16 * K₁ * C₀) ^ e with hD₁
  set D₂ : ℕ := 9 * (12 * K₁) ^ e + C₀ + 3 with hD₂
  -- eventual conditions
  have evP : ∀ᶠ n in atTop, D₁ * (lpP2 a b n + 2) ^ (7 * e) ≤ 2 ^ lpP2 a b n :=
    eventually_lpTime (Params.eventually_of_p (eventually_poly_le D₁ (7 * e)))
  have evL : ∀ᶠ n in atTop, lpLam2 a b n ^ 10 < lpTime a b n :=
    eventually_lpTime (Params.lam_pow_lt_t 10)
  have evD : ∀ᶠ n in atTop, D₂ ≤ lpLam2 a b n :=
    eventually_lpTime (Params.eventually_of_lam (eventually_ge_atTop D₂))
  have evP2 : ∀ᶠ n in atTop, 2 ≤ lpP2 a b n :=
    eventually_lpTime (Params.eventually_of_p (eventually_ge_atTop 2))
  filter_upwards [evP, evL, evD, evP2, eventually_ge_atTop 2] with n hP hL hD hP2 hn
  -- names
  set t := lpTime a b n with ht
  set lam := lpLam2 a b n with hlam
  set p := lpP2 a b n with hp
  set T := lpT2 (sOf j) a b n with hT
  set m := lpM2 (sOf j) a b n with hm
  set ν := nuOf j a b n with hν
  set r := rootLog e n with hr
  set Q := (p + 2) ^ 7 with hQ
  have hT' : T = p / 2 ^ j := lpT2_sOf j a b n
  have hmdef : m = (p + 1) ^ 6 * ((t + 2 ^ T - 1) / 2 ^ T) := rfl
  have hνdef : ν = 2 * n + 1 + (p + 2) * m := by
    rw [hν, nuOf, padLen]; ring
  have ht2 : 2 ≤ t := by have := lt_lpTime a b n; omega
  -- (F1) 2^T ≤ 2^p ≤ λ ≤ t
  have hpl : 2 ^ p ≤ lam := Params.two_pow_p_le ht2
  have hlt : lam < 2 ^ (p + 1) := Params.lam_lt_two_pow_p t
  have hTp : T ≤ p := by rw [hT']; exact Nat.div_le_self _ _
  have h2T : 2 ^ T ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hTp
  have hlam1 : 3 ≤ lam := by omega
  have hlamt : lam ≤ t := by
    have : lam ≤ lam ^ 10 := Nat.le_self_pow (by norm_num) lam
    omega
  have h2Tt : 2 ^ T ≤ t := by omega
  -- (F2) m 2^T ≤ 2 (p+1)^6 t
  have hm2T : m * 2 ^ T ≤ 2 * (p + 1) ^ 6 * t := by
    have e1 := Params.ceilDiv_mul_le t (2 ^ T)
    have e2 : (t + 2 ^ T - 1) / 2 ^ T * 2 ^ T ≤ 2 * t := by omega
    calc m * 2 ^ T = (p + 1) ^ 6 * ((t + 2 ^ T - 1) / 2 ^ T * 2 ^ T) := by rw [hmdef]; ring
      _ ≤ (p + 1) ^ 6 * (2 * t) := Nat.mul_le_mul_left _ e2
      _ = 2 * (p + 1) ^ 6 * t := by ring
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hpQ : (p + 2) * (p + 1) ^ 6 ≤ Q := by
    rw [hQ]
    calc (p + 2) * (p + 1) ^ 6 ≤ (p + 2) * (p + 2) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
      _ = (p + 2) ^ 7 := by ring
  -- (F4) (p+2) m 2^T ≤ 2 Q C₀ n^2
  have htC : t ≤ C₀ * n ^ 2 := lpTime_le a b n (by omega)
  have hF4 : (p + 2) * m * 2 ^ T ≤ 2 * Q * (C₀ * n ^ 2) := by
    calc (p + 2) * m * 2 ^ T = (p + 2) * (m * 2 ^ T) := by ring
      _ ≤ (p + 2) * (2 * (p + 1) ^ 6 * t) := Nat.mul_le_mul_left _ hm2T
      _ = 2 * ((p + 2) * (p + 1) ^ 6) * t := by ring
      _ ≤ 2 * Q * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpQ)
      _ ≤ 2 * Q * (C₀ * n ^ 2) := Nat.mul_le_mul_left _ htC
  -- (F7) Q ≤ λ and D₁ Q^e ≤ λ
  have hQe : D₁ * Q ^ e ≤ lam := by
    have : Q ^ e = (p + 2) ^ (7 * e) := by rw [hQ, ← pow_mul]
    rw [this]; exact le_trans hP hpl
  have hK₁pos : 0 < K₁ := by rw [hK₁]; omega
  have hC₀pos : 0 < C₀ := by rw [hC₀]; omega
  have hD₁1 : 1 ≤ D₁ := by
    have : 0 < (16 * K₁ * C₀) ^ e := pow_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hK₁pos) hC₀pos) e
    rw [hD₁]; omega
  have hQl : Q ≤ lam := by
    have : Q ≤ Q ^ e := Nat.le_self_pow (by omega) Q
    calc Q ≤ Q ^ e := this
      _ ≤ D₁ * Q ^ e := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ lam := hQe
  -- (F6) ν ≤ 5 Q t ≤ 2^(3 λ); Λ := clog ν ≤ 3 λ
  have hm_le : m ≤ 2 * (p + 1) ^ 6 * t := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hm2T
  have hν5 : ν ≤ 5 * Q * t := by
    have hnt := lt_lpTime a b n
    have e1 : (p + 2) * m ≤ 2 * Q * t := by
      calc (p + 2) * m ≤ (p + 2) * (2 * (p + 1) ^ 6 * t) := Nat.mul_le_mul_left _ hm_le
        _ = 2 * ((p + 2) * (p + 1) ^ 6) * t := by ring
        _ ≤ 2 * Q * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpQ)
    have e2 : 3 * t ≤ 3 * Q * t := by
      calc 3 * t = 3 * 1 * t := by ring
        _ ≤ 3 * Q * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQ1)
    rw [hνdef]
    have e3 : 5 * Q * t = 3 * Q * t + 2 * Q * t := by ring
    omega
  have hνpow : ν ≤ 2 ^ (3 * lam) := by
    have htl : t ≤ 2 ^ lam := Params.t_le_two_pow_lam t
    have hl : lam < 2 ^ lam := Params.lt_two_pow' lam
    have h5 : 5 ≤ 2 ^ lam := by
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) hlam1
    calc ν ≤ 5 * Q * t := hν5
      _ ≤ 2 ^ lam * 2 ^ lam * 2 ^ lam := Nat.mul_le_mul (Nat.mul_le_mul h5 (by omega)) htl
      _ = 2 ^ (3 * lam) := by rw [← pow_add, ← pow_add]; ring_nf
  set Λ := Nat.clog 2 ν with hΛ
  have hΛ3 : Λ ≤ 3 * lam := Nat.clog_le_of_le_pow hνpow
  have hν1 : 2 ≤ ν := by rw [hνdef]; omega
  have hΛ1 : 1 ≤ Λ := Nat.clog_pos one_lt_two hν1
  -- (F10, F11) log₂ ν ≤ Λ, (log₂ ν)^σ ≤ Λ^σ =: X
  have hνpos : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast (show 0 < ν by omega)
  have hlog0 : 0 ≤ Real.logb 2 (ν : ℝ) := Real.logb_nonneg one_lt_two (by exact_mod_cast (show 1 ≤ ν by omega))
  have hlogΛ : Real.logb 2 (ν : ℝ) ≤ (Λ : ℝ) := by
    have h1 : (ν : ℝ) ≤ (2 : ℝ) ^ Λ := by exact_mod_cast Nat.le_pow_clog one_lt_two ν
    calc Real.logb 2 (ν : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ Λ) := Real.logb_le_logb_of_le one_lt_two hνpos h1
      _ = (Λ : ℝ) := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  set σ := sigmaOf j with hσ
  have hσ0 : 0 ≤ σ := (sigmaOf_pos j).le
  set X : ℝ := (Λ : ℝ) ^ σ with hX
  have hlogX : Real.logb 2 (ν : ℝ) ^ σ ≤ X := Real.rpow_le_rpow hlog0 hlogΛ hσ0
  have hX1 : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast hΛ1) hσ0
  -- (F13) Tb ≤ C' (ν X + 1)
  set Tb := ⌊C * ((ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1)⌋₊ with hTb
  have hY0 : 0 ≤ (ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1 := by
    have := Real.rpow_nonneg hlog0 σ; positivity
  have hCC : C ≤ (C' : ℝ) := le_trans (le_max_left C 0) (Nat.le_ceil _)
  have hC'0 : (0 : ℝ) ≤ (C' : ℝ) := Nat.cast_nonneg _
  have hTbR : (Tb : ℝ) ≤ (C' : ℝ) * ((ν : ℝ) * X + 1) := by
    have e1 : C * ((ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1) ≤
        (C' : ℝ) * ((ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1) := mul_le_mul_of_nonneg_right hCC hY0
    have e2 : (Tb : ℝ) ≤ (C' : ℝ) * ((ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1) :=
      le_trans (Nat.cast_le.2 (Nat.floor_mono e1)) (Nat.floor_le (mul_nonneg hC'0 hY0))
    have e3 : (ν : ℝ) * Real.logb 2 (ν : ℝ) ^ σ + 1 ≤ (ν : ℝ) * X + 1 := by
      have := mul_le_mul_of_nonneg_left hlogX hνpos.le; linarith
    exact le_trans e2 (mul_le_mul_of_nonneg_left e3 hC'0)
  -- (F14) LHS ≤ K₁ ν X
  have hmν : m ≤ ν := by
    have : m ≤ (p + 2) * m := Nat.le_mul_of_pos_left m (by omega)
    rw [hνdef]; omega
  have hnν : n + 1 ≤ ν := by rw [hνdef]; omega
  have hνX : (ν : ℝ) ≤ (ν : ℝ) * X := le_mul_of_one_le_right hνpos.le hX1
  have h1νX : (1 : ℝ) ≤ (ν : ℝ) * X := by
    have : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (show 1 ≤ ν by omega)
    linarith
  have hLHS : ((m + K * (Tb + 1) + ν + n + 1 : ℕ) : ℝ) ≤ (K₁ : ℝ) * ((ν : ℝ) * X) := by
    push_cast
    have e1 : (m : ℝ) ≤ ν := by exact_mod_cast hmν
    have e2 : (n : ℝ) + 1 ≤ ν := by exact_mod_cast hnν
    have e3 : (K : ℝ) * ((Tb : ℝ) + 1) ≤ (K : ℝ) * ((C' : ℝ) * ((ν : ℝ) * X + 1) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have e4 : (K : ℝ) * (C' : ℝ) ≤ (K : ℝ) * (C' : ℝ) * ((ν : ℝ) * X) :=
      le_mul_of_one_le_right (mul_nonneg hK0 hC'0) h1νX
    have e5 : (K : ℝ) ≤ (K : ℝ) * ((ν : ℝ) * X) := le_mul_of_one_le_right hK0 h1νX
    rw [hK₁]; push_cast
    linarith
  -- (F15) r^e ≤ 2^e λ
  have hre : r ^ e ≤ 2 ^ e * lam :=
    le_trans (rootLog_pow_le e n he1) (Nat.mul_le_mul_left _ (log_succ_le_lam a b n (by omega)))
  have hr0 : 0 < r := rootLog_pos' e n he1
  -- λ^4 ≤ n
  have hl4 : lam ^ 4 ≤ n := by
    have hC₀l : C₀ ≤ lam := by omega
    have e1 : lam ^ 10 < C₀ * n ^ 2 := lt_of_lt_of_le hL htC
    have e2 : C₀ * lam ^ 8 ≤ lam ^ 10 := by
      calc C₀ * lam ^ 8 ≤ lam ^ 2 * lam ^ 8 :=
            Nat.mul_le_mul_right _ (le_trans hC₀l (Nat.le_self_pow (by norm_num) lam))
        _ = lam ^ 10 := by ring
    have e3 : (lam ^ 4) ^ 2 < n ^ 2 := by
      have : C₀ * (lam ^ 4) ^ 2 < C₀ * n ^ 2 := by
        calc C₀ * (lam ^ 4) ^ 2 = C₀ * lam ^ 8 := by ring
          _ < C₀ * n ^ 2 := lt_of_le_of_lt e2 e1
      exact Nat.lt_of_mul_lt_mul_left this
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 e3 |>.le
  -- (F16) 6 K₁ r X ≤ n
  have hF16 : ((6 * K₁ * r : ℕ) : ℝ) * X ≤ (n : ℝ) := by
    apply rpow_trick (sigma_mul_q j) (by omega)
    rw [← he_def]
    have e1 : (6 * K₁ * r) ^ e * Λ ^ 2 ≤ (6 * K₁) ^ e * (2 ^ e * lam) * (3 * lam) ^ 2 := by
      rw [mul_pow (6 * K₁) r e]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hre) (Nat.pow_le_pow_left hΛ3 2)
    have e2 : (6 * K₁) ^ e * (2 ^ e * lam) * (3 * lam) ^ 2 = 9 * (12 * K₁) ^ e * lam ^ 3 := by
      have : (12 * K₁) ^ e = (6 * K₁) ^ e * 2 ^ e := by rw [← mul_pow]; ring_nf
      rw [this]; ring
    have e3 : 9 * (12 * K₁) ^ e * lam ^ 3 ≤ lam * lam ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have e4 : lam * lam ^ 3 = lam ^ 4 := by ring
    have e5 : n ≤ n ^ e := Nat.le_self_pow (by omega) n
    omega
  -- (F17) 4 K₁ C₀ Q r X ≤ 2^T
  have hF17 : ((4 * K₁ * C₀ * Q * r : ℕ) : ℝ) * X ≤ ((2 ^ T : ℕ) : ℝ) := by
    apply rpow_trick (sigma_mul_q j) (by omega)
    rw [← he_def]
    -- λ^4 < (2^T)^e 2^e
    have hp1 : p + 1 ≤ (T + 1) * 2 ^ j := by
      have := Nat.lt_div_mul_add (a := p) (b := 2 ^ j) (by positivity)
      rw [hT', Nat.add_mul, one_mul]; omega
    have hl4T : lam ^ 4 < (2 ^ T) ^ e * 2 ^ e := by
      have e1 : lam < 2 ^ ((T + 1) * 2 ^ j) :=
        lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hp1)
      have e2 : lam ^ 4 < (2 ^ ((T + 1) * 2 ^ j)) ^ 4 := Nat.pow_lt_pow_left e1 (by norm_num)
      have e3 : (2 ^ ((T + 1) * 2 ^ j)) ^ 4 = (2 ^ T) ^ e * 2 ^ e := by
        rw [hej, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      omega
    have e1 : (4 * K₁ * C₀ * Q * r) ^ e * Λ ^ 2 ≤
        (4 * K₁ * C₀) ^ e * Q ^ e * (2 ^ e * lam) * (3 * lam) ^ 2 := by
      rw [mul_pow (4 * K₁ * C₀ * Q) r e, mul_pow (4 * K₁ * C₀) Q e]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hre) (Nat.pow_le_pow_left hΛ3 2)
    have e2 : (4 * K₁ * C₀) ^ e * Q ^ e * (2 ^ e * lam) * (3 * lam) ^ 2 * 2 ^ e =
        (9 * (16 * K₁ * C₀) ^ e * Q ^ e) * lam ^ 3 := by
      have : (16 * K₁ * C₀) ^ e = (4 * K₁ * C₀) ^ e * 2 ^ e * 2 ^ e := by
        rw [← mul_pow, ← mul_pow]; ring_nf
      rw [this]; ring
    have e3 : (9 * (16 * K₁ * C₀) ^ e * Q ^ e) * lam ^ 3 ≤ lam * lam ^ 3 := by
      apply Nat.mul_le_mul_right; rw [← hD₁]; exact hQe
    have e4 : lam * lam ^ 3 = lam ^ 4 := by ring
    have e5 : (4 * K₁ * C₀ * Q * r) ^ e * Λ ^ 2 * 2 ^ e < (2 ^ T) ^ e * 2 ^ e := by
      calc (4 * K₁ * C₀ * Q * r) ^ e * Λ ^ 2 * 2 ^ e
            ≤ (4 * K₁ * C₀) ^ e * Q ^ e * (2 ^ e * lam) * (3 * lam) ^ 2 * 2 ^ e :=
            Nat.mul_le_mul_right _ e1
        _ = (9 * (16 * K₁ * C₀) ^ e * Q ^ e) * lam ^ 3 := e2
        _ ≤ lam ^ 4 := by omega
        _ < (2 ^ T) ^ e * 2 ^ e := hl4T
    exact (Nat.lt_of_mul_lt_mul_right e5).le
  -- (F18) LHS * r ≤ n^2
  have hfinal : ((m + K * (Tb + 1) + ν + n + 1 : ℕ) : ℝ) * (r : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by
    have hr0' : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have hK10 : (0 : ℝ) ≤ (K₁ : ℝ) := Nat.cast_nonneg _
    have hνsplit : (ν : ℝ) = (2 * (n : ℝ) + 1) + ((p : ℝ) + 2) * (m : ℝ) := by
      rw [hνdef]; push_cast; ring
    -- part 1: K₁ (2n+1) X r ≤ n^2 / 2
    have hP1 : (K₁ : ℝ) * (2 * (n : ℝ) + 1) * X * r ≤ (n : ℝ) ^ 2 / 2 := by
      have e1 : ((6 * K₁ * r : ℕ) : ℝ) * X = 6 * (K₁ : ℝ) * (r : ℝ) * X := by push_cast; ring
      rw [e1] at hF16
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have e2 : (K₁ : ℝ) * (2 * (n : ℝ) + 1) * X * r ≤ (K₁ : ℝ) * (3 * (n : ℝ)) * X * r := by
        have : 0 ≤ (K₁ : ℝ) * X * r := by positivity
        have h := mul_le_mul_of_nonneg_left hn1 this
        linarith
      have e3 : (K₁ : ℝ) * (3 * (n : ℝ)) * X * r = (n : ℝ) * (6 * (K₁ : ℝ) * (r : ℝ) * X) / 2 := by ring
      have e4 : (n : ℝ) * (6 * (K₁ : ℝ) * (r : ℝ) * X) ≤ (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hF16 (by positivity)
      rw [e3] at e2
      linarith
    -- part 2: K₁ (p+2) m X r ≤ n^2 / 2
    have hP2 : (K₁ : ℝ) * (((p : ℝ) + 2) * (m : ℝ)) * X * r ≤ (n : ℝ) ^ 2 / 2 := by
      have e1 : ((4 * K₁ * C₀ * Q * r : ℕ) : ℝ) * X = 4 * (K₁ : ℝ) * (C₀ : ℝ) * (Q : ℝ) * (r : ℝ) * X := by
        push_cast; ring
      rw [e1] at hF17
      have hF4R : ((p : ℝ) + 2) * (m : ℝ) * ((2 ^ T : ℕ) : ℝ) ≤ 2 * (Q : ℝ) * ((C₀ : ℝ) * (n : ℝ) ^ 2) := by
        exact_mod_cast hF4
      have h2T0 : (0 : ℝ) < ((2 ^ T : ℕ) : ℝ) := by positivity
      have hpm0 : (0 : ℝ) ≤ ((p : ℝ) + 2) * (m : ℝ) := by positivity
      have hA0 : (0 : ℝ) ≤ (K₁ : ℝ) * X * r := by positivity
      -- multiply by 2^T
      have key : (K₁ : ℝ) * (((p : ℝ) + 2) * (m : ℝ)) * X * r * ((2 ^ T : ℕ) : ℝ) ≤
          (n : ℝ) ^ 2 / 2 * ((2 ^ T : ℕ) : ℝ) := by
        calc (K₁ : ℝ) * (((p : ℝ) + 2) * (m : ℝ)) * X * r * ((2 ^ T : ℕ) : ℝ)
              = ((K₁ : ℝ) * X * r) * (((p : ℝ) + 2) * (m : ℝ) * ((2 ^ T : ℕ) : ℝ)) := by ring
          _ ≤ ((K₁ : ℝ) * X * r) * (2 * (Q : ℝ) * ((C₀ : ℝ) * (n : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left hF4R hA0
          _ = (n : ℝ) ^ 2 / 2 * (4 * (K₁ : ℝ) * (C₀ : ℝ) * (Q : ℝ) * (r : ℝ) * X) := by ring
          _ ≤ (n : ℝ) ^ 2 / 2 * ((2 ^ T : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hF17 (by positivity)
      exact le_of_mul_le_mul_right key h2T0
    calc ((m + K * (Tb + 1) + ν + n + 1 : ℕ) : ℝ) * (r : ℝ) ≤ (K₁ : ℝ) * ((ν : ℝ) * X) * r :=
          mul_le_mul_of_nonneg_right hLHS hr0'
      _ = (K₁ : ℝ) * (2 * (n : ℝ) + 1) * X * r + (K₁ : ℝ) * (((p : ℝ) + 2) * (m : ℝ)) * X * r := by
          rw [hνsplit]; ring
      _ ≤ (n : ℝ) ^ 2 / 2 + (n : ℝ) ^ 2 / 2 := add_le_add hP1 hP2
      _ = ((n ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have hnat : (m + K * (Tb + 1) + ν + n + 1) * r ≤ n ^ 2 := by exact_mod_cast hfinal
  unfold G
  exact (Nat.le_div_iff_mul_le hr0).2 hnat

end

end P1Wrap.W3
