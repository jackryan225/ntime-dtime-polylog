import P1Wrap.Wrapper

/-!
# Arithmetic support for the machine lemmas of W3 (for whoever builds `InnerProg`, `OuterProg`)

* `lpK2_le_guessLen`: the selector `γ` (`k = ⌈log₂ t⌉` bits) fits into the guess of the inner verifier
  (`guessLen ν = ⌊log₂ ν²⌋` bits), for every `n ≥ 1`.
* `lpCost2_le_nu`: one branch of `R` costs at most `c ν` (the padding pays for it).
* `length_padIn_eq`: the padded input has length `ν`.
-/

namespace P1Wrap.W3

open P1Int C1Challenge

theorem sq_le_two_pow_succ : ∀ l : ℕ, l ^ 2 ≤ 2 ^ l + 1
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | l + 4 => by
      have ih := sq_le_two_pow_succ (l + 3)
      have h2 : 2 * (l + 3) + 1 ≤ 2 ^ (l + 3) := by
        have := Params.two_mul_succ_le_two_pow (l + 3) (by omega)
        omega
      have e1 : (l + 4) ^ 2 = (l + 3) ^ 2 + (2 * (l + 3) + 1) := by ring
      have e2 : 2 ^ (l + 4) = 2 ^ (l + 3) + 2 ^ (l + 3) := by ring
      rw [e1, e2]
      omega

/-- `k = ⌈log₂ t⌉ ≤ ⌊log₂ ν²⌋ = guessLen ν` when `t ≥ 2`. -/
theorem lpK2_le_guessLen_of (j a b n : ℕ) (ht2' : 2 ≤ lpTime a b n) :
    lpK2 a b n ≤ guessLen (nuOf j a b n) := by
  set t := lpTime a b n with ht
  set lam := lpLam2 a b n with hlam
  set p := lpP2 a b n with hp
  set T := lpT2 (sOf j) a b n with hT
  set m := lpM2 (sOf j) a b n with hm
  set ν := nuOf j a b n with hν
  have ht2 : 2 ≤ t := ht2'
  have hT' : T = p / 2 ^ j := lpT2_sOf j a b n
  have hTp : T ≤ p := by rw [hT']; exact Nat.div_le_self _ _
  have h2T : 2 ^ T ≤ lam :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hTp) (Params.two_pow_p_le ht2)
  have hlam1 : 1 ≤ lam := Params.lam_pos ht2
  -- m 2^T ≥ t
  have hm2T : t ≤ m * 2 ^ T := by
    have e1 := Params.le_ceilDiv_mul t (2 ^ T) (by positivity)
    have e2 : (t + 2 ^ T - 1) / 2 ^ T ≤ m := Nat.le_mul_of_pos_left _ (by positivity)
    calc t ≤ (t + 2 ^ T - 1) / 2 ^ T * 2 ^ T := e1
      _ ≤ m * 2 ^ T := Nat.mul_le_mul_right _ e2
  have hνdef : ν = 2 * n + 1 + (p + 2) * m := by rw [hν, nuOf, padLen]; ring
  -- ν λ ≥ 2 t
  have hνl : 2 * t ≤ ν * lam := by
    have e1 : 2 * m ≤ ν := by
      have : 2 * m ≤ (p + 2) * m := Nat.mul_le_mul_right _ (by omega)
      omega
    calc 2 * t ≤ 2 * (m * 2 ^ T) := Nat.mul_le_mul_left _ hm2T
      _ = (2 * m) * 2 ^ T := by ring
      _ ≤ ν * lam := Nat.mul_le_mul e1 h2T
  -- 2^λ < 2t and λ² ≤ 2t
  have h2l : 2 ^ lam < 2 * t := Params.two_pow_lam_lt ht2
  have hl2 : lam ^ 2 ≤ 2 * t := by have := sq_le_two_pow_succ lam; omega
  -- 2^λ < ν²
  have key : 2 ^ lam * lam ^ 2 < ν ^ 2 * lam ^ 2 := by
    calc 2 ^ lam * lam ^ 2 < (2 * t) * (2 * t) :=
          Nat.mul_lt_mul_of_lt_of_le h2l hl2 (by positivity)
      _ ≤ (ν * lam) * (ν * lam) := Nat.mul_le_mul hνl hνl
      _ = ν ^ 2 * lam ^ 2 := by ring
  have hpow : 2 ^ lam ≤ ν ^ 2 := (Nat.lt_of_mul_lt_mul_right key).le
  unfold guessLen lpK2
  exact Nat.le_log_of_pow_le one_lt_two hpow

/-- `k ≤ guessLen ν` for every `n`. -/
theorem lpK2_le_guessLen (j a b n : ℕ) : lpK2 a b n ≤ guessLen (nuOf j a b n) := by
  by_cases ht : 2 ≤ lpTime a b n
  · exact lpK2_le_guessLen_of j a b n ht
  · have h0 : lpK2 a b n = 0 := by
      unfold lpK2 lpLam2
      exact Nat.clog_of_right_le_one (by omega) 2
    rw [h0]; exact Nat.zero_le _

/-- One branch of `R` costs at most `c ν`. -/
theorem lpCost2_le_nu (c j a b n : ℕ) : lpCost2 c (sOf j) a b n ≤ c * nuOf j a b n := by
  unfold lpCost2 nuOf padLen
  have : lpM2 (sOf j) a b n * (lpP2 a b n + 1) ≤
      2 * n + 1 + lpM2 (sOf j) a b n + (lpP2 a b n + 1) * lpM2 (sOf j) a b n := by
    rw [mul_comm]; omega
  calc c * lpM2 (sOf j) a b n * (lpP2 a b n + 1) = c * (lpM2 (sOf j) a b n * (lpP2 a b n + 1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ this

theorem length_padIn_eq (j a b : ℕ) (x : List Bool) (u : Fin (lpM2 (sOf j) a b x.length) → Bool) :
    (padIn j a b x (List.ofFn u)).length = nuOf j a b x.length :=
  length_padIn j a b x _ (List.length_ofFn)

end P1Wrap.W3
