import P1Wrap.Params

open P1Wrap.Params

theorem P1P7.SolFit.cone_local_fit' (K : P1Wrap.Consts) (C A c : ℕ) (hC : C ≤ K.C2) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ W : ℕ, W ≤ A * (P1Wrap.Params.B t + 1) →
      2 ^ (c * C * (C ^ P1Wrap.Params.T K t * (W + 1))) * (2 * P1Wrap.Params.lam t + 2) ^ c ≤
        P1Wrap.Params.m K t := by
  let D := c * C * (2 * A + 1) + 2 * c
  let P := max 6 (64 * (2 * D))
  let t₀ : ℕ := 2 ^ (2 ^ P)
  refine ⟨t₀, fun t ht W hW => ?_⟩
  have ht2 : 2 ≤ t := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ t₀ := Nat.pow_le_pow_right (by decide) (Nat.one_le_pow _ _ (by decide))
      _ ≤ t := ht
  have hp : P ≤ p t := by
    have hLam : lam t₀ = 2 ^ P := Nat.clog_pow 2 _ (by decide)
    calc
      P = Nat.log 2 (2 ^ P) := (Nat.log_pow (by decide) P).symm
      _ = p t₀ := by rw [p, hLam]
      _ ≤ p t := Nat.log_mono_right (Nat.clog_mono_right 2 ht)
  have hp6 : 6 ≤ p t := (le_max_left _ _).trans hp
  have hpD : 64 * (2 * D) ≤ p t := (le_max_right _ _).trans hp

  let q := p t / 64
  let exponent := c * C * (C ^ T K t * (W + 1))
  have hWidth : W + 1 ≤ (2 * A + 1) * B t := by
    have hB := B_pos t
    calc
      W + 1 ≤ A * (B t + 1) + 1 := Nat.add_le_add_right hW 1
      _ ≤ A * (2 * B t) + B t :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hB
      _ = (2 * A + 1) * B t := by ring
  have hCpow : C ^ T K t ≤ 2 ^ q := by
    have hc2 := c2_T K t
    calc
      C ^ T K t ≤ (2 ^ K.c2) ^ T K t := Nat.pow_le_pow_left (hC.trans K.C2_le) _
      _ = 2 ^ (K.c2 * T K t) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by dsimp [q]; omega)

  -- Charge the polynomial factor to the same binary exponent.
  have hPoly : (2 * lam t + 2) ^ c ≤ 2 ^ (c * (p t + 2)) := by
    have hLam := lam_lt_two_pow_p t
    have hBase : 2 * lam t + 2 ≤ 2 ^ (p t + 2) := by
      rw [show p t + 2 = (p t + 1) + 1 by omega, pow_succ]
      omega
    calc
      _ ≤ (2 ^ (p t + 2)) ^ c := Nat.pow_le_pow_left hBase _
      _ = _ := by rw [← pow_mul, Nat.mul_comm (p t + 2) c]
  have hBlock : p t + 2 ≤ 2 * (2 ^ q * B t) := by
    have h := two_mul_succ_le_two_pow (p t / 2) (by omega)
    have hB : p t + 2 ≤ 2 * B t := by
      unfold B
      omega
    exact hB.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity)))
  have hTotal : exponent + c * (p t + 2) ≤ D * (2 ^ q * B t) := by
    calc
      _ ≤ c * C * (2 ^ q * ((2 * A + 1) * B t)) + c * (2 * (2 ^ q * B t)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hCpow hWidth))
          (Nat.mul_le_mul_left _ hBlock)
      _ = _ := by dsimp [D]; ring

  have hD : 2 * D ≤ 2 ^ q := le_trans (by dsimp [q]; omega) (lt_two_pow' q).le
  have hHalf : 2 * (exponent + c * (p t + 2)) ≤ lam t := by
    calc
      _ ≤ 2 * (D * (2 ^ q * B t)) := Nat.mul_le_mul_left 2 hTotal
      _ = (2 * D) * (2 ^ q * B t) := (Nat.mul_assoc _ _ _).symm
      _ ≤ 2 ^ q * (2 ^ q * B t) := Nat.mul_le_mul_right _ hD
      _ = 2 ^ (q + (q + p t / 2)) := by rw [B, ← pow_add, ← pow_add]
      _ ≤ 2 ^ p t := Nat.pow_le_pow_right (by decide) (by dsimp [q]; omega)
      _ ≤ lam t := two_pow_p_le ht2
  have hExp : exponent + c * (p t + 2) + T K t + 1 ≤ lam t := by
    have hP := two_mul_succ_le_two_pow (p t) (by omega)
    have hT := T_le_p K t
    have hLam := two_pow_p_le ht2
    omega

  have hCost : (2 ^ exponent * (2 * lam t + 2) ^ c) * 2 ^ T K t * 2 ≤ 2 ^ lam t := by
    calc
      _ ≤ (2 ^ exponent * 2 ^ (c * (p t + 2))) * 2 ^ T K t * 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hPoly))
      _ = 2 ^ (exponent + c * (p t + 2) + T K t + 1) := by rw [← pow_add, ← pow_add, pow_succ]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hExp
  have hCostTime : (2 ^ exponent * (2 * lam t + 2) ^ c) * 2 ^ T K t ≤ t := by
    have hLam := two_pow_lam_lt ht2
    omega
  apply Nat.le_of_mul_le_mul_right _ (by positivity : 0 < 2 ^ T K t)
  exact hCostTime.trans ((Nat.le_mul_of_pos_left t (by positivity : 0 < (p t + 1) ^ 6)).trans
    (m_mul_two_pow_T_ge K t))

#print axioms P1P7.SolFit.cone_local_fit'
