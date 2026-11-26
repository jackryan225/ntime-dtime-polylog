import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-!
# P10: the parameter arithmetic of Lemma P (task P10 of research/g3/leanplan/PLAN.md)

Sources: paper `research/papers/ntime-dtime-polylog.tex` l.574-602 (Lemma P, parameters), l.655-664 (eq:p1-p3),
l.765 (eq:size), l.800-806 (eq:zlen, eq:hidden), l.1060-1103 (lem:space, lem:time); Astra run
`runs/astra/g3-c1-portcase-20261125T063943Z.md` sec. 1 (1), sec. 3 (4), sec. 4 (5).

Everything is natural-number arithmetic. The exponent of Lemma P is `s = 2^-j`; then `T = ⌊s p⌋₊ = p / 2^j`
exactly (`T_eq_floor`), and every real-power bound of the paper (`λ^s`, `λ^{17/32}`, `λ^{3/4}`) is stated as a
bound between natural powers (raise both sides to a power that clears the denominator).

Notation (paper / Lean): `t` time bound (`t = a (n^2+1)` in Lemma P), `λ = ⌈log₂ t⌉` (`lam`), `p = ⌊log₂ λ⌋`,
`T = ⌊s p⌋`, `B = 2^⌊p/2⌋`, `h = ⌊19p/2⌋`, `N = 2^h`, `b = B N` (`bb`), `I = ⌈a 2^λ / b⌉`,
`m = (p+1)^6 ⌈t / 2^T⌉`.
-/

namespace P1Wrap

open Filter

/-- The fixed constants of the compressor over `F_2` (paper sec. 5): `b0`, `C2`, `c2` with `C2 ≤ 2^c2`
(the paper takes `c2 = ⌈log₂ C2⌉`), and `j` with `2^j ≥ 64 (1 + b0 + c2)`, so that `s = 2^-j ≤ 1/(64(1+b0+c2))`
(the paper takes the least such `j`). -/
structure Consts where
  j : ℕ
  b0 : ℕ
  C2 : ℕ
  c2 : ℕ
  C2_le : C2 ≤ 2 ^ c2
  j_spec : 64 * (1 + b0 + c2) ≤ 2 ^ j

namespace Params

variable (K : Consts)

/-- `λ = ⌈log₂ t⌉`. -/
def lam (t : ℕ) : ℕ := Nat.clog 2 t
/-- `p = ⌊log₂ λ⌋`. -/
def p (t : ℕ) : ℕ := Nat.log 2 (lam t)
/-- `T = ⌊s p⌋ = p / 2^j` (see `T_eq_floor`). -/
def T (t : ℕ) : ℕ := p t / 2 ^ K.j
/-- small block length `B = 2^⌊p/2⌋`. -/
def B (t : ℕ) : ℕ := 2 ^ (p t / 2)
/-- `h = ⌊19 p / 2⌋`. -/
def h (t : ℕ) : ℕ := 19 * p t / 2
/-- number of lanes `N = 2^h`. -/
def N (t : ℕ) : ℕ := 2 ^ h t
/-- big block length `b = B N`. -/
def bb (t : ℕ) : ℕ := B t * N t
/-- number of big intervals `I = ⌈a 2^λ / b⌉`. -/
def I (a t : ℕ) : ℕ := (a * 2 ^ lam t + bb t - 1) / bb t
/-- `m = (p+1)^6 ⌈t / 2^T⌉` (exactly the `m` of `LemmaP` in PLAN.md sec. 3). -/
def m (t : ℕ) : ℕ := (p t + 1) ^ 6 * ((t + 2 ^ T K t - 1) / 2 ^ T K t)

/-! ## The exponent `s = 2^-j` -/

theorem T_eq_floor (t : ℕ) : ⌊((2 : ℝ) ^ (-(K.j : ℤ))) * (p t : ℝ)⌋₊ = T K t := by
  have : ((2 : ℝ) ^ (-(K.j : ℤ))) * (p t : ℝ) = ((p t : ℕ) : ℝ) / ((2 ^ K.j : ℕ) : ℝ) := by
    rw [zpow_neg, zpow_natCast]; push_cast; ring
  rw [this, Nat.floor_div_eq_div]
  rfl

/-! ## Elementary facts on `λ` and `p` -/

theorem lam_pos {t : ℕ} (ht : 2 ≤ t) : 0 < lam t := Nat.clog_pos one_lt_two ht

theorem t_le_two_pow_lam (t : ℕ) : t ≤ 2 ^ lam t := Nat.le_pow_clog one_lt_two t

theorem two_pow_lam_lt {t : ℕ} (ht : 2 ≤ t) : 2 ^ lam t < 2 * t := by
  have h1 := Nat.pow_pred_clog_lt_self one_lt_two ht
  have h2 := lam_pos ht
  unfold lam at *
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 t = k + 1 := ⟨Nat.clog 2 t - 1, by omega⟩
  rw [hk] at h1 ⊢
  simp only [Nat.pred_succ] at h1
  rw [pow_succ]; omega

theorem two_pow_p_le {t : ℕ} (ht : 2 ≤ t) : 2 ^ p t ≤ lam t :=
  Nat.pow_log_le_self 2 (lam_pos ht).ne'

theorem lam_lt_two_pow_p (t : ℕ) : lam t < 2 ^ (p t + 1) :=
  Nat.lt_pow_succ_log_self one_lt_two _

/-- `T 2^j ≤ p < (T+1) 2^j`. -/
theorem T_mul_le (t : ℕ) : T K t * 2 ^ K.j ≤ p t := Nat.div_mul_le_self _ _

theorem p_lt_T_succ_mul (t : ℕ) : p t < (T K t + 1) * 2 ^ K.j := by
  have := Nat.lt_div_mul_add (a := p t) (b := 2 ^ K.j) (by positivity)
  unfold T; rw [add_mul, one_mul]; exact this

/-- If `64 c ≤ 2^j` then `64 c T ≤ p`. -/
theorem sixtyfour_mul_T_le {c : ℕ} (hc : 64 * c ≤ 2 ^ K.j) (t : ℕ) : 64 * (c * T K t) ≤ p t := by
  calc 64 * (c * T K t) = (64 * c) * T K t := by ring
    _ ≤ 2 ^ K.j * T K t := Nat.mul_le_mul_right _ hc
    _ = T K t * 2 ^ K.j := by ring
    _ ≤ p t := T_mul_le K t

theorem b0_T (t : ℕ) : 64 * (K.b0 * T K t) ≤ p t :=
  sixtyfour_mul_T_le K (le_trans (by nlinarith) K.j_spec) t

theorem c2_T (t : ℕ) : 64 * (K.c2 * T K t) ≤ p t :=
  sixtyfour_mul_T_le K (le_trans (by nlinarith) K.j_spec) t

theorem T_T (t : ℕ) : 64 * (1 * T K t) ≤ p t :=
  sixtyfour_mul_T_le K (le_trans (by nlinarith) K.j_spec) t

theorem T_le_p (t : ℕ) : T K t ≤ p t := by have := T_T K t; omega

/-! ## (eq:p2) `h - b0 T ≥ 9 p` and `2^{h - b0 T} ≥ (λ/2)^9` -/

theorem nine_p_add_b0T_le_h (t : ℕ) : 9 * p t + K.b0 * T K t ≤ h t := by
  have := b0_T K t
  unfold h
  generalize K.b0 * T K t = x at *
  omega

theorem lam_pow_nine_lt (t : ℕ) : lam t ^ 9 < 2 ^ 9 * 2 ^ (h t - K.b0 * T K t) := by
  have h1 := nine_p_add_b0T_le_h K t
  calc lam t ^ 9 < (2 ^ (p t + 1)) ^ 9 := Nat.pow_lt_pow_left (lam_lt_two_pow_p t) (by norm_num)
    _ = 2 ^ 9 * 2 ^ (9 * p t) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ 9 * 2 ^ (h t - K.b0 * T K t) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## (eq:p3) `C2^T ≤ λ^{1/64}`, `λ^{-s} ≤ 2^{-T} ≤ 2 λ^{-s}` -/

theorem C2_pow_T_pow_le {t : ℕ} (ht : 2 ≤ t) : (K.C2 ^ T K t) ^ 64 ≤ lam t := by
  have h1 := c2_T K t
  calc (K.C2 ^ T K t) ^ 64 ≤ ((2 ^ K.c2) ^ T K t) ^ 64 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left K.C2_le _) _
    _ = 2 ^ (64 * (K.c2 * T K t)) := by rw [← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2 ^ p t := Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ lam t := two_pow_p_le ht

/-- `2^T ≤ λ^s`. -/
theorem two_pow_T_pow_le {t : ℕ} (ht : 2 ≤ t) : (2 ^ T K t) ^ (2 ^ K.j) ≤ lam t := by
  calc (2 ^ T K t) ^ (2 ^ K.j) = 2 ^ (T K t * 2 ^ K.j) := by rw [← pow_mul]
    _ ≤ 2 ^ p t := Nat.pow_le_pow_right (by norm_num) (T_mul_le K t)
    _ ≤ lam t := two_pow_p_le ht

/-- `λ^s < 2^{T+1}`, i.e. `2^{-T} < 2 λ^{-s}`. -/
theorem lam_lt_two_pow_T_succ_pow (t : ℕ) : lam t < (2 ^ (T K t + 1)) ^ (2 ^ K.j) := by
  calc lam t < 2 ^ (p t + 1) := lam_lt_two_pow_p t
    _ ≤ 2 ^ ((T K t + 1) * 2 ^ K.j) :=
        Nat.pow_le_pow_right (by norm_num) (by have := p_lt_T_succ_mul K t; omega)
    _ = (2 ^ (T K t + 1)) ^ (2 ^ K.j) := by rw [← pow_mul]

/-- `2^T ≤ 2^{p/64}`. -/
theorem two_pow_T_le (t : ℕ) : 2 ^ T K t ≤ 2 ^ (p t / 64) :=
  Nat.pow_le_pow_right (by norm_num) (by have := T_T K t; omega)

/-! ## (eq:p1) `λ^{1/2}/4 ≤ B ≤ λ^{1/2}` -/

theorem B_pos (t : ℕ) : 0 < B t := by unfold B; positivity

theorem B_sq_le {t : ℕ} (ht : 2 ≤ t) : B t ^ 2 ≤ lam t := by
  calc B t ^ 2 = 2 ^ (2 * (p t / 2)) := by unfold B; rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ p t := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ lam t := two_pow_p_le ht

theorem lam_lt_sixteen_B_sq (t : ℕ) : lam t < 16 * B t ^ 2 := by
  calc lam t < 2 ^ (p t + 1) := lam_lt_two_pow_p t
    _ ≤ 2 ^ (4 + 2 * (p t / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 * B t ^ 2 := by unfold B; rw [pow_add, ← pow_mul]; ring_nf

/-- (1) of Astra: `B C2^{2T} ≤ λ^{17/32}`. -/
theorem B_C2_pow_le {t : ℕ} (ht : 2 ≤ t) : (B t * K.C2 ^ (2 * T K t)) ^ 32 ≤ lam t ^ 17 := by
  have h1 := c2_T K t
  have hB : B t ^ 32 ≤ 2 ^ (16 * p t) := by
    calc B t ^ 32 = 2 ^ (32 * (p t / 2)) := by unfold B; rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (16 * p t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC : (K.C2 ^ (2 * T K t)) ^ 32 ≤ 2 ^ p t := by
    calc (K.C2 ^ (2 * T K t)) ^ 32 ≤ ((2 ^ K.c2) ^ (2 * T K t)) ^ 32 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left K.C2_le _) _
      _ = 2 ^ (64 * (K.c2 * T K t)) := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 2 ^ p t := Nat.pow_le_pow_right (by norm_num) h1
  calc (B t * K.C2 ^ (2 * T K t)) ^ 32 = B t ^ 32 * (K.C2 ^ (2 * T K t)) ^ 32 := mul_pow _ _ _
    _ ≤ 2 ^ (16 * p t) * 2 ^ p t := Nat.mul_le_mul hB hC
    _ = (2 ^ p t) ^ 17 := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ lam t ^ 17 := Nat.pow_le_pow_left (two_pow_p_le ht) _

/-! ## `m` -/

/-- `t ≤ ⌈t / 2^T⌉ 2^T`. -/
theorem le_ceilDiv_mul (x d : ℕ) (hd : 0 < d) : x ≤ (x + d - 1) / d * d := by
  have h1 := Nat.div_add_mod (x + d - 1) d
  have h2 := Nat.mod_lt (x + d - 1) hd
  generalize (x + d - 1) / d = q at *
  generalize (x + d - 1) % d = r at *
  rw [mul_comm] at h1
  omega

theorem ceilDiv_mul_le (x d : ℕ) : (x + d - 1) / d * d ≤ x + d - 1 := Nat.div_mul_le_self _ _

/-- `m 2^T ≥ (p+1)^6 t`: `m ≥ t λ^{-s} (log λ)^6`. -/
theorem m_mul_two_pow_T_ge (t : ℕ) : (p t + 1) ^ 6 * t ≤ m K t * 2 ^ T K t := by
  unfold m
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (le_ceilDiv_mul t _ (by positivity))

/-- `m 2^T ≤ (p+1)^6 (t + 2^T)`: `m ≤ 2^9 t λ^{-s} (log λ)^6` for large `t`. -/
theorem m_mul_two_pow_T_le (t : ℕ) : m K t * 2 ^ T K t ≤ (p t + 1) ^ 6 * (t + 2 ^ T K t) := by
  unfold m
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (le_trans (ceilDiv_mul_le t (2 ^ T K t))
    (Nat.sub_le (t + 2 ^ T K t) 1))

/-! ## Polynomial versus exponential, and `λ, p → ∞` -/

theorem eventually_mul_pow_lt_two_pow (c k : ℕ) : ∀ᶠ n : ℕ in atTop, c * n ^ k < 2 ^ n := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) one_lt_two
  have hc : (0 : ℝ) < 1 / ((c : ℝ) + 1) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h3 : ((n : ℝ) ^ k) < 1 / ((c : ℝ) + 1) * 2 ^ n := by
    rwa [div_lt_iff₀ h2] at hn
  have h4 : ((c : ℝ) + 1) * (n : ℝ) ^ k < 2 ^ n := by
    have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
    calc ((c : ℝ) + 1) * (n : ℝ) ^ k < ((c : ℝ) + 1) * (1 / ((c : ℝ) + 1) * 2 ^ n) :=
          mul_lt_mul_of_pos_left h3 hc1
      _ = 2 ^ n := by field_simp
  have h5 : (c : ℝ) * (n : ℝ) ^ k < 2 ^ n := by
    have : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
    nlinarith
  exact_mod_cast h5

theorem tendsto_lam : Tendsto lam atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro q
  refine ⟨2 ^ q, fun t ht => ?_⟩
  calc q = Nat.clog 2 (2 ^ q) := (Nat.clog_pow 2 q one_lt_two).symm
    _ ≤ Nat.clog 2 t := Nat.clog_mono_right 2 ht

theorem tendsto_log2 : Tendsto (Nat.log 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro q
  refine ⟨2 ^ q, fun t ht => ?_⟩
  calc q = Nat.log 2 (2 ^ q) := (Nat.log_pow one_lt_two q).symm
    _ ≤ Nat.log 2 t := Nat.log_mono_right ht

theorem tendsto_p : Tendsto p atTop atTop := tendsto_log2.comp tendsto_lam

/-- Transfer of an eventual property of `p` to an eventual property of `t`. -/
theorem eventually_of_p {P : ℕ → Prop} (hP : ∀ᶠ q in atTop, P q) : ∀ᶠ t in atTop, P (p t) :=
  tendsto_p.eventually hP

theorem eventually_of_lam {P : ℕ → Prop} (hP : ∀ᶠ q in atTop, P q) : ∀ᶠ t in atTop, P (lam t) :=
  tendsto_lam.eventually hP

/-! ## Eventual bounds (paper eq:p1, eq:size, eq:zlen, eq:hidden, lem:space, lem:time) -/

theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

theorem two_mul_succ_le_two_pow : ∀ q, 3 ≤ q → 2 * (q + 1) ≤ 2 ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- `T ≥ 1` for large `t`. -/
theorem eventually_T_pos : ∀ᶠ t in atTop, 1 ≤ T K t := by
  filter_upwards [eventually_of_p (eventually_ge_atTop (2 ^ K.j))] with t ht
  unfold T
  exact (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using ht)

/-- `λ^k < t` for large `t`. -/
theorem lam_pow_lt_t (k : ℕ) : ∀ᶠ t in atTop, lam t ^ k < t := by
  filter_upwards [eventually_of_lam (eventually_mul_pow_lt_two_pow 2 k), eventually_ge_atTop 2]
    with t h1 h2
  have h3 := two_pow_lam_lt h2
  have h4 := lt_trans h1 h3
  generalize lam t ^ k = y at *
  omega

theorem bb_pos (t : ℕ) : 0 < bb t := by unfold bb N; exact Nat.mul_pos (B_pos t) (by positivity)

theorem bb_le_pow (t : ℕ) : bb t ≤ 2 ^ (10 * p t) := by
  unfold bb B N h; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem pow_le_two_mul_bb (t : ℕ) : 2 ^ (10 * p t) ≤ 2 * bb t := by
  unfold bb B N h; rw [← pow_add, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bb_le_lam_pow {t : ℕ} (ht : 2 ≤ t) : bb t ≤ lam t ^ 10 :=
  le_trans (bb_le_pow t) (by rw [pow_mul']; exact Nat.pow_le_pow_left (two_pow_p_le ht) 10)

theorem eventually_bb_le_t : ∀ᶠ t in atTop, bb t ≤ t := by
  filter_upwards [lam_pow_lt_t 10, eventually_ge_atTop 2] with t h1 h2
  exact le_trans (bb_le_lam_pow h2) h1.le

/-- (eq:p1) `a t ≤ I b ≤ 4 a t` for large `t`. -/
theorem eventually_Ib (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ t in atTop, a * t ≤ I a t * bb t ∧ I a t * bb t ≤ 4 * a * t := by
  filter_upwards [eventually_bb_le_t, eventually_ge_atTop 2] with t h1 h2
  have e1 := le_ceilDiv_mul (a * 2 ^ lam t) (bb t) (bb_pos t)
  have e2 := ceilDiv_mul_le (a * 2 ^ lam t) (bb t)
  have e3 := t_le_two_pow_lam t
  have e4 := two_pow_lam_lt h2
  have h5 : a * 2 ^ lam t ≤ 2 * (a * t) := by
    calc a * 2 ^ lam t ≤ a * (2 * t) := Nat.mul_le_mul_left _ e4.le
      _ = 2 * (a * t) := by ring
  have h6 : t ≤ a * t := Nat.le_mul_of_pos_left t ha
  have h7 : a * t ≤ a * 2 ^ lam t := Nat.mul_le_mul_left _ e3
  have h8 : 4 * a * t = 4 * (a * t) := by ring
  unfold I
  rw [h8]
  generalize (a * 2 ^ lam t + bb t - 1) / bb t * bb t = q at *
  generalize a * 2 ^ lam t = X at *
  generalize a * t = Y at *
  constructor <;> omega

/-- (4), lem:space for S0-S2: if `B x ≤ C t (p+1)^2` (i.e. `x = O(t (log λ)^2 / λ^{1/2})`) then `x ≤ m/2`. -/
theorem eventually_aux (C : ℕ) :
    ∀ᶠ t in atTop, ∀ x, B t * x ≤ C * t * (p t + 1) ^ 2 → 2 * x ≤ m K t := by
  have hev : ∀ᶠ q in atTop, 2 * C * 2 ^ (q / 64) ≤ 2 ^ (q / 2) := by
    filter_upwards [eventually_ge_atTop (64 * (2 * C))] with q hq
    have h1 : 2 * C ≤ q / 64 := by omega
    have h2 := lt_two_pow' (q / 64)
    calc 2 * C * 2 ^ (q / 64) ≤ 2 ^ (q / 64) * 2 ^ (q / 64) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (q / 64 + q / 64) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (q / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  filter_upwards [eventually_of_p hev] with t ht x hx
  have hT : 2 * C * 2 ^ T K t ≤ B t := le_trans (Nat.mul_le_mul_left _ (two_pow_T_le K t)) ht
  have hm := m_mul_two_pow_T_ge K t
  have hp : (p t + 1) ^ 2 ≤ (p t + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have key : (B t * 2 ^ T K t) * (2 * x) ≤ (B t * 2 ^ T K t) * m K t := by
    calc (B t * 2 ^ T K t) * (2 * x) = 2 * 2 ^ T K t * (B t * x) := by ring
      _ ≤ 2 * 2 ^ T K t * (C * t * (p t + 1) ^ 2) := Nat.mul_le_mul_left _ hx
      _ = (2 * C * 2 ^ T K t) * (t * (p t + 1) ^ 2) := by ring
      _ ≤ B t * (t * (p t + 1) ^ 2) := Nat.mul_le_mul_right _ hT
      _ ≤ B t * (t * (p t + 1) ^ 6) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
      _ = B t * ((p t + 1) ^ 6 * t) := by ring
      _ ≤ B t * (m K t * 2 ^ T K t) := Nat.mul_le_mul_left _ hm
      _ = (B t * 2 ^ T K t) * m K t := by ring
  exact Nat.le_of_mul_le_mul_left key (Nat.mul_pos (B_pos t) (by positivity))

/-- (5), eq:zlen: if `2^T z ≤ C t (p+1)` (i.e. `|z| = O(t λ^{-s} log λ)`) then `|z| ≤ m/2`. -/
theorem eventually_z (C : ℕ) :
    ∀ᶠ t in atTop, ∀ z, 2 ^ T K t * z ≤ C * t * (p t + 1) → 2 * z ≤ m K t := by
  have hev : ∀ᶠ q : ℕ in atTop, 2 * C * (q + 1) ≤ (q + 1) ^ 6 := by
    filter_upwards [eventually_ge_atTop (2 * C)] with q hq
    calc 2 * C * (q + 1) ≤ (q + 1) * (q + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = (q + 1) ^ 2 := by ring
      _ ≤ (q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  filter_upwards [eventually_of_p hev] with t ht z hz
  have hm := m_mul_two_pow_T_ge K t
  have key : 2 ^ T K t * (2 * z) ≤ 2 ^ T K t * m K t := by
    calc 2 ^ T K t * (2 * z) = 2 * (2 ^ T K t * z) := by ring
      _ ≤ 2 * (C * t * (p t + 1)) := Nat.mul_le_mul_left _ hz
      _ = (2 * C * (p t + 1)) * t := by ring
      _ ≤ (p t + 1) ^ 6 * t := Nat.mul_le_mul_right _ ht
      _ ≤ m K t * 2 ^ T K t := hm
      _ = 2 ^ T K t * m K t := by ring
  exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- eq:hidden: the private bits `C (B+1) C2^{2T}` (`= O(λ^{17/32})`) are at most `λ^{3/4}`. -/
theorem eventually_hidden (C : ℕ) :
    ∀ᶠ t in atTop, (C * (B t + 1) * K.C2 ^ (2 * T K t)) ^ 4 ≤ lam t ^ 3 := by
  filter_upwards [eventually_of_lam (eventually_ge_atTop ((2 * C) ^ 32)), eventually_ge_atTop 2]
    with t h1 h2
  have hB := B_C2_pow_le K h2
  have hB1 : B t + 1 ≤ 2 * B t := by have := B_pos t; omega
  have e : (C * (B t + 1) * K.C2 ^ (2 * T K t)) ^ 32 ≤ (lam t ^ 3) ^ 8 := by
    calc (C * (B t + 1) * K.C2 ^ (2 * T K t)) ^ 32
          ≤ (2 * C * (B t * K.C2 ^ (2 * T K t))) ^ 32 := by
          apply Nat.pow_le_pow_left
          calc C * (B t + 1) * K.C2 ^ (2 * T K t) ≤ C * (2 * B t) * K.C2 ^ (2 * T K t) := by gcongr
            _ = 2 * C * (B t * K.C2 ^ (2 * T K t)) := by ring
      _ = (2 * C) ^ 32 * (B t * K.C2 ^ (2 * T K t)) ^ 32 := mul_pow _ _ _
      _ ≤ lam t ^ 7 * lam t ^ 17 := by
          apply Nat.mul_le_mul _ hB
          calc (2 * C) ^ 32 ≤ lam t := h1
            _ ≤ lam t ^ 7 := Nat.le_self_pow (by norm_num) _
      _ = (lam t ^ 3) ^ 8 := by ring
  have e2 : ((C * (B t + 1) * K.C2 ^ (2 * T K t)) ^ 4) ^ 8 ≤ (lam t ^ 3) ^ 8 := by
    rw [← pow_mul]; exact e
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 e2

/-- lem:time, private enumeration: `2^{C x} ≤ m` whenever `x ≤ λ^{3/4}` (so `2^{O(λ^{3/4})} = t^{o(1)} ≤ m`). -/
theorem eventually_enum (C : ℕ) :
    ∀ᶠ t in atTop, ∀ x, x ^ 4 ≤ lam t ^ 3 → 2 ^ (C * x) ≤ m K t := by
  filter_upwards [eventually_of_lam (eventually_ge_atTop (16 * C ^ 4)),
    eventually_of_p (eventually_ge_atTop 3), eventually_ge_atTop 2] with t h1 h3 h2 x hx
  have e1 : (2 * (C * x)) ^ 4 ≤ lam t ^ 4 := by
    calc (2 * (C * x)) ^ 4 = 16 * C ^ 4 * x ^ 4 := by ring
      _ ≤ lam t * lam t ^ 3 := Nat.mul_le_mul h1 hx
      _ = lam t ^ 4 := by ring
  have e2 : 2 * (C * x) ≤ lam t := (Nat.pow_le_pow_iff_left (by norm_num)).1 e1
  have e3 := two_mul_succ_le_two_pow (p t) h3
  have e4 := two_pow_p_le h2
  have e5 := T_le_p K t
  have e6 : C * x + T K t + 1 ≤ lam t := by
    generalize C * x = y at *
    generalize 2 ^ p t = P at *
    omega
  have e7 : 2 ^ (C * x) * 2 ^ T K t * 2 ≤ 2 ^ lam t := by
    rw [← pow_add, ← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) e6
  have e8 := two_pow_lam_lt h2
  have e9 := le_ceilDiv_mul t (2 ^ T K t) (by positivity)
  have e10 : 2 ^ (C * x) * 2 ^ T K t < ((t + 2 ^ T K t - 1) / 2 ^ T K t) * 2 ^ T K t := by
    generalize 2 ^ (C * x) * 2 ^ T K t = A at *
    generalize ((t + 2 ^ T K t - 1) / 2 ^ T K t) * 2 ^ T K t = Q at *
    generalize 2 ^ lam t = L at *
    omega
  have e11 : 2 ^ (C * x) < (t + 2 ^ T K t - 1) / 2 ^ T K t := Nat.lt_of_mul_lt_mul_right e10
  have e12 : (t + 2 ^ T K t - 1) / 2 ^ T K t ≤ m K t := by
    unfold m; exact Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- `t ≤ m^2` for large `t`; with `n^2 ≤ t` this gives `n ≤ m`. -/
theorem eventually_t_le_m_sq : ∀ᶠ t in atTop, t ≤ m K t ^ 2 := by
  filter_upwards [lam_pow_lt_t 2, eventually_ge_atTop 2] with t h1 h2
  have e1 := le_ceilDiv_mul t (2 ^ T K t) (by positivity)
  have e2 : 2 ^ T K t ≤ lam t :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (T_le_p K t)) (two_pow_p_le h2)
  have e3 : (t + 2 ^ T K t - 1) / 2 ^ T K t ≤ m K t := by
    unfold m; exact Nat.le_mul_of_pos_left _ (by positivity)
  generalize (t + 2 ^ T K t - 1) / 2 ^ T K t = D at *
  have e4 : t ≤ D * lam t := le_trans e1 (Nat.mul_le_mul_left _ e2)
  have e5 : t * t ≤ D ^ 2 * lam t ^ 2 := by
    calc t * t ≤ (D * lam t) * (D * lam t) := Nat.mul_le_mul e4 e4
      _ = D ^ 2 * lam t ^ 2 := by ring
  have e6 : D ^ 2 * lam t ^ 2 ≤ D ^ 2 * t := Nat.mul_le_mul_left _ h1.le
  have e7 : t ≤ D ^ 2 := by
    have : t * t ≤ D ^ 2 * t := le_trans e5 e6
    exact Nat.le_of_mul_le_mul_right this (by omega)
  exact le_trans e7 (Nat.pow_le_pow_left e3 2)

/-- `I λ^2 ≤ m` for large `t` (the directory scans of lem:time). -/
theorem eventually_I_lam_sq_le (a : ℕ) (ha : 1 ≤ a) : ∀ᶠ t in atTop, I a t * lam t ^ 2 ≤ m K t := by
  have hev : ∀ᶠ q : ℕ in atTop, a * 2 ^ (3 * q + 5) ≤ 2 ^ (10 * q) := by
    filter_upwards [eventually_ge_atTop (a + 5)] with q hq
    have := lt_two_pow' q
    calc a * 2 ^ (3 * q + 5) ≤ 2 ^ q * 2 ^ (3 * q + 5) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (4 * q + 5) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (10 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  filter_upwards [eventually_of_p hev, eventually_Ib a ha, eventually_ge_atTop 2] with t h1 h2 h4
  have hb := pow_le_two_mul_bb t
  have e1 : a * 2 ^ (3 * p t + 4) ≤ bb t := by
    have : 2 * (a * 2 ^ (3 * p t + 4)) = a * 2 ^ (3 * p t + 5) := by ring
    generalize a * 2 ^ (3 * p t + 4) = X at *
    generalize a * 2 ^ (3 * p t + 5) = Y at *
    generalize 2 ^ (10 * p t) = Z at *
    omega
  have e2 : lam t ^ 2 * 2 ^ T K t ≤ 2 ^ (3 * p t + 2) := by
    calc lam t ^ 2 * 2 ^ T K t ≤ (2 ^ (p t + 1)) ^ 2 * 2 ^ p t :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (lam_lt_two_pow_p t).le 2)
            (Nat.pow_le_pow_right (by norm_num) (T_le_p K t))
      _ = 2 ^ (3 * p t + 2) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hm := m_mul_two_pow_T_ge K t
  have hp : 1 ≤ (p t + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have key : (I a t * lam t ^ 2) * (bb t * 2 ^ T K t) ≤ m K t * (bb t * 2 ^ T K t) := by
    calc (I a t * lam t ^ 2) * (bb t * 2 ^ T K t) = (I a t * bb t) * (lam t ^ 2 * 2 ^ T K t) := by ring
      _ ≤ (4 * a * t) * 2 ^ (3 * p t + 2) := Nat.mul_le_mul h2.2 e2
      _ = t * (a * 2 ^ (3 * p t + 4)) := by ring
      _ ≤ t * bb t := Nat.mul_le_mul_left _ e1
      _ ≤ ((p t + 1) ^ 6 * t) * bb t := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hp)
      _ ≤ (m K t * 2 ^ T K t) * bb t := Nat.mul_le_mul_right _ hm
      _ = m K t * (bb t * 2 ^ T K t) := by ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos (bb_pos t) (by positivity))

/-! ## In terms of the input length: `t = a (n^2 + 1)` -/

/-- `t(n) = a (n^2+1)`, the time bound of `LemmaP` (PLAN.md sec. 3). -/
def tOf (a n : ℕ) : ℕ := a * (n ^ 2 + 1)

theorem tendsto_tOf {a : ℕ} (ha : 1 ≤ a) : Tendsto (tOf a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun n hn => ?_⟩
  unfold tOf
  have : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  calc b ≤ n ^ 2 + 1 := by omega
    _ ≤ a * (n ^ 2 + 1) := Nat.le_mul_of_pos_left _ ha

theorem eventually_n {a : ℕ} (ha : 1 ≤ a) {P : ℕ → Prop} (hP : ∀ᶠ t in atTop, P t) :
    ∀ᶠ n in atTop, P (tOf a n) := (tendsto_tOf ha).eventually hP

/-- `n ≤ m` for large `n`. -/
theorem eventually_n_le_m {a : ℕ} (ha : 1 ≤ a) : ∀ᶠ n in atTop, n ≤ m K (tOf a n) := by
  filter_upwards [eventually_n ha (eventually_t_le_m_sq K)] with n hn
  have h1 : n ^ 2 ≤ tOf a n := by
    unfold tOf
    calc n ^ 2 ≤ n ^ 2 + 1 := Nat.le_succ _
      _ ≤ a * (n ^ 2 + 1) := Nat.le_mul_of_pos_left _ ha
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (le_trans h1 hn)

/-- lem:time (branch time). For the time bound `t = a(n^2+1)` and any constant `C`, for large `n`, every
private enumeration of `x ≤ λ^{3/4}` bits gives
`(T+1)(m+n) + I λ^2 + 2^{C x} ≤ 4 m (p+1)`, i.e. the selector time `O(m log λ)` of Lemma P. -/
theorem eventually_branch_time {a : ℕ} (ha : 1 ≤ a) (C : ℕ) :
    ∀ᶠ n in atTop, ∀ x, x ^ 4 ≤ lam (tOf a n) ^ 3 →
      (T K (tOf a n) + 1) * (m K (tOf a n) + n) + I a (tOf a n) * lam (tOf a n) ^ 2 + 2 ^ (C * x)
        ≤ 4 * m K (tOf a n) * (p (tOf a n) + 1) := by
  filter_upwards [eventually_n_le_m K ha, eventually_n ha (eventually_I_lam_sq_le K a ha),
    eventually_n ha (eventually_enum K C)] with n h1 h2 h3 x hx
  have h4 := h3 x hx
  have h5 := T_le_p K (tOf a n)
  generalize m K (tOf a n) = M at *
  generalize p (tOf a n) = P at *
  generalize T K (tOf a n) = TT at *
  have h6 : (TT + 1) * (M + n) ≤ (P + 1) * (2 * M) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h7 : M ≤ M * (P + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h8 : 4 * M * (P + 1) = (P + 1) * (2 * M) + M * (P + 1) + M * (P + 1) := by ring
  rw [h8]
  generalize I a (tOf a n) * lam (tOf a n) ^ 2 = Y at *
  generalize 2 ^ (C * x) = Z at *
  generalize (TT + 1) * (M + n) = U at *
  generalize (P + 1) * (2 * M) = V at *
  generalize M * (P + 1) = W at *
  omega

end Params
end P1Wrap
