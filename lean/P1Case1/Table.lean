import P1Case1.Main
import OAI.Computability.MultitapeWeakETH.Padding
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# P1, Case 1, tasks G3 + G4: the TRANS table bound from `PriceOver K` and one entropy lemma

`TransEntropyBound K` (the paper's lem:entropy, specialised to the transpose display; open piece A') is
the inequality that OpenAI's `paired_entropy_external_root` gives for a network that displays `xᵀ` with
the rows of `x` pinned at the input terminals. Proved here:
`transFieldTableBound_of_entropy : PriceOver K → TransEntropyBound K → TransFieldTableBound K`,
from the patched `graph_geometry` (any field) and arithmetic.
-/

namespace P1Case1

open OAI.Computability.MultitapeWeakETH (Word Network PriceOver PriceTwo graph_geometry
  normalizedDist)
open Finset

open scoped Classical in
/-- **Open piece A' (paper lem:entropy for TRANS).** For every network with field tables, every spectral
placement and every scale `a ≥ 0`: with `S` the set of inputs whose contraction is a nonzero multiple of
`e_{xᵀ}`, there are pin charges `h` (entropy in bits of the row pinned at `v`, at most `N`, total at most
`N²`) such that
`log₂ |S| − Σ_{i,j} |a d(input i, output j) − 1| ≤ Σ_e width_e · a d(e) + Σ_v h_v · a d(v, root)`. -/
def TransEntropyBound (K : Type) [Field K] : Prop :=
  ∀ (N : ℕ) (G : Network (N * N) N) (tables : (v : Fin G.vertices) → G.View v → K)
    {X : Type} [PseudoMetricSpace X], OAI.Computability.VPVNP.WireGeometry.RealizableConfigurations K X →
    ∀ (p : Fin G.vertices → X) (root : X) (a : ℝ), 0 ≤ a →
      ∃ h : Fin G.vertices → ℝ, (∀ v, 0 ≤ h v ∧ h v ≤ N) ∧ (∑ v, h v) ≤ N * N ∧
        Real.logb 2 ((univ.filter (TransFieldGood G tables)).card : ℝ) -
            ∑ j, ∑ i, |a * dist (p (G.input i)) (p (G.output j)) - 1| ≤
          ∑ e, (G.width e : ℝ) * (a * dist (p (G.src e)) (p (G.dst e))) +
            ∑ v, h v * (a * dist (p v) root)

/-! ## Arithmetic helpers -/

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- If `P < c N √(log₂ N)`, `3 ≤ N ≤ P`, then `P² / ln P ≤ 2 c² N²`. -/
theorem sq_div_log_le {N P : ℕ} {c : ℝ} (hc : 0 ≤ c) (hN : 3 ≤ N) (hNP : N ≤ P)
    (hP : (P : ℝ) < c * (N * Real.sqrt (Real.logb 2 N))) :
    (P : ℝ) ^ 2 / Real.log P ≤ 2 * c ^ 2 * (N : ℝ) ^ 2 := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNP' : (N : ℝ) ≤ P := by exact_mod_cast hNP
  have hlogN : 1 ≤ Real.log N :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) hN3)
  have hlogP : Real.log N ≤ Real.log P := Real.log_le_log (by linarith) hNP'
  have hl2 := Real.log_two_gt_d9
  have hlb : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by linarith)
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hsq : (P : ℝ) ^ 2 ≤ c ^ 2 * (N : ℝ) ^ 2 * Real.logb 2 N := by
    have h1 : (P : ℝ) ^ 2 ≤ (c * (N * Real.sqrt (Real.logb 2 N))) ^ 2 :=
      pow_le_pow_left₀ hP0 hP.le 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hlb] at h1
    linarith
  have hlb2 : Real.logb 2 N ≤ 2 * Real.log N := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < Real.log P := by linarith
  rw [div_le_iff₀ hpos]
  have h3 : c ^ 2 * (N : ℝ) ^ 2 * Real.logb 2 N ≤ c ^ 2 * (N : ℝ) ^ 2 * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hlb2 (by positivity)
  have h4 : 2 * c ^ 2 * (N : ℝ) ^ 2 * Real.log N ≤ 2 * c ^ 2 * (N : ℝ) ^ 2 * Real.log P :=
    mul_le_mul_of_nonneg_left hlogP (by positivity)
  nlinarith

theorem abs_le_sq_add (y : ℝ) : |y| ≤ 5 * y ^ 2 + 1 / 20 := by
  nlinarith [sq_nonneg (|y| - 1/10), sq_abs y, abs_nonneg y]

theorem sqrt_le_of_sq {A B : ℝ} (hB : 0 ≤ B) (h : A ≤ B ^ 2) : Real.sqrt A ≤ B := by
  calc Real.sqrt A ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB

theorem ceilDiv_self_mul (N : ℕ) (hN : 0 < N) : N * N ⌈/⌉ N = N := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have : N * N + N - 1 = N * N + (N - 1) := by omega
  rw [this, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega)]
  simp

/-! ## The table bound -/

theorem transFieldTableBound_of_entropy {K : Type} [Field K] (price : PriceOver K)
    (ent : TransEntropyBound K) : TransFieldTableBound K := by
  classical
  intro D
  obtain ⟨Kc, hKc, n₀, geom⟩ := graph_geometry price D
  set u : ℝ := 1 + Kc with hu
  set w : ℝ := 1 + D with hw
  have hu1 : 1 ≤ u := by linarith
  have hw1 : 1 ≤ w := by have : (0 : ℝ) ≤ D := Nat.cast_nonneg D; linarith
  set c : ℝ := 1 / (400 * u * w ^ 2) with hc_def
  have hc0 : 0 < c := by positivity
  -- the three smallness conditions on c
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw1
  have huw : u ≤ u * w ^ 2 := le_mul_of_one_le_right (by linarith) hw2
  have cuw : u * w ^ 2 * c = 1 / 400 := by
    rw [hc_def]; field_simp
  have hKc_c : Kc * c ≤ 1 / 400 := by
    have : Kc * c ≤ u * w ^ 2 * c := mul_le_mul_of_nonneg_right (by linarith) hc0.le
    linarith
  have hc400 : c ≤ 1 / 400 := by
    have : c ≤ u * w ^ 2 * c := le_mul_of_one_le_left hc0.le (by linarith)
    linarith
  have hKc0 : 0 ≤ Kc * c := by positivity
  have hcc : Kc * c * c ≤ 1 / 400 * (1 / 400) := mul_le_mul hKc_c hc400 hc0.le (by norm_num)
  have small1 : 120 * Kc * (2 * c ^ 2) ≤ 1 / 20 := by nlinarith
  have small2 : 2 * Kc * c ^ 2 ≤ (1 / 20) ^ 2 := by nlinarith
  have small3 : (D : ℝ) ^ 2 * (D * Kc * (2 * c ^ 2)) ≤ (1 / 20) ^ 2 := by
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hDw : (D : ℝ) ≤ w := by linarith
    have hKu : Kc ≤ u := by linarith
    -- D^3 Kc c^2 ≤ (w^2 u c) (w c) = (1/400) (w c) ≤ (1/400)^2
    have hwc : w * c ≤ 1 / 400 := by
      have : w * c ≤ u * w ^ 2 * c := by
        apply mul_le_mul_of_nonneg_right _ hc0.le
        nlinarith
      linarith
    have hD3 : (D : ℝ) ^ 3 * Kc ≤ w ^ 3 * u :=
      mul_le_mul (pow_le_pow_left₀ hD0 hDw 3) hKu hKc.le (by positivity)
    have h4 : (D : ℝ) ^ 3 * Kc * c ^ 2 ≤ w ^ 3 * u * c ^ 2 :=
      mul_le_mul_of_nonneg_right hD3 (sq_nonneg c)
    have h5 : w ^ 3 * u * c ^ 2 = (u * w ^ 2 * c) * (w * c) := by ring
    rw [h5, cuw] at h4
    have h6 : (1 / 400 : ℝ) * (w * c) ≤ 1 / 400 * (1 / 400) :=
      mul_le_mul_of_nonneg_left hwc (by norm_num)
    have h7 : (D : ℝ) ^ 2 * (D * Kc * (2 * c ^ 2)) = 2 * ((D : ℝ) ^ 3 * Kc * c ^ 2) := by ring
    rw [h7]
    linarith
  refine ⟨c, hc0, max 3 n₀, ?_⟩
  intro N hN G bounded tables densityBound
  have hN3 : 3 ≤ N := le_of_max_le_left hN
  have hNn : n₀ ≤ N := le_of_max_le_right hN
  set P := G.vertices with hP_def
  have hNpos : 0 < N := by omega
  have hNP : N ≤ P := by
    have h := Fintype.card_le_of_embedding G.input
    simp only [Fintype.card_fin, ceilDiv_self_mul N hNpos] at h
    exact h
  by_contra hcon
  have hlt : (P : ℝ) < c * (N * Real.sqrt (Real.logb 2 N)) := by
    simpa [scale, hP_def] using lt_of_not_ge hcon
  have hB1 := sq_div_log_le hc0.le hN3 hNP hlt
  have degree : ∀ v, (univ.filter fun t => G.src t = v).card +
      (univ.filter fun t => G.dst t = v).card ≤ D := fun v => bounded.1 v
  obtain ⟨X, p, o, a, ha, edges, terminals, center⟩ := geom P (le_trans hNn hNP) G.src G.dst degree
  obtain ⟨h, hh, hsum, main⟩ := ent N G tables X.realizable p o a ha.le
  -- real facts
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNP' : (N : ℝ) ≤ P := by exact_mod_cast hNP
  have hlogP : 1 ≤ Real.log P :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hP0 : (0 : ℝ) < P := by linarith
  have hPl : (P : ℝ) / Real.log P ≤ 2 * c ^ 2 * N := by
    have h1 : (P : ℝ) / Real.log P * N ≤ (P : ℝ) ^ 2 / Real.log P := by
      rw [div_mul_eq_mul_div, pow_two]
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hNP' hP0.le
    have h3 : (P : ℝ) / Real.log P * N ≤ (2 * c ^ 2 * N) * N := by
      have := h1.trans hB1; nlinarith
    exact le_of_mul_le_mul_right h3 (by linarith)
  -- (1) log₂ |S| ≥ 99/100 N²
  have hlogS : (99 / 100 : ℝ) * (N * N) ≤
      Real.logb 2 ((univ.filter (TransFieldGood G tables)).card : ℝ) := by
    have hcard : (Fintype.card (Word (N * N)) : ℝ) = 2 ^ (N * N) := by simp
    have hd := densityBound
    unfold wordDensity at hd
    rw [hcard] at hd
    have h2pos : (0 : ℝ) < 2 ^ (N * N) := by positivity
    have hS : (2 : ℝ) ^ (-(1/100 : ℝ) * (N * N)) * 2 ^ (N * N) ≤
        ((univ.filter (TransFieldGood G tables)).card : ℝ) := by
      rwa [le_div_iff₀ h2pos] at hd
    have hS' : (2 : ℝ) ^ ((99/100 : ℝ) * (N * N)) ≤
        ((univ.filter (TransFieldGood G tables)).card : ℝ) := by
      convert hS using 1
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity) hS'
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  -- (2) the terminal term
  have hterm : ∑ j, ∑ i, |a * dist (p (G.input i)) (p (G.output j)) - 1| ≤
      (1/20 : ℝ) * (N * N) + 5 * (12 * N * (Kc * P / Real.log P)) := by
    have ht := terminals (N * N ⌈/⌉ N) G.input G.output
    simp only [normalizedDist] at ht
    have hpt : ∀ j i, |a * dist (p (G.input i)) (p (G.output j)) - 1| ≤
        5 * (a * dist (p (G.input i)) (p (G.output j)) - 1) ^ 2 + 1/20 :=
      fun j i => abs_le_sq_add _
    calc ∑ j, ∑ i, |a * dist (p (G.input i)) (p (G.output j)) - 1|
        ≤ ∑ j : Fin (N * N ⌈/⌉ N), ∑ i : Fin (N * N ⌈/⌉ N),
            (5 * (a * dist (p (G.input i)) (p (G.output j)) - 1) ^ 2 + 1/20) :=
          sum_le_sum fun j _ => sum_le_sum fun i _ => hpt j i
      _ = 5 * (∑ j, ∑ i, (a * dist (p (G.input i)) (p (G.output j)) - 1) ^ 2) +
            (1/20) * ((N * N ⌈/⌉ N : ℕ) * (N * N ⌈/⌉ N : ℕ) : ℝ) := by
          simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_sum]
          ring
      _ ≤ _ := by
          have hcast : ((N * N ⌈/⌉ N : ℕ) : ℝ) = N := by rw [ceilDiv_self_mul N hNpos]
          rw [hcast] at ht ⊢
          linarith
  -- (3) the edge term
  have hedge : ∑ e, (G.width e : ℝ) * (a * dist (p (G.src e)) (p (G.dst e))) ≤
      (1/20 : ℝ) * (N * N) := by
    have he := edges (fun e => (G.width e : ℝ)) ((D * N : ℕ) : ℝ) (Nat.cast_nonneg _)
      (fun e => by exact_mod_cast bounded.2 e)
    simp only [normalizedDist] at he
    refine he.trans ?_
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    have hin : (D : ℝ) * P * (Kc * P / Real.log P) = D * Kc * ((P : ℝ) ^ 2 / Real.log P) := by
      ring
    rw [hin]
    have hDN : (0 : ℝ) ≤ ((D * N : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [show ((D * N : ℕ) : ℝ) = Real.sqrt (((D * N : ℕ) : ℝ) ^ 2) from (Real.sqrt_sq hDN).symm,
      ← Real.sqrt_mul (by positivity)]
    apply sqrt_le_of_sq (by positivity)
    have hX : (D : ℝ) * Kc * ((P : ℝ) ^ 2 / Real.log P) ≤ D * Kc * (2 * c ^ 2 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hB1 (by positivity)
    calc ((D * N : ℕ) : ℝ) ^ 2 * ((D : ℝ) * Kc * ((P : ℝ) ^ 2 / Real.log P))
        ≤ ((D * N : ℕ) : ℝ) ^ 2 * (D * Kc * (2 * c ^ 2 * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hX (sq_nonneg _)
      _ = ((D : ℝ) ^ 2 * (D * Kc * (2 * c ^ 2))) * ((N : ℝ) * N) ^ 2 := by push_cast; ring
      _ ≤ (1 / 20) ^ 2 * ((N : ℝ) * N) ^ 2 := mul_le_mul_of_nonneg_right small3 (by positivity)
      _ = _ := by ring
  -- (4) the center term
  have hcen : ∑ v, h v * (a * dist (p v) o) ≤ (N * N : ℝ) / Real.sqrt 2 + (1/20 : ℝ) * (N * N) := by
    have hc := center h (fun v => (hh v).1)
    refine hc.trans ?_
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : (∑ v, h v) / Real.sqrt 2 ≤ (N * N : ℝ) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right hsum hs2
    have hsq : ∑ v, h v ^ 2 ≤ N * (N * N) := by
      calc ∑ v, h v ^ 2 ≤ ∑ v, (N : ℝ) * h v :=
            sum_le_sum fun v _ => by
              rw [pow_two]; exact mul_le_mul_of_nonneg_right (hh v).2 (hh v).1
        _ = N * ∑ v, h v := by rw [mul_sum]
        _ ≤ N * (N * N) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    have h2 : Real.sqrt (∑ v, h v ^ 2) * Real.sqrt (Kc * P / Real.log P) ≤ (1/20) * (N * N) := by
      rw [← Real.sqrt_mul (sum_nonneg fun v _ => sq_nonneg _)]
      apply sqrt_le_of_sq (by positivity)
      have hK0 : 0 ≤ Kc * P / Real.log P := by positivity
      calc (∑ v, h v ^ 2) * (Kc * P / Real.log P) ≤ (N * (N * N)) * (Kc * P / Real.log P) :=
            mul_le_mul_of_nonneg_right hsq hK0
        _ = (N * (N * N)) * Kc * ((P : ℝ) / Real.log P) := by ring
        _ ≤ (N * (N * N)) * Kc * (2 * c ^ 2 * N) :=
            mul_le_mul_of_nonneg_left hPl (by positivity)
        _ = (2 * Kc * c ^ 2) * (N * N) ^ 2 := by ring
        _ ≤ (1/20) ^ 2 * (N * N) ^ 2 := mul_le_mul_of_nonneg_right small2 (by positivity)
        _ = _ := by ring
    linarith
  -- (5) contradiction: 99/100 - 1/20 - 5·12·... > 1/20 + 1/√2 + 1/20
  have hterm' : 5 * (12 * N * (Kc * P / Real.log P)) ≤ (1/20 : ℝ) * (N * N) := by
    have : 5 * (12 * N * (Kc * P / Real.log P)) = 60 * Kc * N * ((P : ℝ) / Real.log P) := by ring
    rw [this]
    have h1 : 60 * Kc * N * ((P : ℝ) / Real.log P) ≤ 60 * Kc * N * (2 * c ^ 2 * N) :=
      mul_le_mul_of_nonneg_left hPl (by positivity)
    have h2 : 60 * Kc * N * (2 * c ^ 2 * N) = (120 * Kc * (2 * c ^ 2)) * (N * N) / 2 := by ring
    have h3 : (120 * Kc * (2 * c ^ 2)) * (N * N) ≤ 1 / 20 * (N * N) :=
      mul_le_mul_of_nonneg_right small1 (by positivity)
    have h4 : (0 : ℝ) ≤ N * N := by positivity
    linarith
  have hs2 : (141 / 100 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hNN : (0 : ℝ) < N * N := by positivity
  have hdiv : (N * N : ℝ) / Real.sqrt 2 ≤ 71 / 100 * (N * N) := by
    rw [div_le_iff₀ (by linarith)]
    have : (71 / 100 : ℝ) * (N * N) * (141 / 100) ≤ 71 / 100 * (N * N) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    linarith
  linarith

/-- **Case 1, milestone 4, any infinite field.** -/
theorem c1_of_price_over_of_entropy (k : Type) [Field k] [Infinite k] (ent : TransEntropyBound k)
    (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceOver k) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_price_over_of_table k (fun pr => transFieldTableBound_of_entropy pr ent) upper price

/-- **Case 1, milestone 4, characteristic two.** Open inputs: the entropy lemma over the algebraic
closure of `ZMod 2` (no ports are used in it) and the NTIME upper bound of coTRANS. -/
theorem c1_of_priceTwo_of_entropy (ent : TransEntropyBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog coTRANS) (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_price_over_of_entropy _ ent upper price

end P1Case1
