import P1Case1.Entropy

namespace P1C1U.AstraC1U

open P1Case1
open OAI.Computability.MultitapeWeakETH (Word Network Machine timely initial frozenRun PriceTwo)
open OAI.Computability.MultitapeWeakETH.PhysicalBlocks

/-- Some seed displays the transpose of each input. Every accepting seed that displays a word
on that input displays its transpose. The seed may make arbitrary local choices throughout. -/
def Displays (M : Machine) (N T : ℕ) : Prop :=
  ∀ x : Word (N * N),
    (∃ seed : Fin (T + 1) → M.Choice, timely M T seed x (fun _ => false) (transposeWord x)) ∧
    ∀ (seed : Fin (T + 1) → M.Choice) (out : Word (N * N)),
      timely M T seed x (fun _ => false) out → out = transposeWord x

noncomputable section

local instance (M : Machine) : Fintype M.Tapes := @Fintype.ofFinite _ M.tapesFinite

/-- The trace extraction in P1Case1.TraceGlue applied directly to a machine with choices. -/
theorem trace_of_displays (M' : Machine) (a : ℕ) :
    ∃ D A : ℕ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ T : ℕ,
      Displays M' N (T + a * (N * N + 1)) →
      ∃ G : Network (N * N) N, G.Bounded D ∧
        (G.vertices : ℝ) * N ≤ A * ((N : ℝ) + T + N * N) ∧
        ∃ tables : G.Relation,
          (2 : ℝ) ^ (-(A : ℝ) * (1 + N + (T : ℝ) / N)) ≤ wordDensity (TransGood G tables) := by
  let heads := Fintype.card M'.Tapes
  let A := (3 + 2 * heads) * (1 + 2 * a)
  have hA : 0 < A := by positivity
  refine ⟨degreeFactor M', A, hA, 1, fun N hN T hdec => ?_⟩
  have hb : 0 < N := hN
  let T' := T + a * (N * N + 1)
  let y0 : Word (N * N) := fun _ => false
  have ex : ∀ x : Word (N * N), ∃ s : Fin (T' + 1) → M'.Choice,
      timely M' T' s x y0 (transposeWord x) := fun x => (hdec x).1
  choose seed hseed using ex
  let record (x : Word (N * N)) := traceOf M' hb T' (extendSeed (seed x)) (initial M' x y0)
  obtain ⟨code, keep⟩ := wordDensity_fiber record
  let start i := ((initial M' (n := N * N) (fun _ => false) (fun _ => false)).tape i).pos
  let base := bases M' start code
  let G := traceNetwork M' (N * N) N T' base
  obtain ⟨tables, sem⟩ := exists_trace_tables (M := M') (n := N * N) hb T' base (fun _ _ => True)
  have good : ∀ x, record x = code → TransGood G (tables y0) x := by
    intro x follows
    let s := seed x
    have hs : (fun i => ((initial M' x y0).tape i).pos) = start :=
      funext ((initial_controller M' x y0 (fun _ => false) (fun _ => false)).2)
    have fits : Follows N T' base (extendSeed s) (initial M' x y0) := by
      intro j hj
      have facts := traceOf_fits M' hb T' (extendSeed s) (initial M' x y0) hj
      change traceOf M' hb T' (extendSeed s) (initial M' x y0) = code at follows
      rwa [hs, follows] at facts
    obtain ⟨accept, write⟩ := (timely_path' s x y0 (transposeWord x)).mp (hseed x)
    refine ⟨(sem x y0 _).mpr (history_of_path hb base (fun _ _ => True) x y0 _ (extendSeed s)
      (fun _ => trivial) fits accept write), fun other hother => ?_⟩
    have initFits := fits 0 (Nat.zero_le _)
    simp only [RunAt, cut, Nat.zero_mul, Nat.zero_min, frozenRun] at initFits
    obtain ⟨f, _, ha, hw⟩ := path_of_history hb base (fun _ _ => True)
      ⟨extendSeed s, fun _ => trivial⟩ x y0 other initFits ((sem x y0 other).mp hother)
    obtain ⟨r, hr⟩ := seed_of_path' f ha hw
    exact (hdec x).2 r other hr
  refine ⟨G, traceNetwork_bounded .., ?_, tables y0, ?_⟩
  ·
    have size : G.vertices * N ≤ 3 * (N + T' + N * N) := traceNetwork_size M' (N * N) N T' base
    have sizeR : (G.vertices : ℝ) * N ≤ 3 * ((N : ℝ) + (T + a * (N * N + 1)) + N * N) := by
      exact_mod_cast size
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have hh0 : (0 : ℝ) ≤ heads := Nat.cast_nonneg heads
    have hAR : (A : ℝ) = (3 + 2 * heads) * (1 + 2 * a) := by simp [A]
    rw [hAR]
    have hNN : (1:ℝ) ≤ N * N := by nlinarith
    have h1 : (a : ℝ) * (N * N + 1) ≤ 2 * a * (N * N) := by
      nlinarith [mul_le_mul_of_nonneg_left hNN ha0]
    have h2 : 3 * ((N : ℝ) + (T + a * (N * N + 1)) + N * N) ≤
        3 * (1 + 2 * a) * ((N : ℝ) + T + N * N) := by nlinarith
    have h3 : 3 * (1 + 2 * (a : ℝ)) * ((N : ℝ) + T + N * N) ≤
        (3 + 2 * heads) * (1 + 2 * a) * ((N : ℝ) + T + N * N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    linarith
  ·
    have one := keep (TransGood G (tables y0)) good
    have loss := trace_loss' hb heads T' (2 * heads) le_rfl
    set E := heads * epochs T' N with hE
    set L : ℝ := ((2 * heads : ℕ) : ℝ) * (1 + (T' : ℝ) / N) with hL
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ E := by positivity
    have hd : ((3 : ℝ) ^ E)⁻¹ ≤ wordDensity (TransGood G (tables y0)) := by
      rw [inv_le_iff_one_le_mul₀ h3pos, mul_comm]; exact one
    have h2L : (2 : ℝ) ^ (-L) ≤ ((3 : ℝ) ^ E)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
      exact inv_anti₀ h3pos loss
    have hexp : -(A : ℝ) * (1 + N + (T : ℝ) / N) ≤ -L := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      have hh0 : (0 : ℝ) ≤ heads := Nat.cast_nonneg heads
      have hT' : (T' : ℝ) / N ≤ (T : ℝ) / N + 2 * a * N := by
        have e1 : (T' : ℝ) = T + a * (N * N + 1) := by simp [T']
        have hNN : (1:ℝ) ≤ N * N := by nlinarith
        have h1 : (a : ℝ) * (N * N + 1) ≤ 2 * a * N * N := by
          nlinarith [mul_le_mul_of_nonneg_left hNN ha0]
        rw [e1, add_div]
        have h2 : (a : ℝ) * (N * N + 1) / N ≤ 2 * a * N := by
          rw [div_le_iff₀ hNpos]; linarith
        linarith
      have hTN : (0 : ℝ) ≤ (T : ℝ) / N := div_nonneg hT0 hNpos.le
      have hAR : (A : ℝ) = (3 + 2 * heads) * (1 + 2 * a) := by simp [A]
      rw [hL, hAR]
      push_cast
      have key : 2 * (heads : ℝ) * (1 + (T' : ℝ) / N) ≤
          (3 + 2 * heads) * (1 + 2 * a) * (1 + N + (T : ℝ) / N) := by
        have k1 : 2 * (heads : ℝ) * (1 + (T' : ℝ) / N) ≤
            2 * heads * (1 + (T : ℝ) / N + 2 * a * N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        have k2 : 2 * (heads : ℝ) * (1 + (T : ℝ) / N + 2 * a * N) ≤
            2 * heads * ((1 + 2 * a) * (1 + N + (T : ℝ) / N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
        have k3 : 2 * (heads : ℝ) * ((1 + 2 * a) * (1 + N + (T : ℝ) / N)) ≤
            (3 + 2 * heads) * (1 + 2 * a) * (1 + N + (T : ℝ) / N) := by
          have : 0 ≤ (1 + 2 * (a : ℝ)) * (1 + N + (T : ℝ) / N) := by positivity
          nlinarith
        linarith
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans (h2L.trans hd)

/-- The relation-table bound uses a scalar that may depend on the displayed input. -/
theorem lower_of_displays (price : PriceTwo) (M' : Machine) (a : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ T : ℕ,
      Displays M' N (T + a * (N * N + 1)) → c * scale (2 * N * N) ≤ T := by
  have table : TransTableBound :=
    transTableBound_of_field (K := AlgebraicClosure (ZMod 2))
      (transFieldTableBound_of_entropy price (Entropy.transEntropyBound _))
  obtain ⟨D, A, hA, N₁, extract⟩ := trace_of_displays M' a
  obtain ⟨c, hc, N₂, hard⟩ := table D
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨κ, hκ, N₃, arith⟩ := g5_arith A c hA' hc
  refine ⟨κ, hκ, max N₁ (max N₂ N₃), fun N hN T hdec => ?_⟩
  have hN1 : N₁ ≤ N := le_of_max_le_left hN
  have hN2 : N₂ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  obtain ⟨small, large⟩ := arith N hN3 T
  by_cases hT : (T : ℝ) ≤ N * N * Real.sqrt (Real.logb 2 N)
  · obtain ⟨loss, conclude⟩ := small hT
    obtain ⟨G, bounded, size, tables, dens⟩ := extract N hN1 T hdec
    have dens' : (2 : ℝ) ^ (-(1/100 : ℝ) * (N * N)) ≤ wordDensity (TransGood G tables) :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) loss).trans dens
    exact conclude G.vertices size (hard N hN2 G bounded tables dens')
  · exact large hT

end
end P1C1U.AstraC1U

#print axioms P1C1U.AstraC1U.lower_of_displays
