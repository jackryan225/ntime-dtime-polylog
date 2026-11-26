import C1Challenge.Statement

/-!
# P1, Case 1, task C2 (core): a fast coTRANS decider gives a fast TRANS decider

Mathlib and the Challenge file only. Machine model: `C1Challenge.Machine` (field-for-field copy of
OpenAI's `FiniteMultiTapeMachine`).

`TransLowerBound` below is the Challenge-model copy of `TransLowerBound` in
`research/g3/blind-noport/lean/TransDecision.lean`: the same text with `FiniteMultiTapeMachine`
replaced by `C1Challenge.Machine` and `MultiTapeHaltsIn` by `HaltsWithin`. The bridge from the
OpenAI-model statement to this one is task W0b.

Main results:
* `coTRANS_transEncode`: `coTRANS (transEncode X Y) = !transAnswer X Y`.
* `not_dtimeIn_coTRANS`: `TransLowerBound → ¬ DTIMEIn coTRANS (n (log₂ n)^(1/4))`.
* `c1_of_transLowerBound`: `TransLowerBound → NTIMELinLog coTRANS →` the statement of `C1Challenge.c1`.
-/

namespace P1Case1

open C1Challenge

/-! ## TRANS and coTRANS -/

/-- Row-major list: entry `(i,k)` at position `N*i + k` (`finProdFinEquiv` sends `(i,k)` to `k + N*i`). -/
def rowMajor {N : ℕ} (X : Fin N → Fin N → Bool) : List Bool :=
  List.ofFn fun j : Fin (N * N) => X (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

/-- The input `(X, Y)`: `X` row-major, then `Y` row-major; length `2N²`. -/
def transEncode {N : ℕ} (X Y : Fin N → Fin N → Bool) : List Bool :=
  rowMajor X ++ rowMajor Y

/-- Membership in TRANS = {(X,Y) : Y = Xᵀ}. -/
def transAnswer {N : ℕ} (X Y : Fin N → Fin N → Bool) : Bool :=
  decide (∀ i k, Y i k = X k i)

/-- `M` decides TRANS at side `N`, halting within `T` steps on every input of side `N`. -/
def DecidesTransIn (M : Machine) (N T : ℕ) : Prop :=
  ∀ X Y : Fin N → Fin N → Bool, HaltsWithin M (transEncode X Y) (transAnswer X Y) T

/-- `scale n = n √(log₂ n)` (OpenAI's `scale` in `MultitapeWeakETH/Machine.lean`). -/
noncomputable def scale (n : ℕ) : ℝ := n * Real.sqrt (Real.logb 2 n)

/-- For each machine: `c_M n √(log₂ n)` at every input length `n = 2N² ≥ n_M` (Challenge model). -/
def TransLowerBound : Prop := ∀ M : Machine, ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
  ∀ N ≥ N₀, ∀ T : ℕ, DecidesTransIn M N T → c * scale (2 * N * N) ≤ T

/-- coTRANS, positional form: the length is `2N²` and the entry `x[N i + k]` (entry `(i,k)` of the
first matrix) differs from `x[N² + N k + i]` (entry `(k,i)` of the second matrix) for some `i, k < N`. -/
def CoTrans (x : List Bool) : Prop :=
  ∃ N i k : ℕ, i < N ∧ k < N ∧ x.length = 2 * N * N ∧
    x.getD (N * i + k) false ≠ x.getD (N * N + N * k + i) false

open Classical in
/-- The language coTRANS: words of length `2N²` whose second half is not the transpose of the first.
Words of other lengths are not in it. -/
noncomputable def coTRANS (x : List Bool) : Bool := decide (CoTrans x)

@[simp] theorem length_rowMajor {N : ℕ} (X : Fin N → Fin N → Bool) :
    (rowMajor X).length = N * N := by
  simp [rowMajor]

@[simp] theorem length_transEncode {N : ℕ} (X Y : Fin N → Fin N → Bool) :
    (transEncode X Y).length = 2 * N * N := by
  simp [transEncode]; ring

theorem rowMajor_getD {N : ℕ} (X : Fin N → Fin N → Bool) {i k : ℕ} (hi : i < N) (hk : k < N) :
    (rowMajor X).getD (N * i + k) false = X ⟨i, hi⟩ ⟨k, hk⟩ := by
  have hN : 0 < N := by omega
  have h : N * i + k < N * N := by nlinarith
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp only [rowMajor, List.getElem_ofFn, finProdFinEquiv_symm_apply]
  congr 1
  · ext
    simp only [Fin.coe_divNat]
    rw [Nat.mul_add_div hN, Nat.div_eq_of_lt hk, Nat.add_zero]
  · ext
    simp only [Fin.coe_modNat]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

theorem transEncode_getD_left {N : ℕ} (X Y : Fin N → Fin N → Bool) {i k : ℕ} (hi : i < N)
    (hk : k < N) : (transEncode X Y).getD (N * i + k) false = X ⟨i, hi⟩ ⟨k, hk⟩ := by
  have h : N * i + k < N * N := by nlinarith
  rw [transEncode, List.getD_append _ _ _ _ (by simpa using h), rowMajor_getD X hi hk]

theorem transEncode_getD_right {N : ℕ} (X Y : Fin N → Fin N → Bool) {i k : ℕ} (hi : i < N)
    (hk : k < N) : (transEncode X Y).getD (N * N + N * k + i) false = Y ⟨k, hk⟩ ⟨i, hi⟩ := by
  have hle : (rowMajor X).length ≤ N * N + N * k + i := by
    rw [length_rowMajor, Nat.add_assoc]; exact Nat.le_add_right _ _
  have hsub : N * N + N * k + i - N * N = N * k + i := by
    rw [Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [transEncode, List.getD_append_right _ _ _ _ hle, length_rowMajor, hsub, rowMajor_getD Y hk hi]

theorem coTrans_transEncode {N : ℕ} (X Y : Fin N → Fin N → Bool) :
    CoTrans (transEncode X Y) ↔ ∃ i k : Fin N, X i k ≠ Y k i := by
  constructor
  · rintro ⟨N', i, k, hi, hk, hlen, hne⟩
    have hN : N' = N := by
      rw [length_transEncode] at hlen
      have h2 : N' * N' = N * N := by linarith
      exact Nat.mul_self_inj.mp h2
    subst hN
    refine ⟨⟨i, hi⟩, ⟨k, hk⟩, ?_⟩
    rwa [transEncode_getD_left X Y hi hk, transEncode_getD_right X Y hi hk] at hne
  · rintro ⟨i, k, hne⟩
    refine ⟨N, i, k, i.2, k.2, length_transEncode X Y, ?_⟩
    rw [transEncode_getD_left X Y i.2 k.2, transEncode_getD_right X Y i.2 k.2]
    exact hne

/-- On encoded pairs, coTRANS is the negation of TRANS. -/
theorem coTRANS_transEncode {N : ℕ} (X Y : Fin N → Fin N → Bool) :
    coTRANS (transEncode X Y) = !transAnswer X Y := by
  have h1 : coTRANS (transEncode X Y) = true ↔ ∃ i k : Fin N, X i k ≠ Y k i := by
    rw [← coTrans_transEncode]
    simp only [coTRANS, decide_eq_true_eq]
  have h2 : (!transAnswer X Y) = true ↔ ∃ i k : Fin N, X i k ≠ Y k i := by
    unfold transAnswer
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    simp only [not_forall]
    constructor
    · rintro ⟨k, i, h⟩
      exact ⟨i, k, fun e => h e.symm⟩
    · rintro ⟨i, k, h⟩
      exact ⟨k, i, fun e => h e.symm⟩
  exact Bool.eq_iff_iff.mpr (h1.trans h2.symm)

/-! ## Flipping the answer -/

/-- The same machine with the answer of every final state negated. -/
def flip (M : Machine) : Machine := { M with accept := fun q => !M.accept q }

theorem haltsWithin_flip {M : Machine} {x : List Bool} {b : Bool} {T : ℕ} :
    HaltsWithin (flip M) x b T ↔ HaltsWithin M x (!b) T := by
  constructor
  · rintro ⟨t, ht, c, hrun, hstop, hacc⟩
    refine ⟨t, ht, c, hrun, hstop, ?_⟩
    rw [← hacc]
    simp [flip]
  · rintro ⟨t, ht, c, hrun, hstop, hacc⟩
    refine ⟨t, ht, c, hrun, hstop, ?_⟩
    simp [flip, hacc]

theorem HaltsWithin.mono {M : Machine} {x : List Bool} {b : Bool} {T T' : ℕ}
    (h : HaltsWithin M x b T) (hT : T ≤ T') : HaltsWithin M x b T' := by
  obtain ⟨t, ht, c, h1, h2, h3⟩ := h
  exact ⟨t, ht.trans hT, c, h1, h2, h3⟩

/-- A coTRANS decider within `C (f n + 1)` steps gives, after flipping its answer, a TRANS decider
at every side `N` within `⌊C (f (2N²) + 1)⌋₊` steps. -/
theorem decidesTransIn_flip {M : Machine} {C : ℝ} {f : ℕ → ℝ}
    (hM : ∀ x : List Bool, ∃ T : ℕ, (T : ℝ) ≤ C * (f x.length + 1) ∧ HaltsWithin M x (coTRANS x) T)
    (N : ℕ) : DecidesTransIn (flip M) N ⌊C * (f (2 * N * N) + 1)⌋₊ := by
  intro X Y
  obtain ⟨T, hT, hrun⟩ := hM (transEncode X Y)
  rw [length_transEncode] at hT
  rw [coTRANS_transEncode] at hrun
  rw [haltsWithin_flip]
  exact HaltsWithin.mono hrun (Nat.le_floor hT)

/-! ## The arithmetic: `n √(log₂ n)` beats `C (n (log₂ n)^(1/4) + 1)` at some side `N ≥ N₀` -/

theorem exists_gap (c C : ℝ) (hc : 0 < c) (N₀ : ℕ) : ∃ N ≥ N₀,
    C * ((((2 * N * N : ℕ) : ℝ) * Real.logb 2 ((2 * N * N : ℕ) : ℝ) ^ (1/4 : ℝ)) + 1) <
      c * scale (2 * N * N) := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, N₀ ≤ m ∧ (2 * C / c) ^ 4 < (2 * m + 1 : ℝ) := by
    refine ⟨N₀ + ⌈(2 * C / c) ^ 4⌉₊, by omega, ?_⟩
    have h := Nat.le_ceil ((2 * C / c) ^ 4)
    push_cast
    have h0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  have hmN : m < 2 ^ m := Nat.lt_two_pow_self
  refine ⟨2 ^ m, by omega, ?_⟩
  -- the length n = 2 (2^m)^2 = 2^(2m+1) and its logarithm L = 2m+1
  set n : ℕ := 2 * 2 ^ m * 2 ^ m with hn_def
  have hn : (n : ℝ) = 2 ^ (2 * m + 1) := by
    rw [hn_def]; push_cast; ring
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; exact one_le_pow₀ (by norm_num)
  have hL : Real.logb 2 (n : ℝ) = 2 * m + 1 := by
    rw [hn, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  set L : ℝ := 2 * m + 1 with hL_def
  have hL1 : (1 : ℝ) ≤ L := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  -- u = L^(1/4): u ≥ 1, u^4 = L, √L = u^2
  set u : ℝ := L ^ (1/4 : ℝ) with hu_def
  have hu1 : 1 ≤ u := Real.one_le_rpow hL1 (by norm_num)
  have hu4 : u ^ 4 = L := by
    rw [hu_def, show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hL0 (by norm_num)
  have hsqrt : Real.sqrt L = u ^ 2 := by
    rw [Real.sqrt_eq_rpow, hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  have hgap : 2 * C / c < u := by
    have hu0 : (0 : ℝ) ≤ u := by linarith
    refine lt_of_pow_lt_pow_left₀ 4 hu0 ?_
    rw [hu4]; exact hm
  have hcu : 2 * C < c * u := by
    rw [div_lt_iff₀ hc] at hgap; linarith
  unfold scale
  rw [hL, hsqrt]
  -- goal: C * (n * u + 1) < c * (n * u^2)
  have hnu : 1 ≤ (n : ℝ) * u := by nlinarith
  rcases le_or_gt C 0 with hC | hC
  · have h1 : C * ((n : ℝ) * u + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
    have h2 : 0 < c * ((n : ℝ) * u ^ 2) := by positivity
    linarith
  · calc C * ((n : ℝ) * u + 1) ≤ 2 * C * ((n : ℝ) * u) := by nlinarith
      _ < c * u * ((n : ℝ) * u) := by
        apply mul_lt_mul_of_pos_right hcu; linarith
      _ = c * ((n : ℝ) * u ^ 2) := by ring

/-! ## Case 1, C2 core -/

/-- **C2 core.** If every TRANS decider needs `c_M n √(log n)` steps at all large `n = 2N²`, then
coTRANS is not in `DTIME(O(n (log₂ n)^(1/4)))` (Challenge model). -/
theorem not_dtimeIn_coTRANS (lower : TransLowerBound) :
    ¬ DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ (1/4 : ℝ)) := by
  rintro ⟨M, C, hM⟩
  obtain ⟨c, hc, N₀, hlow⟩ := lower (flip M)
  obtain ⟨N, hN, hgap⟩ := exists_gap c C hc N₀
  have hdec := decidesTransIn_flip (f := fun n : ℕ => (n : ℝ) * Real.logb 2 n ^ (1/4 : ℝ)) hM N
  have hle := hlow N hN _ hdec
  beta_reduce at hle
  -- the floor is at most its argument, which is nonnegative (some input of side N exists)
  have hnonneg : (0 : ℝ) ≤ C * (((2 * N * N : ℕ) : ℝ) * Real.logb 2 ((2 * N * N : ℕ) : ℝ) ^ (1/4 : ℝ) + 1) := by
    obtain ⟨T, hT, -⟩ := hM (transEncode (fun _ _ => false : Fin N → Fin N → Bool) (fun _ _ => false))
    rw [length_transEncode] at hT
    exact (Nat.cast_nonneg T).trans hT
  have hfloor := Nat.floor_le hnonneg
  linarith

/-- **Case 1 assembly in the Challenge model.** The TRANS lower bound and the NTIME upper bound for
coTRANS give the statement of `C1Challenge.c1`, with `σ = 1/4` and `L = coTRANS`. -/
theorem c1_of_transLowerBound (lower : TransLowerBound) (upper : NTIMELinLog coTRANS) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      NTIMELinLog L ∧ ¬ DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  ⟨1/4, by norm_num, coTRANS, upper, not_dtimeIn_coTRANS lower⟩

/-! ## Every exponent below `1/2` (paper: "Any σ < 1/2 works") -/

theorem exists_gap_rpow (c C σ : ℝ) (hc : 0 < c) (hσ0 : 0 ≤ σ) (hσ : σ < 1/2) (N₀ : ℕ) :
    ∃ N ≥ N₀, C * ((((2 * N * N : ℕ) : ℝ) * Real.logb 2 ((2 * N * N : ℕ) : ℝ) ^ σ) + 1) <
      c * scale (2 * N * N) := by
  set δ : ℝ := 1/2 - σ with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set K : ℝ := max (2 * C / c) 1 with hK_def
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, N₀ ≤ m ∧ K ^ (1/δ) < (2 * m + 1 : ℝ) := by
    refine ⟨N₀ + ⌈K ^ (1/δ)⌉₊, by omega, ?_⟩
    have h := Nat.le_ceil (K ^ (1/δ))
    push_cast
    have h0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    have h1 : (0 : ℝ) ≤ (⌈K ^ (1/δ)⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hmN : m < 2 ^ m := Nat.lt_two_pow_self
  refine ⟨2 ^ m, by omega, ?_⟩
  set n : ℕ := 2 * 2 ^ m * 2 ^ m with hn_def
  have hn : (n : ℝ) = 2 ^ (2 * m + 1) := by
    rw [hn_def]; push_cast; ring
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; exact one_le_pow₀ (by norm_num)
  have hL : Real.logb 2 (n : ℝ) = 2 * m + 1 := by
    rw [hn, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  set L : ℝ := 2 * m + 1 with hL_def
  have hL1 : (1 : ℝ) ≤ L := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hsqrt : Real.sqrt L = L ^ σ * L ^ δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hLpos]
    congr 1
    rw [hδ_def]; ring
  have hs1 : 1 ≤ L ^ σ := Real.one_le_rpow hL1 hσ0
  have ht0 : 0 < L ^ δ := Real.rpow_pos_of_pos hLpos δ
  have hKδ : K < L ^ δ := by
    have hpow : (K ^ (1/δ)) ^ δ = K := by
      rw [← Real.rpow_mul hK0, one_div_mul_cancel hδ.ne', Real.rpow_one]
    have h0 : 0 ≤ K ^ (1/δ) := Real.rpow_nonneg hK0 _
    calc K = (K ^ (1/δ)) ^ δ := hpow.symm
      _ < L ^ δ := Real.rpow_lt_rpow h0 hm hδ
  have hcu : 2 * C < c * L ^ δ := by
    have h1 : 2 * C / c < L ^ δ := lt_of_le_of_lt (le_max_left _ _) hKδ
    rw [div_lt_iff₀ hc] at h1; linarith
  unfold scale
  rw [hL, hsqrt]
  have hns : 1 ≤ (n : ℝ) * L ^ σ := by nlinarith
  rcases le_or_gt C 0 with hC | hC
  · have h1 : C * ((n : ℝ) * L ^ σ + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
    have h2 : 0 < c * ((n : ℝ) * (L ^ σ * L ^ δ)) :=
      mul_pos hc (mul_pos (by linarith) (mul_pos (by linarith) ht0))
    linarith
  · calc C * ((n : ℝ) * L ^ σ + 1) ≤ 2 * C * ((n : ℝ) * L ^ σ) := by nlinarith
      _ < c * L ^ δ * ((n : ℝ) * L ^ σ) := by
        apply mul_lt_mul_of_pos_right hcu; linarith
      _ = c * ((n : ℝ) * (L ^ σ * L ^ δ)) := by ring

/-- **C2 core, every exponent `0 ≤ σ < 1/2`.** -/
theorem not_dtimeIn_coTRANS_of_lt (lower : TransLowerBound) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1/2) : ¬ DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  rintro ⟨M, C, hM⟩
  obtain ⟨c, hc, N₀, hlow⟩ := lower (flip M)
  obtain ⟨N, hN, hgap⟩ := exists_gap_rpow c C σ hc hσ0 hσ N₀
  have hdec := decidesTransIn_flip (f := fun n : ℕ => (n : ℝ) * Real.logb 2 n ^ σ) hM N
  have hle := hlow N hN _ hdec
  beta_reduce at hle
  have hnonneg : (0 : ℝ) ≤
      C * (((2 * N * N : ℕ) : ℝ) * Real.logb 2 ((2 * N * N : ℕ) : ℝ) ^ σ + 1) := by
    obtain ⟨T, hT, -⟩ :=
      hM (transEncode (fun _ _ => false : Fin N → Fin N → Bool) (fun _ _ => false))
    rw [length_transEncode] at hT
    exact (Nat.cast_nonneg T).trans hT
  have hfloor := Nat.floor_le hnonneg
  linarith

/-- **Case 1 assembly, one language for all exponents below `1/2`.** -/
theorem coTRANS_separates (lower : TransLowerBound) (upper : NTIMELinLog coTRANS) :
    NTIMELinLog coTRANS ∧ ∀ σ : ℝ, 0 ≤ σ → σ < 1/2 →
      ¬ DTIMEIn coTRANS (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  ⟨upper, fun _ h0 h1 => not_dtimeIn_coTRANS_of_lt lower h0 h1⟩

end P1Case1
