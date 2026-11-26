import P1Net.Factors

/-!
# P3 size bounds of the routed lane network `N_{x,σ}` (paper `eq:size`)

Lane P1-lean-net (2026-11-25, restart). With `t = I 2^h B` (the run length of `ContractEqCount`), `d_0 = 2^a`:
* `rn_positions`: `P_0 = 2 · I · locCount · 2^h`, so `P_0 · B = 2 · locCount · t` and `locCount = O(h)`
  (`locCount_le`): `P_0 = O(t h / B)`.
* `rn_width_le`: every width is at most `tupWidth`, and `tupWidth_le`: `tupWidth ≤ |Ext K| (|Γ|+|Q|+|K|) B`:
  `W_0 = O(B)`.
* `energy_le_of_width_le` (any OpenAI state): `L_0 ≤ (P_0 d_0 W_0)^2`; `rn_sqrt_energy_le`:
  `√L_0 ≤ 2 · locCount · d_0 · |Ext K| (|Γ|+|Q|+|K|) · t = O(t h)`.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression

/-! ## Any compression state -/

/-- `L ≤ (P d W)^2` when every width is at most `W` (paper: `L_0 = P_0 d_0 Σ b_e^2 ≤ (P_0 d_0 W_0)^2`). -/
theorem energy_le_of_width_le {a g : ℕ} (X : State a g) (W : ℕ) (hW : ∀ e, X.width e ≤ W) :
    X.energy ≤ ((X.positions * 2 ^ a * W : ℕ) : ℝ) ^ 2 := by
  have hc : Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord g) = X.positions * 2 ^ a := by
    simp only [State.positions, Fintype.card_prod, Fintype.card_fin]
    ac_rfl
  have hy : (0 : ℝ) ≤ (X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ) := by positivity
  have key : ∀ e : (X.Base × Fin (2 ^ a)) × BitWord g,
      (X.width e : ℝ) ^ 2 / (1 / ((X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ))) ≤
        (W : ℝ) ^ 2 * ((X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ)) := by
    intro e
    have hx : (X.width e : ℝ) ≤ W := by exact_mod_cast hW e
    have hx0 : (0 : ℝ) ≤ X.width e := by positivity
    rw [div_div_eq_mul_div, div_one]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx 2) hy
  calc X.energy
      = ∑ e, (X.width e : ℝ) ^ 2 / (1 / ((X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ))) := rfl
    _ ≤ ∑ _e : (X.Base × Fin (2 ^ a)) × BitWord g, (W : ℝ) ^ 2 * ((X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun e _ => key e
    _ = (Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord g) : ℝ) *
          ((W : ℝ) ^ 2 * ((X.positions : ℝ) * ((2 ^ a : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((X.positions * 2 ^ a * W : ℕ) : ℝ) ^ 2 := by
        rw [hc]
        push_cast
        ring

/-- `√L ≤ P d W`. -/
theorem sqrt_energy_le_of_width_le {a g : ℕ} (X : State a g) (W : ℕ) (hW : ∀ e, X.width e ≤ W) :
    Real.sqrt X.energy ≤ ((X.positions * 2 ^ a * W : ℕ) : ℝ) :=
  (Real.sqrt_le_sqrt (energy_le_of_width_le X W hW)).trans_eq (Real.sqrt_sq (by positivity))

/-! ## Widths of `N_{x,σ}` -/

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

theorem baseWidth_le (Wc Ws Wt : ℕ) (l : Loc K h) (s : Fin 4) :
    baseWidth Wc Ws Wt l s ≤ max Wc (max Ws Wt) := by
  have h1 : Wc ≤ max Wc (max Ws Wt) := le_max_left _ _
  have h2 : Ws ≤ max Wc (max Ws Wt) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : Wt ≤ max Wc (max Ws Wt) := (le_max_right _ _).trans (le_max_right _ _)
  cases l with
  | tabP c =>
    simp only [baseWidth]
    split_ifs
    · exact h3
    · split
      · exact h2
      · exact h1
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  | _ =>
    simp only [baseWidth]
    split_ifs <;> first | exact h1 | exact h2 | exact h3 | exact Nat.zero_le _

theorem stateNet_width_le (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
    (Wc Ws Wt : ℕ) (e : (((Fin I × Loc K h) × Bool) × Fin (2 ^ a)) × BitWord h) :
    (stateNet (K := K) I σ ha Wc Ws Wt).width e ≤ max Wc (max Ws Wt) := by
  obtain ⟨⟨v, i⟩, l⟩ := e
  show PreGraph.padWidth (preGraph (K := K) I σ) (netWidth I σ Wc Ws Wt) ((v, i), l) ≤ _
  unfold PreGraph.padWidth
  split
  · split_ifs
    · exact Nat.zero_le _
    · unfold netWidth
      split_ifs
      · exact Nat.zero_le _
      · exact baseWidth_le Wc Ws Wt _ _
  · exact Nat.zero_le _

section Factors

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)

theorem strWidth_le_tupWidth : strWidth V B ≤ tupWidth V B :=
  Nat.le_mul_of_pos_left _ (card_ext_pos V.K)

/-- **`W_0`**: every width of `N_{x,σ}` is at most the tuple width. -/
theorem rn_width_le (e : ((rnState V B I σ ha).Base × Fin (2 ^ a)) × BitWord h) :
    (rnState V B I σ ha).width e ≤ tupWidth V B := by
  obtain ⟨⟨v, i⟩, l⟩ := e
  have := stateNet_width_le (K := V.K) I σ ha (strWidth V B) (strWidth V B) (tupWidth V B) ((v, i), l)
  exact this.trans (max_le (strWidth_le_tupWidth V B) (max_le (strWidth_le_tupWidth V B) le_rfl))

omit [NeZero B] in
theorem strWidth_le (hB : 1 ≤ B) :
    strWidth V B ≤ (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K) * B := by
  have hQ : Fintype.card V.Q ≤ Fintype.card V.Q * B := Nat.le_mul_of_pos_right _ hB
  unfold strWidth
  nlinarith

/-- **`W_0 = O(B)`.** -/
theorem tupWidth_le :
    tupWidth V B ≤ Fintype.card (Ext V.K) * (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K) * B := by
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (strWidth_le V B (Nat.one_le_iff_ne_zero.mpr (NeZero.ne B)))

/-- **`P_0`**: the number of positions of `N_{x,σ}`. -/
theorem rn_positions : (rnState V B I σ ha).positions = 2 * (I * locCount V.K h) * 2 ^ h := by
  unfold State.positions
  rw [Fintype.card_prod, card_stateNet_base, Fintype.card_congr (laneEquiv h), Fintype.card_fin]

/-- `P_0 · B = 2 · locCount · t` with `t = I 2^h B`. -/
theorem rn_positions_mul : (rnState V B I σ ha).positions * B = 2 * locCount V.K h * (I * 2 ^ h * B) := by
  rw [rn_positions]
  ring

/-- **`√L_0 = O(t h)`**: `√L_0 ≤ 2 · locCount · d_0 · |Ext K| (|Γ|+|Q|+|K|) · t`, `t = I 2^h B`. -/
theorem rn_sqrt_energy_le :
    Real.sqrt (rnState V B I σ ha).energy ≤
      ((2 * locCount V.K h * 2 ^ a * (Fintype.card (Ext V.K) *
        (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K)) * (I * 2 ^ h * B) : ℕ) : ℝ) := by
  refine (sqrt_energy_le_of_width_le _ (tupWidth V B) (rn_width_le V B I σ ha)).trans ?_
  have hW := tupWidth_le V B
  rw [rn_positions]
  have : 2 * (I * locCount V.K h) * 2 ^ h * 2 ^ a * tupWidth V B ≤
      2 * locCount V.K h * 2 ^ a * (Fintype.card (Ext V.K) *
        (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K)) * (I * 2 ^ h * B) := by
    calc 2 * (I * locCount V.K h) * 2 ^ h * 2 ^ a * tupWidth V B
        ≤ 2 * (I * locCount V.K h) * 2 ^ h * 2 ^ a *
            (Fintype.card (Ext V.K) * (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K) * B) :=
          Nat.mul_le_mul_left _ hW
      _ = _ := by ring
  exact_mod_cast this

end Factors

/-- **`locCount = O(h)`** for a fixed set of tapes. -/
theorem locCount_le : locCount K h ≤ (11 + Fintype.card (Ext K) + 70 * Fintype.card K) * (h + 1) := by
  unfold locCount
  nlinarith [Nat.zero_le (Fintype.card K * h), Nat.zero_le (Fintype.card (Ext K) * h)]

end P1Net
