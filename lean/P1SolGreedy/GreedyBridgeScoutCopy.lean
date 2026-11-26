-- Source: research/agents/P1-sol-scoutgrp/lean/P1SolScoutGrp/EnergyFit.lean
import P1SolGreedy.GreedyBridgeScoutRow
import P1ChkGreedy.LocalC78

namespace P1SolGreedy.SolBridge.Scout

open Filter P1Wrap P1Wit P1ChkGreedy
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open P1SolGreedy.SolBridge.ScoutRow

attribute [local instance] P1P7.instDecEqBase

section State

variable {a g : ℕ} (X : State a (packingLaneBits a g))

theorem prefix_le_total (W : X.packingData.Motif → Bool → Fin 4 → ℕ) (y : X.Base) (b : Bool) :
    truePrefix X W y b ≤ ∑ m, ∑ e, P1P7.layoutCoeff e * W m b e ^ 2 := by
  rw [← truePrefix_last X W]
  unfold truePrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Fin.le_iff_val_le_val]
    simp only [lastBase, Equiv.apply_symm_apply]
    have := (X.baseIndex z).isLt
    omega
  · exact fun _ _ _ => Nat.zero_le _

theorem motif_count :
    Fintype.card X.packingData.Motif ≤ Fintype.card X.Base * 2 ^ packingLaneBits a g * 2 ^ a := by
  calc
    _ ≤ Fintype.card (OldArc X) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord (packingLaneBits a g)) :=
      Fintype.card_congr (packingArcEquiv X.Base a g).symm
    _ = _ := by
      have hw := Fintype.card_congr (bitWordFinEquiv (packingLaneBits a g))
      rw [Fintype.card_fin] at hw
      simp only [Fintype.card_prod, Fintype.card_fin, hw]
      ac_rfl

theorem prefix_bound (W : X.packingData.Motif → Bool → Fin 4 → ℕ) (cap : ℕ)
    (hW : ∀ m b e, W m b e ≤ cap) (y : X.Base) (b : Bool) :
    truePrefix X W y b ≤ (Fintype.card X.Base * 2 ^ packingLaneBits a g * 2 ^ a) * (80 * cap ^ 2) := by
  have hcoef (e : Fin 4) : P1P7.layoutCoeff e ≤ 20 := by fin_cases e <;> decide
  refine (prefix_le_total X W y b).trans ?_
  calc
    _ ≤ ∑ _m : X.packingData.Motif, ∑ _e : Fin 4, 20 * cap ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro e _
      exact Nat.mul_le_mul (hcoef e) (Nat.pow_le_pow_left (hW m b e) 2)
    _ = Fintype.card X.packingData.Motif * (80 * cap ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf <;> ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (motif_count X)

variable {k : Type*} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem supply_width_cap (s : X.ShrinkSelection B) (wW : ℕ)
    (hcap : fieldFactor B * (X.maxWireWidth + 1) ≤ 2 ^ wW) :
    ∀ m b e, termW B X s m b e ≤ 2 ^ wW := by
  intro m b e
  have h := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
    (fun _ => X.width_le_maxWireWidth _) B m (s m)
  exact ((h.2 (b, e)).2).trans hcap

theorem supply_width_from_old (s : X.ShrinkSelection B) (wW : ℕ)
    (hwidth : ∀ e, X.width e < 2 ^ wW) :
    ∀ m b e, termW B X s m b e ≤ fieldFactor B * 2 ^ wW := by
  have hmax : X.maxWireWidth ≤ 2 ^ wW - 1 := by
    apply Finset.sup_le
    intro e _
    have he := hwidth e
    omega
  have hcap : fieldFactor B * (X.maxWireWidth + 1) ≤ fieldFactor B * 2 ^ wW :=
    Nat.mul_le_mul_left _ (by have := Nat.two_pow_pos wW; omega)
  intro m b e
  have h := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
    (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
    (fun _ => X.width_le_maxWireWidth _) B m (s m)
  exact ((h.2 (b, e)).2).trans hcap

end State

theorem eventually_log_weight (C : ℕ) :
    ∀ᶠ t : ℕ in atTop, C * (Params.p t + 1) ≤ Params.lam t := by
  filter_upwards [Params.eventually_of_p (Params.eventually_mul_pow_lt_two_pow (2 * C) 1),
    Params.eventually_of_p (eventually_ge_atTop 1), eventually_ge_atTop 2] with t hp ht ht'
  calc
    _ ≤ (2 * C) * (Params.p t) ^ 1 := by rw [pow_one, mul_comm 2 C, Nat.mul_assoc]; gcongr; omega
    _ ≤ 2 ^ Params.p t := hp.le
    _ ≤ _ := Params.two_pow_p_le ht'

/-- The raw energy prefix fits the canonical energy field once the routed-size
bounds hold and the virtual supply widths fit their common width cap. -/
theorem eventually_energy_fields_fit (K : Consts) (C Cw : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ (D : Dims) (zl : ℕ),
      SpaceIn K 1 C t D zl → 6 * Params.lam t ≤ D.bigW →
      ∀ (l : ℕ), l ≤ D.top →
      ∀ {a g : ℕ} (X : State a (packingLaneBits a g)),
        (D.lv l).bases = Fintype.card X.Base →
        (D.lv l).lanes = 2 ^ packingLaneBits a g →
        (D.lv l).slots = 2 ^ a →
        ∀ (W : X.packingData.Motif → Bool → Fin 4 → ℕ),
          (∀ m b e, W m b e ≤ Cw * 2 ^ D.wW) →
          ∀ y b, truePrefix X W y b < 2 ^ D.bigW := by
  filter_upwards [eventually_log_weight C, eventually_log_weight (320 * C * C * Cw ^ 2),
    Params.eventually_Ib 1 (by decide), eventually_ge_atTop 2] with t hWidth hCoeff hI ht
  intro D zl hS hbig l hl a g X hb hg hs W hW y b
  have hRoute : D.I * D.N ≤ 4 * t := by
    have h : D.I * D.N * Params.B t ≤ 4 * t := by
      rw [hS.I_eq, hS.N_eq, Nat.mul_assoc, Nat.mul_comm (Params.N t), ← Params.bb]
      simpa only [Nat.mul_one] using hI.2
    exact (Nat.le_mul_of_pos_right (D.I * D.N) (Params.B_pos t)).trans h
  have hSize : (D.lv l).bases * (D.lv l).lanes * (D.lv l).slots ≤
      (4 * C * C * (Params.p t + 1)) * t := by
    calc
      _ ≤ (C * D.I * D.N * (Params.p t + 1)) * C :=
        Nat.mul_le_mul (row_positions_le hS l hl) (hS.slots_le l hl)
      _ = (C * C * (Params.p t + 1)) * (D.I * D.N) := by ring
      _ ≤ (C * C * (Params.p t + 1)) * (4 * t) := Nat.mul_le_mul_left _ hRoute
      _ = _ := by ring
  let lam := Params.lam t
  have hw : D.wW ≤ lam := hS.wW_le.trans hWidth
  have hsmall : (320 * C * C * Cw ^ 2) * (Params.p t + 1) ≤ 2 ^ lam :=
    hCoeff.trans (Params.lt_two_pow' _).le
  have hlpos : 0 < lam := Params.lam_pos ht
  calc
    _ ≤ ((D.lv l).bases * (D.lv l).lanes * (D.lv l).slots) * (80 * (Cw * 2 ^ D.wW) ^ 2) := by
      rw [hb, hg, hs]
      exact prefix_bound X W _ hW y b
    _ ≤ ((4 * C * C * (Params.p t + 1)) * t) * (80 * (Cw * 2 ^ lam) ^ 2) := by
      exact Nat.mul_le_mul hSize (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left Cw (Nat.pow_le_pow_right (by decide) hw)) 2))
    _ = ((320 * C * C * Cw ^ 2) * (Params.p t + 1)) * (t * (2 ^ lam) ^ 2) := by ring
    _ ≤ 2 ^ lam * (2 ^ lam * (2 ^ lam) ^ 2) :=
      Nat.mul_le_mul hsmall (Nat.mul_le_mul_right _ (Params.t_le_two_pow_lam t))
    _ = 2 ^ (4 * lam) := by rw [show (4 * lam) = lam + (lam + (lam + lam)) by omega]; simp only [pow_add, pow_two]
    _ < 2 ^ (6 * lam) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hbig

end P1SolGreedy.SolBridge.Scout

#print axioms P1SolGreedy.SolBridge.Scout.prefix_bound
#print axioms P1SolGreedy.SolBridge.Scout.supply_width_from_old
#print axioms P1SolGreedy.SolBridge.Scout.eventually_energy_fields_fit
