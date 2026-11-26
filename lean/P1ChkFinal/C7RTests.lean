import P1ChkFinal.C7RFam

/-!
# P1ChkFinal.C7RTests: the tests of decision D15 for family 6 (lane P1-lean-greedy)

T1/T2 are `C7Rchk_flag`, `C7Rchk_not_admitted` (C7R.lean); T4 is `C7Rfam_shrink`, `C7Rfam_out`, `C7all_shrink_iff`,
`C7all_refresh_iff` (C7RFam.lean). Here:
* `C7all_level_refresh` (family 6 over ALL indices of a refresh level = the refresh part at the term slots);
* T6 `greedy_refresh_step`: the step at a refresh level from the stored-field facts, with the integration bridge as a
  STUB hypothesis `hbridge` (premise of the group ⇒ (stored term table is a choice's table ↔ `G`));
* T3 `C7all_sound_refresh`: a witness whose level-`ℓ` panels and refresh terms are those of a true state and a refresh
  choice passes family 6 at every index of the level (soundness; through the encoding = integ's bridge);
* T7 `census_refresh`: at a refresh level the only kinds with fields are the panel kinds and `terms`.
-/

namespace P1ChkFinal.C7R

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1SolGreedy

/-- **T7 (refresh levels)**: a kind with at least one field at a non-shrinking level is a panel kind or `terms`
(layout, colour, offset, energy have count `0`). -/
theorem census_refresh (L : LevelDims) (h : L.shrink = false) (k : Mem) (hk : 0 < L.count k) :
    k ≠ .layout ∧ k ≠ .colour ∧ k ≠ .offset ∧ k ≠ .energy := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp [LevelDims.count, h] at hk

section Tests

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
  (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- **Family 6 over all indices of a refresh level** = the refresh part at the term slots `(Y, key)` of the level. -/
theorem C7all_level_refresh (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ : ℕ}
    (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = false) :
    (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7all P hdH hconn F B Dn ag x u i) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < ((Dn x.length).lv ℓ).termKeys,
        C7Rfam P hdH hconn F Dn x u (encRefIdx (Dn x.length) ℓ Y key) := by
  constructor
  · intro h Y _ key _
    exact (h _ (encIdx_mod _ hℓ _)).2
  · intro h i hi
    have hsi : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false := by rw [hi]; exact hs
    refine (C7all_refresh_iff P hdH hconn F B Dn ag x u i hsi).mpr ?_
    intro hS
    have hj := hS.2.2
    change i / 2 ^ levBits (Dn x.length) <
      ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).bases *
        ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).termKeys at hj
    rw [hi] at hj
    set j := i / 2 ^ levBits (Dn x.length) with hjdef
    set tk := ((Dn x.length).lv ℓ).termKeys
    have htk : 0 < tk := by
      rcases Nat.eq_zero_or_pos tk with h0 | h0
      · rw [h0, Nat.mul_zero] at hj; exact absurd hj (Nat.not_lt_zero _)
      · exact h0
    have hY : j / tk < ((Dn x.length).lv ℓ).bases := by
      rw [Nat.div_lt_iff_lt_mul htk]; exact hj
    have hkey : j % tk < tk := Nat.mod_lt _ htk
    have hidx : encRefIdx (Dn x.length) ℓ (j / tk) (j % tk) = i := by
      unfold encRefIdx encIdx
      rw [Nat.mod_add_div j tk, hjdef, ← hi]
      exact Nat.mod_add_div i _
    have := h _ hY _ hkey
    rw [hidx] at this
    exact this hS

/-- **T3 (soundness at a refresh level)**: if the stored panels of level `ℓ` are those of a refresh state `X` and the stored
term table is that of a refresh choice `c` (what the encoding of a tuple stores, integ's bridge), family 6 passes at every
index of the level. -/
theorem C7all_sound_refresh {g : ℕ} (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ : ℕ}
    (X : State a (a + g)) (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = false)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hK : ((Dn x.length).lv ℓ).termKeys = 2 ^ g)
    (hg : ((Dn x.length).lv ℓ).laneW - a = g)
    (hP : ∀ y, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X y) (P1P7.panel X y))
    (c : DyadicRefreshChoice X P hdH hconn F)
    (hst : storedTm (Dn x.length) u ℓ X = trueBlockTerms P hdH hconn F X c) :
    ∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7all P hdH hconn F B Dn ag x u i :=
  (C7all_level_refresh P hdH hconn F B Dn ag x u hℓ hs).mpr
    ((C7Rfam_stage P hdH hconn F Dn x u X hℓ hs hN hK hg hP).mpr ⟨c, hst⟩)

/-- **T6 (the greedy step at a refresh level, D5Steps shape, integration bridge as a STUB)**: the five greedy families at
the indices of a refresh level `ℓ` pass exactly when the group `G` holds, given the premise `Pre` of the group and the
bridge `hbridge` (premise ⇒ (the stored refresh term table is a choice's table ↔ `G`); for `G = greedyG ℓ u`,
`Pre` = the earlier groups, the bridge is integ's encoding lemma). -/
theorem greedy_refresh_step {g : ℕ} (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ : ℕ}
    (X : State a (a + g)) (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = false)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hK : ((Dn x.length).lv ℓ).termKeys = 2 ^ g)
    (hg : ((Dn x.length).lv ℓ).laneW - a = g)
    (hP : ∀ y, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X y) (P1P7.panel X y))
    (Pre G : Prop)
    (hbridge : Pre → ((∃ c : DyadicRefreshChoice X P hdH hconn F,
      storedTm (Dn x.length) u ℓ X = trueBlockTerms P hdH hconn F X c) ↔ G)) (hpre : Pre) :
    ((∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C5fam Dn x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C6fam Dn ag x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7all P hdH hconn F B Dn ag x u i) ∧
      (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C8fam B Dn ag x u i) ∧ C9fam Dn x u ℓ) ↔ G := by
  have h5 : ∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C5fam Dn x u i := fun i hi =>
    GreedyRefreshGap.C5fam_refresh Dn x u i (by rw [hi]; exact hs)
  have h6 : ∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C6fam Dn ag x u i := fun i hi =>
    GreedyRefreshGap.C6fam_refresh Dn ag x u i (by rw [hi]; exact hs)
  have h8 : ∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C8fam B Dn ag x u i := fun i hi =>
    GreedyRefreshGap.C8fam_refresh B Dn ag x u i (by rw [hi]; exact hs)
  have h9 : C9fam Dn x u ℓ := GreedyRefreshGap.C9fam_refresh Dn x u ℓ hs
  rw [← hbridge hpre, ← C7Rfam_stage P hdH hconn F Dn x u X hℓ hs hN hK hg hP,
    ← C7all_level_refresh P hdH hconn F B Dn ag x u hℓ hs]
  exact ⟨fun h => h.2.2.1, fun h => ⟨h5, h6, h, h8, h9⟩⟩

end Tests

end P1ChkFinal.C7R

#print axioms P1ChkFinal.C7R.census_refresh
#print axioms P1ChkFinal.C7R.C7all_level_refresh
#print axioms P1ChkFinal.C7R.C7all_sound_refresh
#print axioms P1ChkFinal.C7R.greedy_refresh_step
