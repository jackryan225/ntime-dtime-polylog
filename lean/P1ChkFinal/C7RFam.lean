import P1ChkFinal.C7R
import P1ChkFinal.GreedyRefreshGap

/-!
# P1ChkFinal.C7RFam: family 6 after decision D15 = C7 at shrinking AND refresh levels (lane P1-lean-greedy)

* `C7Rfam`: index `i = ℓ + 2^L j` (as every per-level family), `j = key + termKeys * Y`: at a REFRESH level `ℓ`
  (`shrink = false`, `j < bases * termKeys`; the final level has `termKeys = 0` in the genuine dims) it is the stored-field
  check `C7Rat` at the term slot `(Y, key)`; every other index accepts. The refresh data `P, hdH, hconn, F` (in the genuine
  schedule: `S.graph`, `Bt.refresh`, `a = S.portExponent`, `dH = 2^S.expanderExponent`) are the same at every refresh level;
  the lane bits of the block word at level `ℓ` are `g = laneW - a`.
* `C7all = C7fam ∧ C7Rfam` (family 6), index count `max (cntTerm ..) (cntRef ..)`.
* T4: `C7Rfam_shrink` (accepts at a shrinking level), `C7Rfam_out` (beyond its count), so `C7all ↔ C7fam` at shrinking
  levels and `C7all ↔ C7Rfam` at refresh levels (`C7fam_refresh` of GreedyRefreshGap).
* `C7Rfam_stage`: at a refresh level with true panels, the family passes at every index of the level exactly when the
  stored term table is the table of a refresh choice (`C7Rat_all_iff`).
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

/-- The index geometry of the refresh term slots: `bases * termKeys` slots per level, at the non-shrinking levels. -/
def refDims (D : Dims) : Dims :=
  { D with lv := fun ℓ => { D.lv ℓ with bases := (D.lv ℓ).bases * (D.lv ℓ).termKeys, shrink := !(D.lv ℓ).shrink } }

/-- Number of indices of the refresh part of family 6. -/
def cntRef (D : Dims) : ℕ := cntBase (refDims D)

section Fam

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

/-- **Family 6, refresh part**: C7 (refresh) at the term slot named by the index, at refresh levels. -/
def C7Rfam (Dn : ℕ → Dims) (x u : List Bool) (i : ℕ) : Prop :=
  let D := Dn x.length
  let ℓ := i % 2 ^ levBits D
  let j := i / 2 ^ levBits D
  ShrinkIdx (refDims D) i →
    C7Rat (g := (D.lv ℓ).laneW - a) P hdH hconn F D u ℓ (j / (D.lv ℓ).termKeys) (j % (D.lv ℓ).termKeys)

theorem C7Rfam_out (Dn : ℕ → Dims) (x u : List Bool) {i : ℕ} (hi : cntRef (Dn x.length) ≤ i) :
    C7Rfam P hdH hconn F Dn x u i :=
  fun h => absurd h (not_shrinkIdx_of_ge _ hi)

/-- **T4**: the refresh part accepts at every index of a shrinking level. -/
theorem C7Rfam_shrink (Dn : ℕ → Dims) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = true) : C7Rfam P hdH hconn F Dn x u i := by
  rintro ⟨-, hs, -⟩
  change (!((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink) = true at hs
  rw [h] at hs
  exact absurd hs Bool.false_ne_true

/-- **Family 6 after D15**: C7 at shrinking levels (Sol greedyprog2's `C7fam`) and at refresh levels (`C7Rfam`). -/
def C7all {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ) : Prop :=
  C7fam B Dn ag x u i ∧ C7Rfam P hdH hconn F Dn x u i

/-- Number of indices of family 6 after D15. -/
def cnt7all (D : Dims) (ag : ℕ → ℕ × ℕ) : ℕ := max (cntTerm D ag) (cntRef D)

section All

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
  (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem C7all_out (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {i : ℕ}
    (hi : cnt7all (Dn x.length) (ag x.length) ≤ i) : C7all P hdH hconn F B Dn ag x u i :=
  ⟨C7fam_out B Dn ag x u (le_trans (le_max_left _ _) hi),
    C7Rfam_out P hdH hconn F Dn x u (le_trans (le_max_right _ _) hi)⟩

/-- **T4** at a shrinking level family 6 is the old C7. -/
theorem C7all_shrink_iff (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = true) :
    C7all P hdH hconn F B Dn ag x u i ↔ C7fam B Dn ag x u i :=
  ⟨fun h7 => h7.1, fun h7 => ⟨h7, C7Rfam_shrink P hdH hconn F Dn x u i h⟩⟩

/-- **T4** at a refresh level family 6 is the refresh part. -/
theorem C7all_refresh_iff (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false) :
    C7all P hdH hconn F B Dn ag x u i ↔ C7Rfam P hdH hconn F Dn x u i :=
  ⟨fun h7 => h7.2, fun h7 => ⟨GreedyRefreshGap.C7fam_refresh B Dn ag x u i h, h7⟩⟩

end All

/-- The index of the term slot `(Y, key)` of level `ℓ` in the refresh part. -/
def encRefIdx (D : Dims) (ℓ Y key : ℕ) : ℕ := encIdx D ℓ (key + (D.lv ℓ).termKeys * Y)

/-- **Family 6 (refresh part) at one refresh level** = `C7Rat` at every term slot of the level. -/
theorem C7Rfam_level (Dn : ℕ → Dims) (x u : List Bool) {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top)
    (hs : ((Dn x.length).lv ℓ).shrink = false) :
    (∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < ((Dn x.length).lv ℓ).termKeys,
        C7Rfam P hdH hconn F Dn x u (encRefIdx (Dn x.length) ℓ Y key)) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < ((Dn x.length).lv ℓ).termKeys,
        C7Rat (g := ((Dn x.length).lv ℓ).laneW - a) P hdH hconn F (Dn x.length) u ℓ Y key := by
  apply forall_congr'
  intro Y
  apply forall_congr'
  intro hY
  apply forall_congr'
  intro key
  apply forall_congr'
  intro hk
  have hm : encRefIdx (Dn x.length) ℓ Y key % 2 ^ levBits (Dn x.length) = ℓ := encIdx_mod _ hℓ _
  have hd : encRefIdx (Dn x.length) ℓ Y key / 2 ^ levBits (Dn x.length) =
      key + ((Dn x.length).lv ℓ).termKeys * Y := encIdx_div _ hℓ _
  have hpos : 0 < ((Dn x.length).lv ℓ).termKeys := lt_of_le_of_lt (Nat.zero_le _) hk
  have hq : (key + ((Dn x.length).lv ℓ).termKeys * Y) / ((Dn x.length).lv ℓ).termKeys = Y := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hr : (key + ((Dn x.length).lv ℓ).termKeys * Y) % ((Dn x.length).lv ℓ).termKeys = key := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  unfold C7Rfam
  simp only [hm, hd, hq, hr]
  constructor
  · intro h
    apply h
    refine ⟨?_, ?_, ?_⟩
    · change encRefIdx (Dn x.length) ℓ Y key % 2 ^ levBits (Dn x.length) ≤ (Dn x.length).top
      rw [hm]; exact hℓ
    · change (!((Dn x.length).lv (encRefIdx (Dn x.length) ℓ Y key % 2 ^ levBits (Dn x.length))).shrink) = true
      rw [hm, hs]; rfl
    · change encRefIdx (Dn x.length) ℓ Y key / 2 ^ levBits (Dn x.length) <
        ((Dn x.length).lv (encRefIdx (Dn x.length) ℓ Y key % 2 ^ levBits (Dn x.length))).bases *
          ((Dn x.length).lv (encRefIdx (Dn x.length) ℓ Y key % 2 ^ levBits (Dn x.length))).termKeys
      rw [hm, hd]
      calc key + ((Dn x.length).lv ℓ).termKeys * Y < ((Dn x.length).lv ℓ).termKeys * (Y + 1) := by
            rw [Nat.mul_succ]; omega
        _ ≤ ((Dn x.length).lv ℓ).termKeys * ((Dn x.length).lv ℓ).bases := Nat.mul_le_mul_left _ hY
        _ = _ := Nat.mul_comm _ _
  · intro h _
    exact h

/-- **Family 6 (refresh part), stage form at a refresh level** (true panels of a refresh state `X`): the family passes at
every term slot of the level exactly when the stored term table is the table of a refresh choice. -/
theorem C7Rfam_stage {g : ℕ} (Dn : ℕ → Dims) (x u : List Bool) {ℓ : ℕ} (X : State a (a + g))
    (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = false)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hK : ((Dn x.length).lv ℓ).termKeys = 2 ^ g)
    (hg : ((Dn x.length).lv ℓ).laneW - a = g)
    (hP : ∀ y, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X y) (P1P7.panel X y)) :
    (∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < ((Dn x.length).lv ℓ).termKeys,
        C7Rfam P hdH hconn F Dn x u (encRefIdx (Dn x.length) ℓ Y key)) ↔
      ∃ c : DyadicRefreshChoice X P hdH hconn F, storedTm (Dn x.length) u ℓ X = trueBlockTerms P hdH hconn F X c := by
  rw [C7Rfam_level P hdH hconn F Dn x u hℓ hs, ← C7Rat_all_iff P hdH hconn F (Dn x.length) u ℓ X hP, hg]
  constructor
  · intro h s
    refine h _ (hN ▸ (X.baseIndex s.1).isLt) _ ?_
    rw [hK]
    exact (bitWordFinEquiv g s.2).isLt
  · intro h Y hY key hk
    obtain ⟨y, rfl⟩ := P1ChkFinal.exists_addr_eq X (hN ▸ hY)
    rw [hK] at hk
    have hw : P1ChkFinal.bwNum ((bitWordFinEquiv g).symm ⟨key, hk⟩) = key := by
      unfold P1ChkFinal.bwNum
      rw [Equiv.apply_symm_apply]
    have := h (y, (bitWordFinEquiv g).symm ⟨key, hk⟩)
    rwa [hw] at this

end Fam

end P1ChkFinal.C7R

#print axioms P1ChkFinal.C7R.C7all_out
#print axioms P1ChkFinal.C7R.C7all_refresh_iff
#print axioms P1ChkFinal.C7R.C7Rfam_level
#print axioms P1ChkFinal.C7R.C7Rfam_stage
