import P1ChkFinal.C7RFam

/-!
# P1ChkFinal.GreedyIndex: index conversion of the greedy families at one level (lane P1-lean-greedy)

"All indices `i` with level `i % 2^L = ℓ`" (the D5 quantifier with `lev c i = i % 2^L`) against the level forms of the
stage lemmas (`encIdx`, `encTermIdx`). Generic lemma `level_all_iff` for every family of the shape `ShrinkIdx D' i → Q ..`,
then C5, C6, C8 (`D' = D`) and C7 (`D' = termDims D ag`, `j = key + stride * Y`).
-/

namespace P1ChkFinal.GreedyIndex

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1SolGreedy

/-- **Generic conversion** for a family `ShrinkIdx D' i → Q (level) (rest)` at a shrinking level `ℓ ≤ top`. -/
theorem level_all_iff (D' : Dims) (Q : ℕ → ℕ → Prop) {ℓ : ℕ} (hℓ : ℓ ≤ D'.top) (hs : (D'.lv ℓ).shrink = true) :
    (∀ i, i % 2 ^ levBits D' = ℓ → (ShrinkIdx D' i → Q (i % 2 ^ levBits D') (i / 2 ^ levBits D'))) ↔
      ∀ Y < (D'.lv ℓ).bases, Q ℓ Y := by
  constructor
  · intro h Y hY
    have hm := encIdx_mod D' hℓ Y
    have hd := encIdx_div D' hℓ Y
    have := h (encIdx D' ℓ Y) hm ⟨by rw [hm]; exact hℓ, by rw [hm]; exact hs, by rw [hm, hd]; exact hY⟩
    rwa [hm, hd] at this
  · intro h i hi hS
    rw [hi]
    obtain ⟨-, -, hb⟩ := hS
    rw [hi] at hb
    exact h _ hb

variable (Dn : ℕ → Dims) (x u : List Bool)

theorem C5_all_iff {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C5fam Dn x u i) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, C5fam Dn x u (encIdx (Dn x.length) ℓ Y) :=
  (level_all_iff (Dn x.length) (fun l Y => C5chk (Dn x.length) u l Y) hℓ hs).trans (C5fam_level Dn x u hℓ hs).symm

theorem C6_all_iff (ag : ℕ → ℕ → ℕ × ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top)
    (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C6fam Dn ag x u i) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ Y) :=
  (level_all_iff (Dn x.length) (fun l Y => C6chk (ag x.length l).1 (ag x.length l).2 (Dn x.length) u l Y) hℓ hs).trans
    (C6fam_level Dn ag x u hℓ hs).symm

theorem C9_all_iff {ℓ : ℕ} : (∀ i, i = ℓ → C9fam Dn x u i) ↔ C9fam Dn x u ℓ :=
  ⟨fun h => h ℓ rfl, fun h i hi => hi ▸ h⟩

section Motif

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
  (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem C8_all_iff (ag : ℕ → ℕ → ℕ × ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top)
    (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C8fam B Dn ag x u i) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, C8fam B Dn ag x u (encIdx (Dn x.length) ℓ Y) :=
  (level_all_iff (Dn x.length) (fun l Y => C8chk (ag x.length l).1 (ag x.length l).2 (Dn x.length) u l B
      (DWLocal (a := (ag x.length l).1) (g := (ag x.length l).2) (D := Dn x.length)) Y) hℓ hs).trans
    (forall_congr' fun Y => forall_congr' fun hY => (C8fam_level B Dn ag x u hℓ hs Y hY).symm)

theorem C7_all_iff (ag : ℕ → ℕ → ℕ × ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top)
    (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ i, i % 2 ^ levBits (Dn x.length) = ℓ → C7fam B Dn ag x u i) ↔
      ∀ Y < ((Dn x.length).lv ℓ).bases, ∀ key < termStride (ag x.length) ℓ,
        C7fam B Dn ag x u (encTermIdx (Dn x.length) (ag x.length) ℓ Y key) := by
  have hgen := level_all_iff (termDims (Dn x.length) (ag x.length))
    (fun l j => C7key B (ag x.length l).1 (ag x.length l).2 (Dn x.length) u l
      (j / termStride (ag x.length) l) (j % termStride (ag x.length) l)) hℓ hs
  refine hgen.trans ?_
  have hsd : 0 < termStride (ag x.length) ℓ := termStride_pos _ _
  constructor
  · intro h Y hY key hk
    refine (C7fam_key B Dn ag x u hℓ hs hY hk).mpr ?_
    have hj : key + termStride (ag x.length) ℓ * Y <
        ((Dn x.length).lv ℓ).bases * termStride (ag x.length) ℓ := by
      calc key + termStride (ag x.length) ℓ * Y < termStride (ag x.length) ℓ * (Y + 1) := by
            rw [Nat.mul_succ]; omega
        _ ≤ termStride (ag x.length) ℓ * ((Dn x.length).lv ℓ).bases := Nat.mul_le_mul_left _ hY
        _ = _ := Nat.mul_comm _ _
    have := h _ hj
    simp only [Nat.add_mul_div_left _ _ hsd, Nat.div_eq_of_lt hk, Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk] at this
    exact this
  · intro h j hj
    change j < ((Dn x.length).lv ℓ).bases * termStride (ag x.length) ℓ at hj
    have hY : j / termStride (ag x.length) ℓ < ((Dn x.length).lv ℓ).bases := by
      rw [Nat.div_lt_iff_lt_mul hsd]; exact hj
    have hk : j % termStride (ag x.length) ℓ < termStride (ag x.length) ℓ := Nat.mod_lt _ hsd
    exact (C7fam_key B Dn ag x u hℓ hs hY hk).mp (h _ hY _ hk)

end Motif

end P1ChkFinal.GreedyIndex

#print axioms P1ChkFinal.GreedyIndex.C6_all_iff
#print axioms P1ChkFinal.GreedyIndex.C7_all_iff
#print axioms P1ChkFinal.GreedyIndex.C8_all_iff
