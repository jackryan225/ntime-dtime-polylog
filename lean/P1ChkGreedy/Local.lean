import P1ChkGreedy.Bind

/-!
# P1ChkGreedy.Local: the checks C5 and C9 as tests on the STORED fields only (D5 form, part (b) layer 1)

Lane P1-lean-W2-chkgreedy. G3-chief's D5 interface (board 1548, amendment 1556) asks for each family a Prop
`Ck (fixed data) (x u : List Bool) (i : ℕ)` that a program decides from `x`, `u`, `i` alone. The checks of
`P1ChkGreedy.Bind` refer to the TRUE state `X` (its slot graph gives the neighbours). Here the neighbours are read
from the STORED base records (fields `outAddr`, `inAddr` of P6), as the verifier does:
* `C5chk D u ℓ y`: the stored colour at address `y` is `< 2d+1`, is none of the `2d` masked stored colours of the
  stored neighbour addresses, and every smaller number is one of them (OpenAI's `chooseColor`, later neighbours = 0).
* `C9chk D u ℓ`: the layout field is a bit and equals `decide (E_true(last) < E_false(last))` with the stored energy
  prefixes at the last address `bases - 1`.
LINKS (used in the stage step of `P1Count.stages_iff`, where the base records of level `ℓ` are already true):
`C5chk_iff`: if the stored neighbour addresses at `y` are the true ones, `C5chk D u ℓ (addr y) ↔ C5u D u ℓ X y`;
`C9chk_iff`: if `bases = card X.Base`, `C9chk D u ℓ ↔ C9u D u ℓ X`.
Family form (D5): index `i = ℓ + 2^L y` (`L = clog₂ (top + 1)`); indices that name no base of a shrinking level
accept (`C5fam_out`).
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif

/-! ## C5 on the stored fields -/

/-- The masked stored colour of the base at address `z`, as read from the base at address `y` (bases of larger or
equal address count as `0`; an out-of-range stored colour counts as `0`, as in `colOf`). -/
def mcol (D : P1Wit.Dims) (u : List Bool) (ℓ d y z : ℕ) : ℕ :=
  if z < y then (if P1Wit.rdColour D u ℓ z < 2 * d + 1 then P1Wit.rdColour D u ℓ z else 0) else 0

/-- The `2d` values that C5 reads at address `y`: out-neighbours by slot, then in-neighbours by slot. -/
def c5vals (D : P1Wit.Dims) (u : List Bool) (ℓ y : ℕ) : List ℕ :=
  (List.range (D.lv ℓ).slots).map (fun k => mcol D u ℓ (D.lv ℓ).slots y (P1Wit.rdOutAddr D u ℓ y k)) ++
    (List.range (D.lv ℓ).slots).map (fun k => mcol D u ℓ (D.lv ℓ).slots y (P1Wit.rdInAddr D u ℓ y k))

/-- **C5 on the stored fields** at address `y` of level `ℓ`. -/
def C5chk (D : P1Wit.Dims) (u : List Bool) (ℓ y : ℕ) : Prop :=
  P1Wit.rdColour D u ℓ y < 2 * (D.lv ℓ).slots + 1 ∧
    P1Wit.rdColour D u ℓ y ∉ c5vals D u ℓ y ∧
    ∀ k < P1Wit.rdColour D u ℓ y, k ∈ c5vals D u ℓ y

instance (D : P1Wit.Dims) (u : List Bool) (ℓ y : ℕ) : Decidable (C5chk D u ℓ y) := by
  unfold C5chk; infer_instance

section C5Link

variable {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

theorem mcol_eq (X : State a (packingLaneBits a g)) (y z : X.Base) :
    mcol D u ℓ (2 ^ a) (P1P7.addr X y) (P1P7.addr X z) =
      (masked X.baseIndex 0 (colOf D u ℓ X) y z).val := by
  unfold mcol masked colOf finOr0 P1P7.addr
  by_cases h1 : X.baseIndex z < X.baseIndex y
  · have h1' : (X.baseIndex z : ℕ) < X.baseIndex y := Fin.lt_def.mp h1
    simp only [h1, h1', ↓reduceIte]
    split_ifs <;> simp
  · have h1' : ¬ (X.baseIndex z : ℕ) < X.baseIndex y := fun h => h1 (Fin.lt_def.mpr h)
    simp [h1, h1']

/-- The values read by `C5chk` are exactly the values `colorForbidden` of OpenAI's rule on the decoded table. -/
theorem mem_c5vals (X : State a (packingLaneBits a g)) (y : X.Base) (hd : (D.lv ℓ).slots = 2 ^ a)
    (hout : ∀ k : Fin (2 ^ a), P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) k = (P1P7.outNbr X y k).1)
    (hin : ∀ k : Fin (2 ^ a), P1Wit.rdInAddr D u ℓ (P1P7.addr X y) k = (P1P7.inNbr X y k).1) (v : ℕ) :
    v ∈ c5vals D u ℓ (P1P7.addr X y) ↔
      ∃ t, (X.slots.base.colorForbidden y (masked X.baseIndex 0 (colOf D u ℓ X) y) t : ℕ) = v := by
  unfold c5vals
  rw [hd]
  simp only [List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · refine ⟨(true, ⟨k, hk⟩), ?_⟩
      have h : P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) k = (P1P7.outNbr X y ⟨k, hk⟩).1 := hout ⟨k, hk⟩
      rw [h]
      exact (mcol_eq D u ℓ X y (X.slots.base.target (y, ⟨k, hk⟩)).1).symm
    · refine ⟨(false, ⟨k, hk⟩), ?_⟩
      have h : P1Wit.rdInAddr D u ℓ (P1P7.addr X y) k = (P1P7.inNbr X y ⟨k, hk⟩).1 := hin ⟨k, hk⟩
      rw [h]
      exact (mcol_eq D u ℓ X y (X.slots.base.target.symm (y, ⟨k, hk⟩)).1).symm
  · rintro ⟨⟨b, i⟩, rfl⟩
    cases b with
    | true =>
      left
      refine ⟨i.val, i.isLt, ?_⟩
      rw [hout i]
      exact mcol_eq D u ℓ X y (X.slots.base.target (y, i)).1
    | false =>
      right
      refine ⟨i.val, i.isLt, ?_⟩
      rw [hin i]
      exact mcol_eq D u ℓ X y (X.slots.base.target.symm (y, i)).1

/-- **Link C5.** If the stored neighbour addresses of `y` are the true ones, the test on the stored fields is the
check `C5u` of `P1ChkGreedy.Bind`. -/
theorem C5chk_iff (X : State a (packingLaneBits a g)) (y : X.Base) (hd : (D.lv ℓ).slots = 2 ^ a)
    (hout : ∀ k : Fin (2 ^ a), P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) k = (P1P7.outNbr X y k).1)
    (hin : ∀ k : Fin (2 ^ a), P1Wit.rdInAddr D u ℓ (P1P7.addr X y) k = (P1P7.inNbr X y k).1) :
    C5chk D u ℓ (P1P7.addr X y) ↔ C5u D u ℓ X y := by
  have hm := mem_c5vals D u ℓ X y hd hout hin
  unfold C5chk C5u C5s
  rw [hd, C5_iff_least]
  apply and_congr_right
  intro hr
  have hcol : (colOf D u ℓ X y : ℕ) = P1Wit.rdColour D u ℓ (P1P7.addr X y) := finOr0_val hr
  apply and_congr
  · rw [hm]
    constructor
    · intro h t ht
      exact h ⟨t, by rw [← ht, hcol]⟩
    · rintro h ⟨t, ht⟩
      apply h t
      apply Fin.ext
      rw [hcol, ht]
  · constructor
    · intro h k hk
      have hk' : (k : ℕ) < P1Wit.rdColour D u ℓ (P1P7.addr X y) := by
        rw [← hcol]
        exact Fin.lt_def.mp hk
      obtain ⟨t, ht⟩ := (hm k).mp (h k hk')
      exact ⟨t, Fin.ext ht⟩
    · intro h k hk
      have hk2 : k < 2 * 2 ^ a + 1 := lt_trans hk hr
      obtain ⟨t, ht⟩ := h ⟨k, hk2⟩ (by rw [Fin.lt_def, hcol]; exact hk)
      exact (hm k).mpr ⟨t, by rw [ht]⟩

end C5Link

/-! ## C9 on the stored fields -/

/-- **C9 on the stored fields** (one per shrinking level): the layout field is a bit and agrees with the stored
energy prefixes at the last address `bases - 1` (ties give `0`, paper layout 1). -/
def C9chk (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) : Prop :=
  P1Wit.rdLayout D u ℓ < 2 ∧
    decide (P1Wit.rdLayout D u ℓ = 1) =
      decide (P1Wit.rdEnergy D u ℓ ((D.lv ℓ).bases - 1) (eCode true) <
        P1Wit.rdEnergy D u ℓ ((D.lv ℓ).bases - 1) (eCode false))

instance (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) : Decidable (C9chk D u ℓ) := by
  unfold C9chk; infer_instance

theorem addr_lastBase {a g : ℕ} (X : State a (packingLaneBits a g)) : P1P7.addr X (lastBase X) = Fintype.card X.Base - 1 := by
  simp [P1P7.addr, lastBase]

/-- **Link C9.** -/
theorem C9chk_iff {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (hN : (D.lv ℓ).bases = Fintype.card X.Base) : C9chk D u ℓ ↔ C9u D u ℓ X := by
  unfold C9chk C9u C9 EOf
  rw [addr_lastBase, hN]

/-! ## Family form of D5: index `i = ℓ + 2^L y` -/

/-- Bits of the level part of an index. -/
def levBits (D : P1Wit.Dims) : ℕ := Nat.clog 2 (D.top + 1)

/-- The index of base address `y` of level `ℓ`. -/
def encIdx (D : P1Wit.Dims) (ℓ y : ℕ) : ℕ := ℓ + 2 ^ levBits D * y

theorem lev_lt (D : P1Wit.Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) : ℓ < 2 ^ levBits D :=
  lt_of_lt_of_le (Nat.lt_succ_of_le hℓ) (Nat.le_pow_clog (by norm_num) _)

theorem encIdx_mod (D : P1Wit.Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) (y : ℕ) :
    encIdx D ℓ y % 2 ^ levBits D = ℓ := by
  unfold encIdx
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lev_lt D hℓ)]

theorem encIdx_div (D : P1Wit.Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) (y : ℕ) :
    encIdx D ℓ y / 2 ^ levBits D = y := by
  unfold encIdx
  have hp : 0 < 2 ^ levBits D := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (lev_lt D hℓ), Nat.zero_add]

/-- An index names a base of a shrinking level. -/
def ShrinkIdx (D : P1Wit.Dims) (i : ℕ) : Prop :=
  i % 2 ^ levBits D ≤ D.top ∧ (D.lv (i % 2 ^ levBits D)).shrink = true ∧
    i / 2 ^ levBits D < (D.lv (i % 2 ^ levBits D)).bases

/-- The largest number of bases of a level. -/
def maxBases (D : P1Wit.Dims) : ℕ := ((List.range (D.top + 1)).map fun ℓ => (D.lv ℓ).bases).foldr max 0

theorem bases_le_maxBases (D : P1Wit.Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) : (D.lv ℓ).bases ≤ maxBases D := by
  unfold maxBases
  have hmem : (D.lv ℓ).bases ∈ (List.range (D.top + 1)).map fun ℓ => (D.lv ℓ).bases :=
    List.mem_map.mpr ⟨ℓ, List.mem_range.mpr (Nat.lt_succ_of_le hℓ), rfl⟩
  generalize (List.range (D.top + 1)).map (fun ℓ => (D.lv ℓ).bases) = l at hmem ⊢
  induction l with
  | nil => simp at hmem
  | cons b l ih =>
    rcases List.mem_cons.mp hmem with h | h
    · rw [h, List.foldr_cons]
      exact le_max_left _ _
    · rw [List.foldr_cons]
      exact le_trans (ih h) (le_max_right _ _)

/-- Number of indices of the families C5, C6, C8 at an input length (`D = Dn n`). -/
def cntBase (D : P1Wit.Dims) : ℕ := 2 ^ levBits D * maxBases D

/-- **Family C5** (D5 number 4): the index names a base of a shrinking level (else it accepts) and C5 passes there. -/
def C5fam (Dn : ℕ → P1Wit.Dims) (x u : List Bool) (i : ℕ) : Prop :=
  ShrinkIdx (Dn x.length) i →
    C5chk (Dn x.length) u (i % 2 ^ levBits (Dn x.length)) (i / 2 ^ levBits (Dn x.length))

theorem not_shrinkIdx_of_ge (D : P1Wit.Dims) {i : ℕ} (hi : cntBase D ≤ i) : ¬ ShrinkIdx D i := by
  rintro ⟨hℓ, -, hy⟩
  have h1 := bases_le_maxBases D hℓ
  have hp : 0 < 2 ^ levBits D := Nat.two_pow_pos _
  have h2 : maxBases D ≤ i / 2 ^ levBits D := by
    rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm]
    exact hi
  omega

theorem C5fam_out (Dn : ℕ → P1Wit.Dims) (x u : List Bool) {i : ℕ} (hi : cntBase (Dn x.length) ≤ i) :
    C5fam Dn x u i := fun h => absurd h (not_shrinkIdx_of_ge _ hi)

/-- **Family C5 at one shrinking level** = C5 on the stored fields at every base address. -/
theorem C5fam_level (Dn : ℕ → P1Wit.Dims) (x u : List Bool) {ℓ : ℕ} (hℓ : ℓ ≤ (Dn x.length).top)
    (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ y < ((Dn x.length).lv ℓ).bases, C5fam Dn x u (encIdx (Dn x.length) ℓ y)) ↔
      ∀ y < ((Dn x.length).lv ℓ).bases, C5chk (Dn x.length) u ℓ y := by
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  unfold C5fam ShrinkIdx
  rw [encIdx_mod _ hℓ, encIdx_div _ hℓ]
  exact ⟨fun h => h ⟨hℓ, hs, hy⟩, fun h _ => h⟩

/-- Number of indices of the family C9 (one per level). -/
def cntLev (D : P1Wit.Dims) : ℕ := D.top + 1

/-- **Family C9** (D5 number 8): index `i` = level; non-shrinking levels and `i > top` accept. -/
def C9fam (Dn : ℕ → P1Wit.Dims) (x u : List Bool) (i : ℕ) : Prop :=
  (i ≤ (Dn x.length).top ∧ ((Dn x.length).lv i).shrink = true) → C9chk (Dn x.length) u i

theorem C9fam_out (Dn : ℕ → P1Wit.Dims) (x u : List Bool) {i : ℕ} (hi : cntLev (Dn x.length) ≤ i) :
    C9fam Dn x u i := fun h => absurd h.1 (by unfold cntLev at hi; omega)

end P1ChkGreedy
