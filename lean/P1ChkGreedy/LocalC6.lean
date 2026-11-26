import P1ChkGreedy.Local

/-!
# P1ChkGreedy.LocalC6: check C6 (greedy tag offsets) on the STORED fields (D5 form, part (b) layer 1)

Lane P1-lean-W2-chkgreedy. OpenAI's rule `chooseTag` (SlotGreedyScan.lean:218) at base `y` reads the
`2d((d+1)+(d+1)^2)` values `tagForbidden τ y f t` (l.206), where `τ` is the tag part of the lane displacement of a base
arc (`tagShift`, PackingLanes.lean:78) and `f` the offsets with later neighbours read as `0`. On the stored fields:
displacements are read from the base records (P6 fields `outDisp`, `inDisp`, numbers `bitWordFinEquiv` of the
displacement word), neighbours from `outAddr`, `inAddr`, offsets from `offset`. The level parameters `a`, `g` (the
level is an OpenAI `State a (packingLaneBits a g)`) are fixed data.
`RecTrue D u ℓ X`: the four base-record families of level `ℓ` hold the true values (what C4/C10 give in the stage
order). LINK `C6chk_iff`: under `RecTrue`, `C6chk a g D u ℓ (addr y) ↔ C6u D u ℓ X y`; `C5chk_iff'` likewise for C5.
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression

section C6Stored

variable (a g : ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- Tag part of a stored displacement number (`packingFields`: colour bits, slot label, TAG, remaining lane). -/
def tagOfDisp (v : ℕ) : BitWord (packingTagBits (2 ^ a)) :=
  (packingFields a g ((bitWordFinEquiv (packingLaneBits a g)).symm (finOr0 _ v))).2.2.1

/-- `τ` of out-slot `k` of the base at address `Z`, from the stored base record. -/
def tauOut (Z k : ℕ) : BitWord (packingTagBits (2 ^ a)) := tagOfDisp a g (P1Wit.rdOutDisp D u ℓ Z k)

/-- `τ` of the arc that enters in-slot `k` of the base at address `Z`. -/
def tauIn (Z k : ℕ) : BitWord (packingTagBits (2 ^ a)) := tagOfDisp a g (P1Wit.rdInDisp D u ℓ Z k)

/-- OpenAI's `tagIncrement` on the stored records. -/
def incS (Z : ℕ) : Option (Fin (2 ^ a)) → BitWord (packingTagBits (2 ^ a))
  | none => 0
  | some j => tauOut a g D u ℓ Z j

/-- Masked stored offset of the base at address `Z`, read from the base at address `Y`. -/
def moff (Y Z : ℕ) : BitWord (packingTagBits (2 ^ a)) :=
  if Z < Y then (bitWordFinEquiv (packingTagBits (2 ^ a))).symm (finOr0 _ (P1Wit.rdOffset D u ℓ Z)) else 0

/-- The forbidden tags of OpenAI's `tagForbidden`, computed from the stored fields at address `Y`. -/
def forbS (Y : ℕ) : SlotGraph.TagTests (2 ^ a) → BitWord (packingTagBits (2 ^ a))
  | ((true, i), .inl o) => tauOut a g D u ℓ Y i + incS a g D u ℓ Y o
  | ((false, i), .inl o) => tauIn a g D u ℓ Y i + incS a g D u ℓ Y o
  | ((true, i), .inr (o1, o2)) =>
    tauOut a g D u ℓ Y i + incS a g D u ℓ Y o1 + incS a g D u ℓ (P1Wit.rdOutAddr D u ℓ Y i) o2 -
      moff a D u ℓ Y (P1Wit.rdOutAddr D u ℓ Y i)
  | ((false, i), .inr (o1, o2)) =>
    tauIn a g D u ℓ Y i + incS a g D u ℓ (P1Wit.rdInAddr D u ℓ Y i) o1 + incS a g D u ℓ Y o2 -
      moff a D u ℓ Y (P1Wit.rdInAddr D u ℓ Y i)

/-- **C6 on the stored fields** at address `Y` of level `ℓ`: the stored offset number is a tag, is none of the
forbidden tag numbers, and every smaller number is one of them. -/
def C6chk (Y : ℕ) : Prop :=
  P1Wit.rdOffset D u ℓ Y < 2 ^ packingTagBits (2 ^ a) ∧
    (∀ t, P1Wit.rdOffset D u ℓ Y ≠ (bitWordFinEquiv _ (forbS a g D u ℓ Y t) : ℕ)) ∧
    ∀ k < P1Wit.rdOffset D u ℓ Y, ∃ t, (bitWordFinEquiv _ (forbS a g D u ℓ Y t) : ℕ) = k

instance (Y : ℕ) : Decidable (C6chk a g D u ℓ Y) := by
  unfold C6chk; infer_instance

end C6Stored

section C6Link

variable {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- The stored base records of level `ℓ` (neighbour addresses and displacements, both directions) are the true ones
of the state `X`. -/
def RecTrue (X : State a (packingLaneBits a g)) : Prop :=
  ∀ (z : X.Base) (k : Fin (2 ^ a)),
    P1Wit.rdOutAddr D u ℓ (P1P7.addr X z) k = (P1P7.outNbr X z k).1 ∧
    P1Wit.rdInAddr D u ℓ (P1P7.addr X z) k = (P1P7.inNbr X z k).1 ∧
    P1Wit.rdOutDisp D u ℓ (P1P7.addr X z) k = (bitWordFinEquiv _ (P1P7.outNbr X z k).2 : ℕ) ∧
    P1Wit.rdInDisp D u ℓ (P1P7.addr X z) k = (bitWordFinEquiv _ (P1P7.inNbr X z k).2 : ℕ)

theorem tagOfDisp_true (w : BitWord (packingLaneBits a g)) :
    tagOfDisp a g (bitWordFinEquiv _ w : ℕ) = (packingFields a g w).2.2.1 := by
  unfold tagOfDisp
  have h : finOr0 _ (bitWordFinEquiv _ w : ℕ) = bitWordFinEquiv _ w := ((finOr0_eq_iff _ _).mpr rfl).2
  rw [h, Equiv.symm_apply_apply]

variable {D u ℓ}

theorem tauOut_eq {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (z : X.Base) (k : Fin (2 ^ a)) :
    tauOut a g D u ℓ (P1P7.addr X z) k = tagShift X (z, k) := by
  unfold tauOut
  rw [(h z k).2.2.1]
  exact tagOfDisp_true _

theorem tauIn_eq {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (z : X.Base) (k : Fin (2 ^ a)) :
    tauIn a g D u ℓ (P1P7.addr X z) k = tagShift X (X.slots.base.target.symm (z, k)) := by
  unfold tauIn
  rw [(h z k).2.2.2]
  exact tagOfDisp_true _

theorem incS_eq {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (z : X.Base) (o : Option (Fin (2 ^ a))) :
    incS a g D u ℓ (P1P7.addr X z) o = tagIncrement (tagShift X) z o := by
  cases o with
  | none => rfl
  | some j => exact tauOut_eq h z j

theorem moff_eq (X : State a (packingLaneBits a g)) (y z : X.Base) :
    moff a D u ℓ (P1P7.addr X y) (P1P7.addr X z) = masked X.baseIndex 0 (offOf D u ℓ X) y z := by
  unfold moff masked offOf P1P7.addr
  by_cases h1 : X.baseIndex z < X.baseIndex y
  · rw [if_pos (Fin.lt_def.mp h1), if_pos h1]
  · rw [if_neg (fun h => h1 (Fin.lt_def.mpr h)), if_neg h1]

/-- Under `RecTrue`, the stored forbidden list is OpenAI's `tagForbidden` on the decoded offsets. -/
theorem forbS_eq {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (y : X.Base)
    (t : SlotGraph.TagTests (2 ^ a)) :
    forbS a g D u ℓ (P1P7.addr X y) t =
      X.slots.base.tagForbidden (tagShift X) y (masked X.baseIndex 0 (offOf D u ℓ X) y) t := by
  obtain ⟨⟨b, i⟩, r⟩ := t
  cases b with
  | true =>
    rcases r with o | ⟨o1, o2⟩
    · show tauOut a g D u ℓ (P1P7.addr X y) i + incS a g D u ℓ (P1P7.addr X y) o = _
      rw [tauOut_eq h, incS_eq h]
      rfl
    · have hz : P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) i = P1P7.addr X (X.slots.base.target (y, i)).1 :=
        (h y i).1
      show tauOut a g D u ℓ (P1P7.addr X y) i + incS a g D u ℓ (P1P7.addr X y) o1 +
          incS a g D u ℓ (P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) i) o2 -
          moff a D u ℓ (P1P7.addr X y) (P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) i) = _
      rw [hz, tauOut_eq h, incS_eq h, incS_eq h, moff_eq]
      rfl
  | false =>
    rcases r with o | ⟨o1, o2⟩
    · show tauIn a g D u ℓ (P1P7.addr X y) i + incS a g D u ℓ (P1P7.addr X y) o = _
      rw [tauIn_eq h, incS_eq h]
      rfl
    · have hz : P1Wit.rdInAddr D u ℓ (P1P7.addr X y) i =
          P1P7.addr X (X.slots.base.target.symm (y, i)).1 := (h y i).2.1
      show tauIn a g D u ℓ (P1P7.addr X y) i + incS a g D u ℓ (P1Wit.rdInAddr D u ℓ (P1P7.addr X y) i) o1 +
          incS a g D u ℓ (P1P7.addr X y) o2 -
          moff a D u ℓ (P1P7.addr X y) (P1Wit.rdInAddr D u ℓ (P1P7.addr X y) i) = _
      rw [hz, tauIn_eq h, incS_eq h, incS_eq h, moff_eq]
      rfl

/-- **Link C6.** Under `RecTrue`, the test on the stored fields is the check `C6u` of `P1ChkGreedy.Bind`. -/
theorem C6chk_iff {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (y : X.Base) :
    C6chk a g D u ℓ (P1P7.addr X y) ↔ C6u D u ℓ X y := by
  have hf := forbS_eq h y
  unfold C6chk C6u C6s
  rw [C6_iff_least]
  apply and_congr_right
  intro hr
  have hidx : (bitWordFinEquiv _ (offOf D u ℓ X y) : ℕ) = P1Wit.rdOffset D u ℓ (P1P7.addr X y) := by
    unfold offOf
    rw [Equiv.apply_symm_apply]
    exact finOr0_val hr
  simp only [hf]
  apply and_congr
  · apply forall_congr'
    intro t
    rw [← hidx]
    exact ⟨fun h1 e => h1 (congrArg Fin.val e), fun h1 e => h1 (Fin.ext e)⟩
  · constructor
    · intro h1 k hk
      have hk' : (k : ℕ) < P1Wit.rdOffset D u ℓ (P1P7.addr X y) := by
        rw [← hidx]
        exact Fin.lt_def.mp hk
      obtain ⟨t, ht⟩ := h1 k hk'
      exact ⟨t, Fin.ext ht⟩
    · intro h1 k hk
      have hk2 : k < 2 ^ packingTagBits (2 ^ a) := lt_trans hk hr
      obtain ⟨t, ht⟩ := h1 ⟨k, hk2⟩ (by rw [Fin.lt_def, hidx]; exact hk)
      exact ⟨t, by rw [ht]⟩

/-- **Link C5** with the hypothesis `RecTrue`. -/
theorem C5chk_iff' {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X) (hd : (D.lv ℓ).slots = 2 ^ a)
    (y : X.Base) : C5chk D u ℓ (P1P7.addr X y) ↔ C5u D u ℓ X y :=
  C5chk_iff D u ℓ X y hd (fun k => (h y k).1) (fun k => (h y k).2.1)

end C6Link

/-! ## Family C6 (D5 number 5) -/

/-- **Family C6**: `ag n ℓ = (a, g)` are the OpenAI parameters of level `ℓ` at input length `n` (fixed data). -/
def C6fam (Dn : ℕ → P1Wit.Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ) : Prop :=
  ShrinkIdx (Dn x.length) i →
    C6chk (ag x.length (i % 2 ^ levBits (Dn x.length))).1 (ag x.length (i % 2 ^ levBits (Dn x.length))).2
      (Dn x.length) u (i % 2 ^ levBits (Dn x.length)) (i / 2 ^ levBits (Dn x.length))

theorem C6fam_out (Dn : ℕ → P1Wit.Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {i : ℕ}
    (hi : cntBase (Dn x.length) ≤ i) : C6fam Dn ag x u i :=
  fun h => absurd h (not_shrinkIdx_of_ge _ hi)

theorem C6fam_level (Dn : ℕ → P1Wit.Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ : ℕ}
    (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = true) :
    (∀ y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ y)) ↔
      ∀ y < ((Dn x.length).lv ℓ).bases,
        C6chk (ag x.length ℓ).1 (ag x.length ℓ).2 (Dn x.length) u ℓ y := by
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  unfold C6fam ShrinkIdx
  rw [encIdx_mod _ hℓ, encIdx_div _ hℓ]
  exact ⟨fun h => h ⟨hℓ, hs, hy⟩, fun h _ => h⟩

end P1ChkGreedy
