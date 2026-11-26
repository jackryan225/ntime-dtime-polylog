import P1P7.ShrinkBase

/-!
# P7, shrink half, layer 2: lane-zero IDs, their keys, and the transport of slot ranks

The new slot graph of a shrinking substep (`X.shrinkStateIndex ready layout`, ShrinkStatePass.lean:38) numbers the
lane-zero IDs `Id X.packingData.BaseMotif subdiv` at each packed base by OpenAI's mixed-radix keys
(`slotIdentifier`, SlotIdentifierOrder.lean:48). OpenAI's `paddedSlot_numbers` (SlotRegularization.lean:133) says that
the slot number of an ID is the number of smaller IDs at the same endpoint. Here:
* `okey`: a canonical key (independent of the number of bases) whose lexicographic order is OpenAI's order;
* `tId`: the partner ID in the other state (old base replaced by its partner);
* `rank_transport`: equal key sets give equal ranks;
* `out_rank`, `in_rank`: OpenAI's slot numbers as ranks of `okey`.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBaseIds {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

/-! ## Ranks transported along key-preserving partners (pure combinatorics) -/

section Rank

theorem card_filter_key_lt {E K : Type*} [LinearOrder K] (s : Finset E) (key : E → K)
    (hinj : Set.InjOn key s) (κ : K) :
    (s.filter (fun z => key z < κ)).card = ((s.image key).filter (· < κ)).card := by
  rw [Finset.filter_image,
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

theorem image_key_eq {E E' K : Type*} [LinearOrder K] (s : Finset E) (s' : Finset E')
    (key : E → K) (key' : E' → K) (hinj : Set.InjOn key s) (hinj' : Set.InjOn key' s')
    (hcard : s'.card ≤ s.card) (hpart : ∀ e ∈ s, ∃ e' ∈ s', key' e' = key e) :
    s.image key = s'.image key' := by
  have hsub : s.image key ⊆ s'.image key' := by
    intro κ hκ
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hκ
    obtain ⟨e', he', hk⟩ := hpart e he
    exact Finset.mem_image.mpr ⟨e', he', hk⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injOn hinj', Finset.card_image_of_injOn hinj]
  exact hcard

/-- Ranks are transported along a key-preserving partner relation between two finite sets of equal size. -/
theorem rank_transport {E E' K : Type*} [LinearOrder K] (s : Finset E) (s' : Finset E')
    (key : E → K) (key' : E' → K) (hinj : Set.InjOn key s) (hinj' : Set.InjOn key' s')
    (hcard : s'.card ≤ s.card) (hpart : ∀ e ∈ s, ∃ e' ∈ s', key' e' = key e) (κ : K) :
    (s.filter (fun z => key z < κ)).card = (s'.filter (fun z => key' z < κ)).card := by
  rw [card_filter_key_lt s key hinj, card_filter_key_lt s' key' hinj',
    image_key_eq s s' key key' hinj hinj' hcard hpart]

/-- Mixed radix with a top digit is lexicographic. -/
theorem nat_lex {M t1 t2 i1 i2 : ℕ} (h1 : i1 < M) (h2 : i2 < M) :
    i1 + M * t1 < i2 + M * t2 ↔ t1 < t2 ∨ (t1 = t2 ∧ i1 < i2) := by
  constructor
  · intro h
    rcases lt_trichotomy t1 t2 with ht | ht | ht
    · exact Or.inl ht
    · subst ht; exact Or.inr ⟨rfl, Nat.lt_of_add_lt_add_right h⟩
    · exfalso
      have h3 : M * t2 + M ≤ M * t1 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left M ht
      linarith
  · rintro (ht | ⟨rfl, hi⟩)
    · have h3 : M * t1 + M ≤ M * t2 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left M ht
      linarith
    · exact Nat.add_lt_add_right hi _

end Rank

/-! ## Partner IDs -/

section Ids

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)} {subdiv : Fin 4 → ℕ}

/-- The motif condition of the transported arc in `X'`. -/
abbrev MotifT (X X' : State a (packingLaneBits a g))
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) : Prop :=
  ¬ (X'.packingData.thick (sourcePosition (tA X X' α)) ∧
    X'.packingData.thick (sourcePosition (X'.packingData.actual (tA X X' α))))

/-- The partner of a lane-zero ID: same type, same subdivision, transported wire. -/
noncomputable def tId (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv)
    (hm : MotifT X X' z.2.1.1.val) : SurvivingSlots.Id X'.packingData.BaseMotif subdiv :=
  ⟨z.1, (⟨⟨tA X X' z.2.1.1.val, hm⟩, z.2.1.2⟩, z.2.2)⟩

theorem roleBase_tId (layout : Bool) (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv)
    (hm : MotifT X X' z.2.1.1.val) (h : EndsGood X X' z.2.1.1.val) (r : PackedRole) :
    X'.packingData.roleBase layout r (tId z hm).2.1 = tB X X' (X.packingData.roleBase layout r z.2.1) :=
  congrArg packedBase (survivingRole_tA layout r z.2.1.1 ⟨tA X X' z.2.1.1.val, hm⟩ rfl h)

theorem endpoint_tId (layout : Bool) (pick : Fin 4 → PackedRole)
    (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv)
    (hm : MotifT X X' z.2.1.1.val) (h : EndsGood X X' z.2.1.1.val) :
    endpoint (X'.packingData.roleBase layout) pick (tId z hm) =
      tB X X' (endpoint (X.packingData.roleBase layout) pick z) :=
  roleBase_tId layout z hm h (pick z.1)

theorem roleDisplacement_tId (layout : Bool) (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv)
    (hm : MotifT X X' z.2.1.1.val) (h : EndsGood X X' z.2.1.1.val) :
    X'.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) (tId z hm) =
      X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) z := by
  have h1 := survivingRole_tA layout (targetRole layout z.1) z.2.1.1 ⟨tA X X' z.2.1.1.val, hm⟩ rfl h
  have h2 := survivingRole_tA layout (sourceRole layout z.1) z.2.1.1 ⟨tA X X' z.2.1.1.val, hm⟩ rfl h
  show (X'.packingData.survivingRole layout (targetRole layout z.1) ⟨tA X X' z.2.1.1.val, hm⟩).2.2 -
      (X'.packingData.survivingRole layout (sourceRole layout z.1) ⟨tA X X' z.2.1.1.val, hm⟩).2.2 = _
  rw [h1, h2]
  rfl

end Ids

/-! ## Keys -/

section Keys

variable {a g : ℕ}

/-- OpenAI's base-motif key (`baseMotifIndex`, SlotIdentifierOrder.lean:29) as a natural number: address of the wire's
source base, tag, out-slot, colour bits, slot label. It does not depend on the number of bases. -/
def arcKey (X : State a (packingLaneBits a g))
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) : ℕ :=
  (((addr X α.1.1.1 * 2 ^ packingTagBits (2 ^ a) +
    (bitWordFinEquiv (packingTagBits (2 ^ a)) α.1.1.2.1).val) * 2 ^ a + α.1.2.val) *
      2 ^ (2 * 2 ^ a + 1) + (bitWordFinEquiv (2 * 2 ^ a + 1) α.2.1).val) * 2 ^ a +
        (X.packingData.slotLabel α.2.2).val

theorem baseMotifIndex_val (X : State a (packingLaneBits a g)) (bm : X.packingData.BaseMotif) :
    (X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) bm).val =
      arcKey X bm.1.1 := by
  simp only [PackingData.baseMotifIndex, finProdFinEquiv_apply_val, arcKey, addr]
  ring

theorem arcKey_tA {X X' : State a (packingLaneBits a g)}
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (h : addr X' (pb X X' α.1.1.1) = addr X α.1.1.1) :
    arcKey X' (tA X X' α) = arcKey X α := by
  unfold arcKey
  rw [show addr X' (tA X X' α).1.1.1 = addr X α.1.1.1 from h]
  rfl

variable (subdiv : Fin 4 → ℕ)

/-- The canonical key of a lane-zero ID: (type, subdivision index + S * arc key), lexicographic. -/
def okey (X : State a (packingLaneBits a g)) (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv) :
    ℕ ×ₗ ℕ :=
  toLex (z.1.val, z.2.2.val + (∑ t, subdiv t) * arcKey X z.2.1.1.val)

theorem okey_tId {X X' : State a (packingLaneBits a g)} (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv)
    (hm : MotifT X X' z.2.1.1.val) (h : addr X' (pb X X' z.2.1.1.val.1.1.1) = addr X z.2.1.1.val.1.1.1) :
    okey subdiv X' (tId z hm) = okey subdiv X z := by
  unfold okey
  rw [show arcKey X' (tId z hm).2.1.1.val = arcKey X z.2.1.1.val from arcKey_tA z.2.1.1.val h]
  rfl

theorem slotIdentifier_val (X : State a (packingLaneBits a g))
    (z : SurvivingSlots.Id X.packingData.BaseMotif subdiv) :
    ∃ M : ℕ, (z.2.2.val + (∑ t, subdiv t) * arcKey X z.2.1.1.val) < M ∧ ∀ z2 :
      SurvivingSlots.Id X.packingData.BaseMotif subdiv,
      (z2.2.2.val + (∑ t, subdiv t) * arcKey X z2.2.1.1.val) < M ∧
      (X.packingData.slotIdentifier X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv z2).val =
        (z2.2.2.val + (∑ t, subdiv t) * arcKey X z2.2.1.1.val) + M * z2.1.val := by
  have key : ∀ z2 : SurvivingSlots.Id X.packingData.BaseMotif subdiv,
      (z2.2.2.val + (∑ t, subdiv t) * arcKey X z2.2.1.1.val) <
        (Fintype.card X.Base * (2 ^ packingTagBits (2 ^ a) * (2 ^ a * (2 ^ (2 * 2 ^ a + 1) * 2 ^ a)))) *
          ∑ t, subdiv t ∧
      (X.packingData.slotIdentifier X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv z2).val =
        (z2.2.2.val + (∑ t, subdiv t) * arcKey X z2.2.1.1.val) +
          ((Fintype.card X.Base * (2 ^ packingTagBits (2 ^ a) * (2 ^ a * (2 ^ (2 * 2 ^ a + 1) * 2 ^ a)))) *
            ∑ t, subdiv t) * z2.1.val := by
    intro z2
    have hb := baseMotifIndex_val X z2.2.1
    let inner := finProdFinEquiv
      (X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) z2.2.1,
        Fin.castLE (Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ z2.1)) z2.2.2)
    have hin : (inner : ℕ) = z2.2.2.val + (∑ t, subdiv t) * arcKey X z2.2.1.1.val := by
      simp only [inner, finProdFinEquiv_apply_val, Fin.coe_castLE, hb]
    refine ⟨by rw [← hin]; exact inner.isLt, ?_⟩
    simp only [PackingData.slotIdentifier, finProdFinEquiv_apply_val, Fin.coe_castLE, hb]
  exact ⟨_, (key z).1, key⟩

/-- OpenAI's order of lane-zero IDs (`slotIdentifierOrder`) is the lexicographic order of `okey`. -/
theorem id_lt_iff (X : State a (packingLaneBits a g))
    (z1 z2 : SurvivingSlots.Id X.packingData.BaseMotif subdiv) :
    (X.packingData.slotIdentifier X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv z1).val <
        (X.packingData.slotIdentifier X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv z2).val ↔
      okey subdiv X z1 < okey subdiv X z2 := by
  obtain ⟨M, -, hM⟩ := slotIdentifier_val subdiv X z1
  rw [(hM z1).2, (hM z2).2, nat_lex (hM z1).1 (hM z2).1, okey, okey, Prod.Lex.toLex_lt_toLex]

theorem okey_injective (X : State a (packingLaneBits a g)) :
    Function.Injective (okey subdiv X) := by
  intro z1 z2 h
  apply X.packingData.slotIdentifier_injective X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) subdiv
  apply Fin.ext
  obtain ⟨M, -, hM⟩ := slotIdentifier_val subdiv X z1
  rw [(hM z1).2, (hM z2).2]
  have h' := congrArg ofLex h
  simp only [okey, ofLex_toLex, Prod.mk.injEq] at h'
  rw [h'.1, h'.2]

end Keys

end P1P7
