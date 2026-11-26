import P1SolC10SA.PanelProgram
import P1SolC10SA.RankSpec

namespace P1SolC10SA.SolShrink

open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1P7

variable {a b g : ℕ} {δ : ℝ}

def stateEnd {d n : ℕ} (Y : State d n) (incoming : Bool) (p : Y.Base) (k : Fin (2 ^ d)) : EndRow :=
  bif incoming then ((inNbr Y p k).1, wordNum (inNbr Y p k).2, inFar Y p k)
  else ((outNbr Y p k).1, wordNum (outNbr Y p k).2, outFar Y p k)

section Graph

variable (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (layout : Bool) (w : X.packingData.Motif → Fin 4 → ℕ)

noncomputable abbrev outState := X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)

abbrev ShrinkPadding (X : State a (packingLaneBits a g)) (b : ℕ) :=
  Packed X × Fin (2 ^ b - PackingData.survivingDegree (2 ^ a) (2 * 2 ^ a + 1) (SD a b))

theorem stateEnd_numberSide (incoming : Bool)
    (z : OldId X (SD a b) ⊕ ShrinkPadding X b) :
    stateEnd (outState X ready layout w) incoming (numberSide X ready incoming layout z).1
        (numberSide X ready incoming layout z).2 =
      (packedCode X (numberSide X ready (!incoming) layout z).1,
        wordNum ((X.shrinkStateIndex ready layout).graph.displacement
          ((X.shrinkStateIndex ready layout).outgoing z)),
        (numberSide X ready (!incoming) layout z).2.val) := by
  let I := X.shrinkStateIndex ready layout
  cases incoming
  · change (addr (outState X ready layout w) (I.graph.base.target (I.outgoing z)).1,
      wordNum (I.graph.displacement (I.outgoing z)), (I.graph.base.target (I.outgoing z)).2.val) =
      (packedCode X (I.incoming z).1, wordNum (I.graph.displacement (I.outgoing z)), (I.incoming z).2.val)
    rw [I.match_eq, addr_shrinkOut, packedCode, Nat.add_comm]
  · have he : I.graph.base.target.symm (I.incoming z) = I.outgoing z :=
      (Equiv.symm_apply_eq _).mpr (I.match_eq z).symm
    change (addr (outState X ready layout w) (I.graph.base.target.symm (I.incoming z)).1,
      wordNum (I.graph.displacement (I.graph.base.target.symm (I.incoming z))),
      (I.graph.base.target.symm (I.incoming z)).2.val) =
      (packedCode X (I.outgoing z).1, wordNum (I.graph.displacement (I.outgoing z)), (I.outgoing z).2.val)
    rw [he, addr_shrinkOut, packedCode, Nat.add_comm]

theorem genuineEnd_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (incoming : Bool) (j : TagW a) (z : OldId X (SD a b))
    (hz : typedEnd X (SD a b) incoming layout z = (x, j)) :
    genuineEnd a (∑ t, SD a b t) incoming (2 ^ g, db, layout) (ballIds a b (2 ^ g) db) (idCode X z) =
      (packedCode X (numberSide X ready (!incoming) layout (.inl z)).1,
        wordNum ((X.shrinkStateIndex ready layout).graph.displacement
          ((X.shrinkStateIndex ready layout).outgoing (.inl z))),
        (numberSide X ready (!incoming) layout (.inl z)).2.val) := by
  obtain ⟨hs, ht⟩ := nearEnds X h (SD a b) incoming layout z (by rw [hz]; simp)
  let p := typedEnd X (SD a b) (!incoming) layout z
  have hp : (baseGraph X).edist x p.1 ≤ 4 := by
    have hh := roles_near X layout (pickRole incoming layout z.1) (pickRole (!incoming) layout z.1) z.2.1.val
    change (baseGraph X).edist (typedEnd X (SD a b) incoming layout z).1 p.1 ≤ 4 at hh
    rw [hz] at hh
    exact hh
  have other : childCode a (bif incoming
      then idEnd a false (2 ^ g, db, layout) (idCode X z)
      else idEnd a true (2 ^ g, db, layout) (idCode X z)) = packedCode X p := by
    cases incoming
    · exact child_idEnd_spec X h.toGraphRows (SD a b) true layout z hs ht
    · exact child_idEnd_spec X h.toGraphRows (SD a b) false layout z hs ht
  have hshift := (X.shrinkStateIndex ready layout).displacement_eq (.inl z)
  change (X.shrinkStateIndex ready layout).graph.displacement ((X.shrinkStateIndex ready layout).outgoing (.inl z)) =
    X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) z at hshift
  simp only [genuineEnd, other]
  rw [← numberSide_rank X h ready (!incoming) layout p hp z rfl,
    numberSide_end X ready (!incoming) layout z, hshift,
    idEnd_spec X h.toGraphRows (SD a b) false layout z hs ht,
    idEnd_spec X h.toGraphRows (SD a b) true layout z hs ht]
  unfold PackingData.roleDisplacement
  rw [wordNum_sub]
  rfl

theorem rotateTag_spec (incoming : Bool) (p : Packed X) :
    addressChild a (addr X p.1) (rotateTag a incoming (wordNum p.2)) =
      packedCode X ((bif incoming then (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm
        else cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))) p) := by
  let e := bitWordFinEquiv (packingTagBits (2 ^ a))
  let : NeZero (tagCount a) := ⟨(Nat.two_pow_pos _).ne'⟩
  rcases p with ⟨x, t⟩
  change addressChild a (addr X x) (rotateTag a incoming (e t).val) = _
  have hJ : 1 < tagCount a := Nat.one_lt_two_pow (Nat.succ_pos _).ne'
  have oneVal : (1 : Fin (tagCount a)).val = 1 := Nat.mod_eq_of_lt hJ
  cases incoming
  · simp only [Bool.cond_false, cycleTags_apply, addressChild, rotateTag, packedCode, wordNum,
      e, Equiv.apply_symm_apply, finRotate_apply, Fin.val_add, oneVal]
  · simp only [Bool.cond_true, cycleTags_symm_apply, addressChild, rotateTag, packedCode, wordNum,
      e, Equiv.apply_symm_apply, finRotate_symm_apply, Fin.val_sub, oneVal, Nat.add_comm (tagCount a - 1)]

theorem dummyEnd_spec (incoming : Bool) (d : ShrinkPadding X b) :
    let p := (numberSide X ready incoming layout (.inr d)).1
    let k := (numberSide X ready incoming layout (.inr d)).2
    dummyEnd a incoming (addr X p.1) (wordNum p.2) k.val =
      (packedCode X (numberSide X ready (!incoming) layout (.inr d)).1,
        wordNum ((X.shrinkStateIndex ready layout).graph.displacement
          ((X.shrinkStateIndex ready layout).outgoing (.inr d))),
        (numberSide X ready (!incoming) layout (.inr d)).2.val) := by
  let I := X.shrinkStateIndex ready layout
  let cyc : Equiv.Perm (Packed X) := cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))
  have hs : (I.outgoing (.inr d)).1 = d.1 := I.src_eq (.inr d)
  have ht : (I.incoming (.inr d)).1 = cyc d.1 := I.dst_eq (.inr d)
  have hz : I.graph.displacement (I.outgoing (.inr d)) = 0 := I.displacement_eq (.inr d)
  have hk : (I.outgoing (.inr d)).2.val = (I.incoming (.inr d)).2.val :=
    (out_dummy_val X ready layout d.1 d.2).trans (in_dummy_val X ready layout d.1 d.2).symm
  simp only [dummyEnd, rotateTag_spec X]
  change (_, 0, _) = (_, wordNum (I.graph.displacement (I.outgoing (.inr d))), _)
  rw [hz, wordNum_zero]
  cases incoming
  · change (packedCode X (cyc (I.outgoing (.inr d)).1), 0, (I.outgoing (.inr d)).2.val) =
      (packedCode X (I.incoming (.inr d)).1, 0, (I.incoming (.inr d)).2.val)
    rw [hs, ht, hk]
  · change (packedCode X (cyc.symm (I.incoming (.inr d)).1), 0, (I.incoming (.inr d)).2.val) =
      (packedCode X (I.outgoing (.inr d)).1, 0, (I.outgoing (.inr d)).2.val)
    rw [ht, hs, hk, Equiv.symm_apply_apply]

theorem endRecord_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (incoming : Bool) (j : TagW a) (k : Fin (2 ^ b)) :
    let kId := idAt a (∑ t, SD a b t)
      (localFibre a b (2 ^ g) db incoming layout (packedCode X (x,j))) k.val
    endRecord a (∑ t, SD a b t) incoming (2 ^ g, db, layout) (ballIds a b (2 ^ g) db)
      (addr X x) (wordNum j) k.val kId = stateEnd (outState X ready layout w) incoming (x,j) k := by
  let f := numberSide X ready incoming layout
  dsimp only
  rw [idAt_numberSide X h ready incoming layout (x,j) (by simp) k]
  rcases he : f.symm ((x,j),k) with z | d
  · have hp : f (.inl z) = ((x,j),k) := (Equiv.eq_symm_apply f).mp he.symm
    have hx := (numberSide_end X ready incoming layout z).symm.trans (congrArg Prod.fst hp)
    change endRecord a _ incoming _ _ _ _ k.val (some (idCode X z)) = _
    rw [show endRecord a (∑ t, SD a b t) incoming (2 ^ g, db, layout) (ballIds a b (2 ^ g) db)
      (addr X x) (wordNum j) k.val (some (idCode X z)) =
        genuineEnd a (∑ t, SD a b t) incoming (2 ^ g, db, layout) (ballIds a b (2 ^ g) db) (idCode X z) from rfl]
    have spec := stateEnd_numberSide X ready layout w incoming (.inl z)
    change stateEnd (outState X ready layout w) incoming (f (.inl z)).1 (f (.inl z)).2 = _ at spec
    rw [hp] at spec
    exact (genuineEnd_spec X ready layout h incoming j z hx).trans spec.symm
  · have hp : f (.inr d) = ((x,j),k) := (Equiv.eq_symm_apply f).mp he.symm
    have spec := stateEnd_numberSide X ready layout w incoming (.inr d)
    change stateEnd (outState X ready layout w) incoming (f (.inr d)).1 (f (.inr d)).2 = _ at spec
    rw [hp] at spec
    have hd := dummyEnd_spec X ready layout incoming d
    change dummyEnd a incoming (addr X (f (.inr d)).1.1) (wordNum (f (.inr d)).1.2) (f (.inr d)).2.val = _ at hd
    rw [hp] at hd
    change dummyEnd a incoming (addr X x) (wordNum j) k.val = _
    exact hd.trans spec.symm

end Graph

end P1SolC10SA.SolShrink
