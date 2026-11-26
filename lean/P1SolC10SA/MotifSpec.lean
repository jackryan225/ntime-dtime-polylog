import P1SolC10SA.Motifs

namespace P1SolC10SA.SolShrink

open OAI.Computability.VPVNP.Compression
open P1P7

variable {a g : ℕ}

abbrev OldArc (X : State a (packingLaneBits a g)) :=
  Arc X.Base (BitWord a) (TagW a) (BitWord g) (oldDegree a) (colourBits a)

abbrev OldSite (X : State a (packingLaneBits a g)) := Site X.Base (TagW a) (BitWord g)

abbrev OldBundle (X : State a (packingLaneBits a g)) := OldSite X × Fin (oldDegree a)

abbrev OldPlace (X : State a (packingLaneBits a g)) :=
  Position X.Base (BitWord a) (TagW a) (BitWord g) (colourBits a)

def siteCode (X : State a (packingLaneBits a g)) (p : OldSite X) : SiteRow :=
  (addr X p.1, wordNum p.2.1, wordNum p.2.2)

def bundleCode (X : State a (packingLaneBits a g)) (p : OldBundle X) : BundleRow :=
  (siteCode X p.1, p.2.val)

def placeCode (X : State a (packingLaneBits a g)) (p : OldPlace X) : PlaceRow :=
  (siteCode X p.1, wordNum p.2.1, wordNum p.2.2)

def arcCode (X : State a (packingLaneBits a g)) (e : OldArc X) : ArcRow :=
  (bundleCode X e.1, wordNum e.2.1, wordNum e.2.2)

def outgoingCode (X : State a (packingLaneBits a g)) (y : X.Base) (i : Fin (oldDegree a)) : EndRow :=
  ((outNbr X y i).1, wordNum (outNbr X y i).2, outFar X y i)

/-- The three fields needed to recover the packed roles of an old wire. -/
structure GraphRows (X : State a (packingLaneBits a g)) (db : BallRows) : Prop where
  out : ∀ (y : X.Base) (i : Fin (oldDegree a)), hasRow db (addr X y) = true →
    (slotAt db (addr X y) i.val).1 = outgoingCode X y i
  colour : ∀ y, hasRow db (addr X y) = true →
    (rowAt db (addr X y)).2.1 = (X.packingData.color y).val
  offset : ∀ y, hasRow db (addr X y) = true →
    (rowAt db (addr X y)).2.2.1 = wordNum (X.packingData.offset y)

section Correctness

variable {X : State a (packingLaneBits a g)} {db : BallRows}

theorem sourceRow_spec (e : OldArc X) :
    sourceRow (arcCode X e) = placeCode X (sourcePosition e) := rfl

theorem codedSiteTarget_spec (h : GraphRows X db) (p : OldBundle X)
    (hp : hasRow db (addr X p.1.1) = true) :
    codedSiteTarget a (2 ^ g) db (bundleCode X p) =
      bundleCode X (X.packingData.siteGraph.target p) := by
  let y := p.1.1
  let i := p.2
  change (let out := (slotAt db (addr X y) i.val).1
          let shift := splitLane (oldDegree a) (tagCount a) (2 ^ g) out.2.1
          ((out.1, wordNum p.1.2.1 ^^^ shift.2.2.1, wordNum p.1.2.2 ^^^ shift.2.2.2), out.2.2)) = _
  rw [h.out y i hp]
  dsimp only [outgoingCode, outNbr, outFar]
  rw [splitLane_packing]
  change ((_, _, _), _) =
    ((addr X (X.slots.base.target (y, i)).1,
      wordNum (p.1.2.1 + (packingFields a g (X.slots.displacement (y, i))).2.2.1),
      wordNum (p.1.2.2 + (packingFields a g (X.slots.displacement (y, i))).2.2.2)),
      (X.slots.base.target (y, i)).2.val)
  rw [wordNum_add, wordNum_add]

theorem codedTarget_spec (h : GraphRows X db) (e : OldArc X)
    (he : hasRow db (addr X e.1.1.1) = true) :
    codedTarget a (2 ^ g) db (arcCode X e) = arcCode X (X.packingData.actual e) := by
  obtain ⟨p, u, v⟩ := e
  change (let out := (slotAt db (addr X p.1.1) p.2.val).1
          let shift := splitLane (oldDegree a) (tagCount a) (2 ^ g) out.2.1
          (codedSiteTarget a (2 ^ g) db (bundleCode X p), wordNum u ^^^ shift.1,
            wordNum v ^^^ shift.2.1)) = _
  rw [h.out _ _ he, codedSiteTarget_spec h p he]
  simp only [outgoingCode, outNbr, splitLane_packing, PackingData.actual_apply, arcCode, wordNum_add]
  rfl

theorem codedThick_spec (h : GraphRows X db) (p : OldPlace X)
    (hp : hasRow db (addr X p.1.1) = true) :
    codedThick a db (placeCode X p) = decide (X.packingData.thick p) := by
  let c := X.packingData.color p.1.1
  change decide (wordNum p.2.1 / read 1 (thickPowers a) (rowAt db (addr X p.1.1)).2.1 % 2 = 1) = _
  rw [h.colour _ hp]
  have hr : read 1 (thickPowers a) c.val = 2 ^ (colourBits a - 1 - c.val) := by
    simp only [read, thickPowers, List.getElem?_ofFn, c.isLt, dite_true, Option.getD_some]
  rw [hr, ← Nat.testBit_eq_decide_div_mod_eq, wordNum_bit]
  change decide ((p.2.1 c).val = 1) = decide (p.2.1 c = 1)
  have hval : (p.2.1 c).val = 1 ↔ p.2.1 c = 1 :=
    (ZMod.val_injective 2).eq_iff (a := p.2.1 c) (b := 1)
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hval)

theorem assignedRow_spec (h : GraphRows X db) (p : OldPlace X)
    (hp : hasRow db (addr X p.1.1) = true) :
    assignedRow db (placeCode X p) = bundleCode X (X.packingData.assignedBundle p) := by
  change ((addr X p.1.1, wordNum p.1.2.1 ^^^ (rowAt db (addr X p.1.1)).2.2.1,
      wordNum p.1.2.2), wordNum p.2.2) =
    ((addr X p.1.1, wordNum (p.1.2.1 + X.packingData.offset p.1.1), wordNum p.1.2.2),
      wordNum p.2.2)
  rw [h.offset _ hp, wordNum_add]

theorem codedPlacement_spec (h : GraphRows X db) (layout : Bool) (p : OldPlace X)
    (hp : hasRow db (addr X p.1.1) = true) :
    codedPlacement a (2 ^ g) db layout (placeCode X p) =
      siteCode X (X.packingData.placement layout p) := by
  unfold codedPlacement PackingData.placement
  have hp' : hasRow db (addr X (X.packingData.assignedBundle p).1.1) = true := hp
  rw [codedThick_spec h _ hp, assignedRow_spec h _ hp, codedSiteTarget_spec h _ hp']
  by_cases ht : X.packingData.thick p <;> cases layout <;> simp [ht, bundleCode, placeCode]

theorem motifTest_spec (h : GraphRows X db) (e : OldArc X)
    (hs : hasRow db (addr X e.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual e).1.1.1) = true) :
    motifTest a (2 ^ g) db (arcCode X e) =
      decide (¬ (X.packingData.thick (sourcePosition e) ∧
        X.packingData.thick (sourcePosition (X.packingData.actual e)))) := by
  unfold motifTest
  dsimp only
  rw [codedTarget_spec h e hs, sourceRow_spec, sourceRow_spec,
    codedThick_spec h (sourcePosition e) hs, codedThick_spec h (sourcePosition (X.packingData.actual e)) ht]
  change (hasRow db (addr X e.1.1.1) &&
    hasRow db (addr X (X.packingData.actual e).1.1.1) && !(_ && _)) = _
  by_cases ha : X.packingData.thick (sourcePosition e) <;>
    by_cases hb : X.packingData.thick (sourcePosition (X.packingData.actual e)) <;>
    simp [hs, ht, ha, hb]

theorem rolesRow_spec (h : GraphRows X db) (layout : Bool) (m : X.packingData.Motif)
    (hs : hasRow db (addr X m.val.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual m.val).1.1.1) = true) :
    rolesRow a (2 ^ g) db layout (arcCode X m.val) =
      (bundleCode X (X.packingData.bundle m), siteCode X (X.packingData.roleB m),
        siteCode X (X.packingData.roleD layout m)) := by
  have hc : hasRow db (addr X (X.packingData.C m).1.1) = true := by
    unfold PackingData.C
    split
    · exact ht
    · exact hs
  have hd : hasRow db (addr X (X.packingData.D m).1.1) = true := by
    unfold PackingData.D
    split
    · exact hs
    · exact ht
  have hb : hasRow db (addr X (X.packingData.bundle m).1.1) = true := hc
  unfold rolesRow
  dsimp only
  rw [codedTarget_spec h m.val hs, sourceRow_spec, sourceRow_spec, codedThick_spec h _ hs]
  have ec : (bif decide (X.packingData.thick (sourcePosition m.val))
      then placeCode X (sourcePosition (X.packingData.actual m.val))
      else placeCode X (sourcePosition m.val)) = placeCode X (X.packingData.C m) := by
    by_cases hm : X.packingData.thick (sourcePosition m.val) <;> simp [PackingData.C, hm]
  have ed : (bif decide (X.packingData.thick (sourcePosition m.val))
      then placeCode X (sourcePosition m.val)
      else placeCode X (sourcePosition (X.packingData.actual m.val))) = placeCode X (X.packingData.D m) := by
    by_cases hm : X.packingData.thick (sourcePosition m.val) <;> simp [PackingData.D, hm]
  rw [ec, ed, assignedRow_spec h _ hc]
  change (bundleCode X (X.packingData.bundle m),
    (codedSiteTarget a (2 ^ g) db (bundleCode X (X.packingData.bundle m))).1,
    codedPlacement a (2 ^ g) db layout (placeCode X (X.packingData.D m))) = _
  rw [codedSiteTarget_spec h (X.packingData.bundle m) hb,
    codedPlacement_spec h layout (X.packingData.D m) hd]
  rfl

theorem motifKey_spec (e : OldArc X) : motifKey a (arcCode X e) = arcKey X e := rfl

theorem hasRow_mem {db : BallRows} {x : ℕ} (h : hasRow db x = true) :
    x ∈ db.map Prod.fst := by
  by_contra hn
  rw [hasRow, lookup_default_of_absent none db x hn] at h
  cases h

theorem baseMotifRows_spec (h : GraphRows X db)
    (haddr : ∀ i ∈ db.map Prod.fst, ∃ y, addr X y = i) (r : ArcRow) :
    r ∈ baseMotifRows a (2 ^ g) db ↔
      ∃ m : X.packingData.BaseMotif, arcCode X m.val.val = r ∧
        hasRow db (addr X m.val.val.1.1.1) = true ∧
        hasRow db (addr X (X.packingData.actual m.val.val).1.1.1) = true := by
  unfold baseMotifRows
  simp only [List.mem_filter, List.mem_flatMap]
  constructor
  · rintro ⟨⟨i, hi, hr⟩, htest⟩
    obtain ⟨y, rfl⟩ := haddr i (((unique_spec _).2 i).mp hi)
    obtain ⟨t, hrow⟩ := mem_baseMotifCandidates.mp hr
    let e : OldArc X :=
      (((y, ((bitWordFinEquiv (packingTagBits (oldDegree a))).symm t.1, 0)), t.2.1),
        (bitWordFinEquiv (colourBits a)).symm t.2.2.1, (bitWordFinEquiv a).symm t.2.2.2)
    have he : arcCode X e = r := by
      rw [← hrow]
      have hz : (bitWordFinEquiv g 0).val = 0 := wordNum_zero g
      simp only [e, arcCode, bundleCode, siteCode, candidateArc, wordNum,
        Equiv.apply_symm_apply, hz]
    rw [← he] at htest
    have hs : hasRow db (addr X e.1.1.1) = true := by
      rw [motifTest] at htest
      dsimp only [arcCode, bundleCode, siteCode] at htest
      simp only [Bool.and_eq_true_iff] at htest
      tauto
    have ht : hasRow db (addr X (X.packingData.actual e).1.1.1) = true := by
      rw [motifTest, codedTarget_spec h e hs] at htest
      dsimp only [arcCode, bundleCode, siteCode] at htest
      simp only [Bool.and_eq_true_iff] at htest
      tauto
    have hm := of_decide_eq_true ((motifTest_spec h e hs ht).symm.trans htest)
    exact ⟨⟨⟨e, hm⟩, rfl⟩, he, hs, ht⟩
  · rintro ⟨m, rfl, hs, ht⟩
    let e := m.val.val
    have hz : e.1.1.2.2 = 0 := m.property
    have hrow : arcCode X e ∈ baseMotifCandidates a (addr X e.1.1.1) := by
      apply mem_baseMotifCandidates.mpr
      refine ⟨(bitWordFinEquiv (packingTagBits (oldDegree a)) e.1.1.2.1, e.1.2,
        bitWordFinEquiv (colourBits a) e.2.1, bitWordFinEquiv a e.2.2), ?_⟩
      simp only [candidateArc, arcCode, bundleCode, siteCode, hz, wordNum_zero]
    exact ⟨⟨_, ((unique_spec _).2 _).mpr (hasRow_mem hs), hrow⟩,
      (motifTest_spec h e hs ht).trans (decide_eq_true m.val.property)⟩

end Correctness

end P1SolC10SA.SolShrink
