import P1P7.Defs
import P1P7.Transport

/-!
# P7, shrink half, layer 1: partner bases and transport of the packing data

Two old states `X`, `X'` (same `a`, `g`). The partner `pb X X' y` of a base `y` is the base of `X'` with the same
address. `SGood X X' y` says that `y` and its partner carry the same panel, greedy colour and greedy tag offset.
Under `SGood` at the bases involved, every datum of OpenAI's packing construction (`X.packingData`,
PackingLanes.lean:72; SlotPacking.lean; SurvivingSlots.lean) commutes with the transport `tS`/`tP`/`tA`, which
replaces the old base of a site, position or arc by its partner and keeps every other coordinate.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots

/-! ## Partner bases -/

section Partner

variable {a g g' : ℕ}

/-- The base of `X'` with the same address as `y` (a fixed base if there is none). -/
noncomputable def pb (X : State a g) (X' : State a g') (y : X.Base) : X'.Base :=
  if h : addr X y < Fintype.card X'.Base then X'.baseIndex.symm ⟨addr X y, h⟩
  else Classical.choice X'.baseNonempty

theorem pb_eq (X : State a g) (X' : State a g') {y : X.Base} {y' : X'.Base}
    (h : addr X y = addr X' y') : pb X X' y = y' := by
  have hlt : addr X y < Fintype.card X'.Base := by
    rw [h]; exact (X'.baseIndex y').isLt
  rw [pb, dif_pos hlt]
  apply X'.baseIndex.injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext h

theorem addr_pb (X : State a g) (X' : State a g') {y : X.Base} {y' : X'.Base}
    (h : addr X y = addr X' y') : addr X' (pb X X' y) = addr X y := by
  rw [pb_eq X X' h]; exact h.symm

/-- Transport of a site, position, arc or packed base: the old base is replaced by its partner. -/
noncomputable def tS {T L : Type*} (X : State a g) (X' : State a g') (s : Site X.Base T L) : Site X'.Base T L :=
  (pb X X' s.1, s.2)

noncomputable def tP {H T L : Type*} {c : ℕ} (X : State a g) (X' : State a g') (p : Position X.Base H T L c) :
    Position X'.Base H T L c :=
  (tS X X' p.1, p.2)

noncomputable def tA {H T L : Type*} {d c : ℕ} (X : State a g) (X' : State a g') (α : Arc X.Base H T L d c) :
    Arc X'.Base H T L d c :=
  ((tS X X' α.1.1, α.1.2), α.2)

noncomputable def tB {T : Type*} (X : State a g) (X' : State a g') (b : X.Base × T) : X'.Base × T :=
  (pb X X' b.1, b.2)

@[simp] theorem sourcePosition_tA {H T L : Type*} {d c : ℕ} (X : State a g) (X' : State a g')
    (α : Arc X.Base H T L d c) : sourcePosition (tA X X' α) = tP X X' (sourcePosition α) := rfl

@[simp] theorem packedBase_tS {T L : Type*} (X : State a g) (X' : State a g') (s : Site X.Base T L) :
    packedBase (tS X X' s) = tB X X' (packedBase s) := rfl

end Partner

/-! ## Good bases -/

section Good

variable {a g : ℕ}

/-- `y` and its partner have the same address, panel, greedy colour and greedy tag offset. -/
structure SGood (X X' : State a (packingLaneBits a g)) (y : X.Base) : Prop where
  addr_eq : addr X' (pb X X' y) = addr X y
  panel_eq : panel X y = panel X' (pb X X' y)
  color_eq : X.packingData.color y = X'.packingData.color (pb X X' y)
  offset_eq : X.packingData.offset y = X'.packingData.offset (pb X X' y)

variable {X X' : State a (packingLaneBits a g)} {y : X.Base}

theorem SGood.outNbr_eq (h : SGood X X' y) (k : Fin (2 ^ a)) :
    addr X (X.slots.base.target (y, k)).1 = addr X' (X'.slots.base.target (pb X X' y, k)).1 ∧
      X.slots.displacement (y, k) = X'.slots.displacement (pb X X' y, k) := by
  have hon : outNbr X y = outNbr X' (pb X X' y) := congrArg (fun p => p.1) h.panel_eq
  have := congrFun hon k
  simp only [outNbr, Prod.mk.injEq] at this
  exact this

theorem SGood.tgt1 (h : SGood X X' y) (k : Fin (2 ^ a)) :
    pb X X' (X.slots.base.target (y, k)).1 = (X'.slots.base.target (pb X X' y, k)).1 :=
  pb_eq X X' (h.outNbr_eq k).1

theorem SGood.tgt_addr (h : SGood X X' y) (k : Fin (2 ^ a)) :
    addr X' (pb X X' (X.slots.base.target (y, k)).1) = addr X (X.slots.base.target (y, k)).1 :=
  addr_pb X X' (h.outNbr_eq k).1

theorem SGood.tgt2 (h : SGood X X' y) (k : Fin (2 ^ a)) :
    (X.slots.base.target (y, k)).2 = (X'.slots.base.target (pb X X' y, k)).2 := by
  have hof : outFar X y = outFar X' (pb X X' y) := congrArg (fun p => p.2.1) h.panel_eq
  exact Fin.ext (congrFun hof k)

theorem SGood.disp (h : SGood X X' y) (k : Fin (2 ^ a)) :
    X.slots.displacement (y, k) = X'.slots.displacement (pb X X' y, k) :=
  (h.outNbr_eq k).2

theorem SGood.inNbr_eq (h : SGood X X' y) (k : Fin (2 ^ a)) :
    addr X (X.slots.base.target.symm (y, k)).1 = addr X' (X'.slots.base.target.symm (pb X X' y, k)).1 ∧
      X.slots.displacement (X.slots.base.target.symm (y, k)) =
        X'.slots.displacement (X'.slots.base.target.symm (pb X X' y, k)) := by
  have hin : inNbr X y = inNbr X' (pb X X' y) := congrArg (fun p => p.2.2.1) h.panel_eq
  have := congrFun hin k
  simp only [inNbr, Prod.mk.injEq] at this
  exact this

theorem SGood.itgt1 (h : SGood X X' y) (k : Fin (2 ^ a)) :
    pb X X' (X.slots.base.target.symm (y, k)).1 = (X'.slots.base.target.symm (pb X X' y, k)).1 :=
  pb_eq X X' (h.inNbr_eq k).1

theorem SGood.itgt_addr (h : SGood X X' y) (k : Fin (2 ^ a)) :
    addr X' (pb X X' (X.slots.base.target.symm (y, k)).1) = addr X (X.slots.base.target.symm (y, k)).1 :=
  addr_pb X X' (h.inNbr_eq k).1

theorem SGood.itgt2 (h : SGood X X' y) (k : Fin (2 ^ a)) :
    (X.slots.base.target.symm (y, k)).2 = (X'.slots.base.target.symm (pb X X' y, k)).2 := by
  have hif : inFar X y = inFar X' (pb X X' y) := congrArg (fun p => p.2.2.2.1) h.panel_eq
  exact Fin.ext (congrFun hif k)

theorem SGood.width_eq (h : SGood X X' y) (k : Fin (2 ^ a)) (l : BitWord (packingLaneBits a g)) :
    X.width ((y, k), l) = X'.width ((pb X X' y, k), l) := by
  have how : outWidths X y = outWidths X' (pb X X' y) := congrArg (fun p => p.2.2.2.2) h.panel_eq
  exact congrFun (congrFun how k) l

end Good

/-! ## Transport of the packing data -/

section Packing

variable {a g : ℕ} (X X' : State a (packingLaneBits a g))

/-- Short names for the coordinate types of the packing. -/
abbrev TagW (a : ℕ) := BitWord (packingTagBits (2 ^ a))

theorem siteGraph_tS (y : X.Base) (tl : TagW a × BitWord g) (i : Fin (2 ^ a)) (h : SGood X X' y) :
    X'.packingData.siteGraph.target ((pb X X' y, tl), i) =
      (tS X X' (X.packingData.siteGraph.target ((y, tl), i)).1,
        (X.packingData.siteGraph.target ((y, tl), i)).2) := by
  change (((X'.slots.base.target (pb X X' y, i)).1,
      tl + (packingFields a g (X'.slots.displacement (pb X X' y, i))).2.2),
      (X'.slots.base.target (pb X X' y, i)).2) =
    ((pb X X' (X.slots.base.target (y, i)).1,
      tl + (packingFields a g (X.slots.displacement (y, i))).2.2),
      (X.slots.base.target (y, i)).2)
  rw [h.tgt1, h.tgt2, h.disp]

theorem actual_tA (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (h : SGood X X' α.1.1.1) :
    X'.packingData.actual (tA X X' α) = tA X X' (X.packingData.actual α) := by
  obtain ⟨⟨⟨y, tl⟩, i⟩, u, hh⟩ := α
  change (X'.packingData.siteGraph.target ((pb X X' y, tl), i),
      u + (packingFields a g (X'.slots.displacement (pb X X' y, i))).1,
      hh + (packingFields a g (X'.slots.displacement (pb X X' y, i))).2.1) =
    ((tS X X' (X.packingData.siteGraph.target ((y, tl), i)).1,
      (X.packingData.siteGraph.target ((y, tl), i)).2),
      u + (packingFields a g (X.slots.displacement (y, i))).1,
      hh + (packingFields a g (X.slots.displacement (y, i))).2.1)
  rw [siteGraph_tS X X' y tl i h, h.disp]

theorem thick_tP (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (h : SGood X X' p.1.1) :
    X'.packingData.thick (tP X X' p) ↔ X.packingData.thick p := by
  change p.2.1 (X'.packingData.color (pb X X' p.1.1)) = 1 ↔ p.2.1 (X.packingData.color p.1.1) = 1
  rw [h.color_eq]

/-- The head base of an old arc. -/
theorem actual_base (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) :
    (sourcePosition (X.packingData.actual α)).1.1 = (X.slots.base.target (α.1.1.1, α.1.2)).1 := rfl

/-- Both ends of an old arc are good. -/
def EndsGood (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) : Prop :=
  SGood X X' α.1.1.1 ∧ SGood X X' (X.slots.base.target (α.1.1.1, α.1.2)).1

/-- The thick-thick test of an old wire is transported. -/
theorem thickThick_tA (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (h : EndsGood X X' α) :
    (X'.packingData.thick (sourcePosition (tA X X' α)) ∧
        X'.packingData.thick (sourcePosition (X'.packingData.actual (tA X X' α)))) ↔
      (X.packingData.thick (sourcePosition α) ∧
        X.packingData.thick (sourcePosition (X.packingData.actual α))) := by
  rw [actual_tA X X' α h.1, sourcePosition_tA, sourcePosition_tA,
    thick_tP X X' (sourcePosition α) h.1, thick_tP X X' (sourcePosition (X.packingData.actual α)) h.2]

/-- The motif condition of an old wire is transported. -/
theorem motif_tA (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (h : EndsGood X X' α)
    (hm : ¬ (X.packingData.thick (sourcePosition α) ∧
        X.packingData.thick (sourcePosition (X.packingData.actual α)))) :
    ¬ (X'.packingData.thick (sourcePosition (tA X X' α)) ∧
        X'.packingData.thick (sourcePosition (X'.packingData.actual (tA X X' α)))) := by
  rw [thickThick_tA X X' α h]; exact hm

variable {X X'}

theorem C_tA (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (h : EndsGood X X' m.val) :
    X'.packingData.C m' = tP X X' (X.packingData.C m) := by
  unfold PackingData.C
  simp only [hm, actual_tA X X' m.val h.1, sourcePosition_tA]
  by_cases ht : X.packingData.thick (sourcePosition m.val)
  · rw [if_pos ((thick_tP X X' (sourcePosition m.val) h.1).mpr ht), if_pos ht]
  · rw [if_neg (fun h' => ht ((thick_tP X X' (sourcePosition m.val) h.1).mp h')), if_neg ht]

theorem D_tA (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (h : EndsGood X X' m.val) :
    X'.packingData.D m' = tP X X' (X.packingData.D m) := by
  unfold PackingData.D
  simp only [hm, actual_tA X X' m.val h.1, sourcePosition_tA]
  by_cases ht : X.packingData.thick (sourcePosition m.val)
  · rw [if_pos ((thick_tP X X' (sourcePosition m.val) h.1).mpr ht), if_pos ht]
  · rw [if_neg (fun h' => ht ((thick_tP X X' (sourcePosition m.val) h.1).mp h')), if_neg ht]

/-- The C and D endpoints sit at the two ends of the wire. -/
theorem C_good (m : X.packingData.Motif) (h : EndsGood X X' m.val) :
    SGood X X' (X.packingData.C m).1.1 := by
  unfold PackingData.C
  split_ifs
  · exact h.2
  · exact h.1

theorem D_good (m : X.packingData.Motif) (h : EndsGood X X' m.val) :
    SGood X X' (X.packingData.D m).1.1 := by
  unfold PackingData.D
  split_ifs
  · exact h.1
  · exact h.2

theorem assignedBundle_tP (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (h : SGood X X' p.1.1) :
    X'.packingData.assignedBundle (tP X X' p) =
      (tS X X' (X.packingData.assignedBundle p).1, (X.packingData.assignedBundle p).2) := by
  change ((pb X X' p.1.1, p.1.2.1 + X'.packingData.offset (pb X X' p.1.1), p.1.2.2),
      bitWordFinEquiv a p.2.2) =
    ((pb X X' p.1.1, p.1.2.1 + X.packingData.offset p.1.1, p.1.2.2), bitWordFinEquiv a p.2.2)
  rw [h.offset_eq]

theorem placement_tP (layout : Bool)
    (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1)) (h : SGood X X' p.1.1) :
    X'.packingData.placement layout (tP X X' p) = tS X X' (X.packingData.placement layout p) := by
  unfold PackingData.placement
  rw [assignedBundle_tP p h]
  have hs := siteGraph_tS X X' (X.packingData.assignedBundle p).1.1
    (X.packingData.assignedBundle p).1.2 (X.packingData.assignedBundle p).2 h
  by_cases ht : X.packingData.thick p
  · rw [if_pos ((thick_tP X X' p h).mpr ht), if_pos ht]; rfl
  · rw [if_neg (fun h' => ht ((thick_tP X X' p h).mp h')), if_neg ht]
    cases layout
    · rfl
    · exact congrArg Prod.fst hs

theorem bundle_tA (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (h : EndsGood X X' m.val) :
    X'.packingData.bundle m' = (tS X X' (X.packingData.bundle m).1, (X.packingData.bundle m).2) := by
  unfold PackingData.bundle
  rw [C_tA m m' hm h, assignedBundle_tP _ (C_good m h)]

theorem roleA_tA (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (h : EndsGood X X' m.val) :
    X'.packingData.roleA m' = tS X X' (X.packingData.roleA m) := by
  unfold PackingData.roleA
  rw [bundle_tA m m' hm h]

theorem roleB_tA (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (h : EndsGood X X' m.val) :
    X'.packingData.roleB m' = tS X X' (X.packingData.roleB m) := by
  unfold PackingData.roleB
  rw [bundle_tA m m' hm h]
  have hs := siteGraph_tS X X' (X.packingData.bundle m).1.1 (X.packingData.bundle m).1.2
    (X.packingData.bundle m).2 (C_good m h)
  exact congrArg Prod.fst hs

theorem roleD_tA (layout : Bool) (m : X.packingData.Motif) (m' : X'.packingData.Motif)
    (hm : m'.val = tA X X' m.val) (h : EndsGood X X' m.val) :
    X'.packingData.roleD layout m' = tS X X' (X.packingData.roleD layout m) := by
  unfold PackingData.roleD
  rw [D_tA m m' hm h, placement_tP layout _ (D_good m h)]

theorem survivingRole_tA (layout : Bool) (r : PackedRole) (m : X.packingData.Motif)
    (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val) (h : EndsGood X X' m.val) :
    X'.packingData.survivingRole layout r m' = tS X X' (X.packingData.survivingRole layout r m) := by
  cases r
  · exact roleA_tA m m' hm h
  · exact roleB_tA m m' hm h
  · exact roleD_tA layout m m' hm h

end Packing

end P1P7
