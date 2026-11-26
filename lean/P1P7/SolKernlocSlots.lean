import P1P7.KernelRes

namespace P1P7.SolKernloc

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkPayload
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.NetworkKernel

noncomputable local instance {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

section Slots

variable {a b g : ℕ} {δ factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {X X' : State a (packingLaneBits a g)}

noncomputable abbrev outputState (X : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (L : Bool) : State b g :=
  X.shrinkOutputState L (SD a b) (fun m t => selW B X s m (L, t)) (X.shrinkStateIndex ready L)

variable {B ready}

/-- The canonical slice of an output arc, named using its lane-zero ID and source lane. -/
theorem genuineWidth (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (L : Bool) (z : Id X.packingData.BaseMotif (SD a b)) (l : BitWord g) :
    (outputState B ready X s L).width ((X.shrinkStateIndex ready L).outgoing (.inl z), l) =
      splitWidth (selW B X s
        ((X.packingData.survivingLaneEquiv L (SD a b)).symm (z, l)).2.1 (L, z.1))
        (SD a b z.1) z.2.2 := by
  have h := X.packingData.shrinkSlotWidth_genuine L (SD a b)
    (fun m t => selW B X s m (L, t)) (X.shrinkStateIndex ready L).outgoing
    ((X.packingData.survivingLaneEquiv L (SD a b)).symm (z, l))
  simp only [PackingData.shrinkArcEquiv_genuine, Equiv.apply_symm_apply] at h
  rcases z with ⟨t, bm, i⟩
  exact h

/-- The lifted edge arriving at a numbered in-slot has the outgoing number of
the same ID and source lane obtained by subtracting the shift. -/
theorem inEdge_payloadType (Y : State b g) (v : Y.network.Site) (k : Fin (2 ^ b)) :
    Y.network.Payload ((inFib Y v).symm k).1 =
      (Fin (Y.width (Y.slots.base.target.symm (v.1, k),
        v.2 - Y.slots.displacement (Y.slots.base.target.symm (v.1, k)))) → Bool) := rfl

private theorem partner_reconstruct (L : Bool) (z : Id X.packingData.BaseMotif (SD a b))
    (hm : MotifT X X' z.2.1.1.val) (hE : EndsGood X X' z.2.1.1.val) (l : BitWord g) :
    ((X'.packingData.survivingLaneEquiv L (SD a b)).symm (tId z hm, l)).2.1.val =
      tA X X' (((X.packingData.survivingLaneEquiv L (SD a b)).symm (z, l)).2.1.val) := by
  rcases z with ⟨t, bm, i⟩
  have h := survivingRole_tA L (sourceRole L t) bm.1 (tM bm.1 hE) rfl hE
  have hLane : (X'.packingData.survivingRole L (sourceRole L t) (tM bm.1 hE)).2.2 =
      (X.packingData.survivingRole L (sourceRole L t) bm.1).2.2 := congrArg (fun q => q.2.2) h
  change translateArc (tA X X' bm.1.val)
      (l - (X'.packingData.survivingRole L (sourceRole L t) (tM bm.1 hE)).2.2) =
    tA X X' (translateArc bm.1.val (l - (X.packingData.survivingRole L (sourceRole L t) bm.1).2.2))
  rw [hLane]
  rfl

theorem inWidth {x : X.Base} (hg : Good3 X X' x)
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B) (hch : Ch3 B X X' s s' x)
    (L : Bool) (j : TagW a) (l : BitWord g) (k : Fin (2 ^ b)) :
    (outputState B ready X s L).network.Payload ((inFib (outputState B ready X s L) ((x, j), l)).symm k).1 =
    (outputState B ready X' s' L).network.Payload
      ((inFib (outputState B ready X' s' L) ((pb X X' x, j), l)).symm k).1 := by
  let Y := outputState B ready X s L
  let Y' := outputState B ready X' s' L
  let I := X.shrinkStateIndex ready L
  let I' := X'.shrinkStateIndex ready L
  refine (inEdge_payloadType Y ((x, j), l) k).trans
    (Eq.trans ?_ (inEdge_payloadType Y' ((pb X X' x, j), l) k).symm)
  apply congrArg (fun n => Fin n → Bool)
  change Y.width (Y.slots.base.target.symm ((x, j), k),
      l - Y.slots.displacement (Y.slots.base.target.symm ((x, j), k))) =
    Y'.width (Y'.slots.base.target.symm ((pb X X' x, j), k),
      l - Y'.slots.displacement (Y'.slots.base.target.symm ((pb X X' x, j), k)))
  have hg₂ : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y hy => hg y (hy.trans (by norm_num))
  rcases in_corr X X' ready L x j hg₂ k with ⟨z, hm, h, h', hE⟩ | ⟨i, h, h'⟩
  · have ei := I.match_eq (.inl z)
    have ei' := I'.match_eq (.inl (tId z hm))
    change I.incoming (.inl z) = _ at h
    change I'.incoming (.inl (tId z hm)) = _ at h'
    rw [h] at ei
    rw [h'] at ei'
    have hi : Y.slots.base.target.symm ((x, j), k) = I.outgoing (.inl z) :=
      (Equiv.symm_apply_eq _).mpr ei.symm
    have hi' : Y'.slots.base.target.symm ((pb X X' x, j), k) = I'.outgoing (.inl (tId z hm)) :=
      (Equiv.symm_apply_eq _).mpr ei'.symm
    let sh := X.packingData.roleDisplacement L (sourceRole L) (targetRole L) z
    have hs : Y.slots.displacement (I.outgoing (.inl z)) = sh := I.displacement_eq _
    have hs' : Y'.slots.displacement (I'.outgoing (.inl (tId z hm))) = sh :=
      (I'.displacement_eq _).trans (roleDisplacement_tId L z hm hE)
    rw [hi, hi', hs, hs']
    change (outputState B ready X s L).width ((X.shrinkStateIndex ready L).outgoing (.inl z), l - sh) =
      (outputState B ready X' s' L).width
        ((X'.shrinkStateIndex ready L).outgoing (.inl (tId z hm)), l - sh)
    rw [genuineWidth, genuineWidth]
    let m := ((X.packingData.survivingLaneEquiv L (SD a b)).symm (z, l - sh)).2.1
    let m' := ((X'.packingData.survivingLaneEquiv L (SD a b)).symm (tId z hm, l - sh)).2.1
    have hEm : EndsGood X X' m.val := by
      rcases z with ⟨t, bm, i⟩
      exact hE
    have hmotif : m' = tM m hEm := Subtype.ext (partner_reconstruct L z hm hE (l - sh))
    have hbase : (X.packingData.survivingRole L (targetRole L z.1) m).1 = x := by
      have e := (X.packingData.survivingLane_endpoints L (SD a b) z (l - sh)).2
      have ebase : (endpoint (X.packingData.roleBase L) (targetRole L) z).1 = x :=
        congrArg Prod.fst ((I.dst_eq (.inl z)).symm.trans (congrArg Prod.fst h))
      exact (congrArg Prod.fst e).trans ebase
    change splitWidth (selW B X s m (L, z.1)) (SD a b z.1) z.2.2 =
      splitWidth (selW B X' s' m' (L, z.1)) (SD a b z.1) z.2.2
    rw [hmotif, selW_eq B hg s s' hch L (targetRole L z.1) m hbase hEm]
  · let d := ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i)
    let d' := ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i)
    have ei := I.match_eq (.inr d)
    have ei' := I'.match_eq (.inr d')
    change I.incoming (.inr d) = _ at h
    change I'.incoming (.inr d') = _ at h'
    rw [h] at ei
    rw [h'] at ei'
    have hi : Y.slots.base.target.symm ((x, j), k) = I.outgoing (.inr d) :=
      (Equiv.symm_apply_eq _).mpr ei.symm
    have hi' : Y'.slots.base.target.symm ((pb X X' x, j), k) = I'.outgoing (.inr d') :=
      (Equiv.symm_apply_eq _).mpr ei'.symm
    rw [hi, hi']
    exact (X.packingData.shrinkSlotWidth_padding L (SD a b)
      (fun m t => selW B X s m (L,t)) I.outgoing d _).trans
      (X'.packingData.shrinkSlotWidth_padding L (SD a b)
        (fun m t => selW B X' s' m (L,t)) I'.outgoing d' _).symm

noncomputable abbrev actualArc (X : State a (packingLaneBits a g)) (L : Bool)
    (m : X.packingData.Motif) (t : Fin 4) (i : Fin (SD a b t)) :=
  X.packingData.shrinkArcEquiv L (SD a b) (X.shrinkStateIndex ready L).outgoing (.inl ⟨t, m, i⟩)

private noncomputable abbrev baseId (X : State a (packingLaneBits a g)) (m : X.packingData.Motif)
    (t : Fin 4) (i : Fin (SD a b t)) : Id X.packingData.BaseMotif (SD a b) :=
  ⟨t, X.packingData.baseMotif m, i⟩

private theorem baseId_ends (m : X.packingData.Motif) (hE : EndsGood X X' m.val)
    (t : Fin 4) (i : Fin (SD a b t)) : EndsGood X X' (baseId X m t i).2.1.1.val := hE

private theorem baseId_partner (m : X.packingData.Motif) (hE : EndsGood X X' m.val)
    (t : Fin 4) (i : Fin (SD a b t)) :
    baseId X' (tM m hE) t i = tId (baseId X m t i)
      (motif_tA X X' _ (baseId_ends m hE t i) (baseId X m t i).2.1.1.property) := rfl

private theorem baseId_at (L : Bool) (pick : Fin 4 → PackedRole) (m : X.packingData.Motif)
    (t : Fin 4) (i : Fin (SD a b t)) :
    endpoint (X.packingData.roleBase L) pick (baseId X m t i) =
      packedBase (X.packingData.survivingRole L (pick t) m) := by
  change packedBase (X.packingData.survivingRole L (pick t)
    (X.packingData.translateMotif m (-X.packingData.sourceLane m))) = _
  rw [PackingData.survivingRole_translate]
  rfl

theorem actualArc_out_slot {x : X.Base} (hg : Good3 X X' x)
    (L : Bool) (j : TagW a) (m : X.packingData.Motif) (hE : EndsGood X X' m.val)
    (t : Fin 4) (i : Fin (SD a b t))
    (hs : packedBase (X.packingData.survivingRole L (sourceRole L t) m) = (x, j)) :
    (actualArc (ready := ready) X' L (tM m hE) t i).2 =
      (actualArc (ready := ready) X L m t i).2 := by
  let z := baseId X m t i
  let z' := baseId X' (tM m hE) t i
  have hEz : EndsGood X X' z.2.1.1.val := baseId_ends m hE t i
  have hm := motif_tA X X' _ hEz z.2.1.1.property
  have hzPair : z' = tId z hm := baseId_partner m hE t i
  have hz : endpoint (X.packingData.roleBase L) (sourceRole L) z = (x, j) :=
    (baseId_at L (sourceRole L) m t i).trans hs
  have hz' : endpoint (X'.packingData.roleBase L) (sourceRole L) z' = (pb X X' x, j) := by
    rw [hzPair, endpoint_tId L (sourceRole L) z hm hEz, hz]
    rfl
  have hr := rank_eq X X' (SD a b) L (sourceRole L) x j
    (fun y hy => hg y (hy.trans (by norm_num))) z ((mem_fib X _ L _ _ z).mpr hz) hm
  rw [← hzPair] at hr
  apply Fin.ext
  change ((X'.shrinkStateIndex ready L).outgoing (.inl z')).2.val =
    ((X.shrinkStateIndex ready L).outgoing (.inl z)).2.val
  have hRank := out_rank X ready L z
  have hRank' := out_rank X' ready L z'
  rw [hz] at hRank
  rw [hz'] at hRank'
  exact hRank'.trans (hr.symm.trans hRank.symm)

theorem actualArc_in_slot {x : X.Base} (hg : Good3 X X' x)
    (L : Bool) (j : TagW a) (m : X.packingData.Motif) (hE : EndsGood X X' m.val)
    (t : Fin 4) (i : Fin (SD a b t))
    (hs : packedBase (X.packingData.survivingRole L (targetRole L t) m) = (x, j)) :
    ((X'.shrinkStateIndex ready L).graph.actualGraph.target
        (actualArc (ready := ready) X' L (tM m hE) t i)).2 =
      ((X.shrinkStateIndex ready L).graph.actualGraph.target
        (actualArc (ready := ready) X L m t i)).2 := by
  let z := baseId X m t i
  let z' := baseId X' (tM m hE) t i
  have hEz : EndsGood X X' z.2.1.1.val := baseId_ends m hE t i
  have hm := motif_tA X X' _ hEz z.2.1.1.property
  have hzPair : z' = tId z hm := baseId_partner m hE t i
  have hz : endpoint (X.packingData.roleBase L) (targetRole L) z = (x, j) :=
    (baseId_at L (targetRole L) m t i).trans hs
  have hz' : endpoint (X'.packingData.roleBase L) (targetRole L) z' = (pb X X' x, j) := by
    rw [hzPair, endpoint_tId L (targetRole L) z hm hEz, hz]
    rfl
  have hr := rank_eq X X' (SD a b) L (targetRole L) x j
    (fun y hy => hg y (hy.trans (by norm_num))) z ((mem_fib X _ L _ _ z).mpr hz) hm
  rw [← hzPair] at hr
  apply Fin.ext
  let I := X.shrinkStateIndex ready L
  let I' := X'.shrinkStateIndex ready L
  change (I'.graph.base.target (I'.outgoing (.inl z'))).2.val =
    (I.graph.base.target (I.outgoing (.inl z))).2.val
  rw [I.match_eq, I'.match_eq]
  have hRank := in_rank X ready L z
  have hRank' := in_rank X' ready L z'
  rw [hz] at hRank
  rw [hz'] at hRank'
  exact hRank'.trans (hr.symm.trans hRank.symm)


theorem outWidth {x : X.Base} (hg : Good3 X X' x)
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B) (hch : Ch3 B X X' s s' x)
    (L : Bool) (j : TagW a) (l : BitWord g) (k : Fin (2 ^ b)) :
    (outputState B ready X s L).network.Payload ((outFib (outputState B ready X s L) ((x, j), l)).symm k).1 =
      (outputState B ready X' s' L).network.Payload
        ((outFib (outputState B ready X' s' L) ((pb X X' x, j), l)).symm k).1 :=
  congrArg (fun n => Fin n → Bool) (congrFun (congrFun (outWidths_shrink B ready X X' s s' L x j hg hch) k) l)

theorem outWidth_pair {x : X.Base} (hg : Good3 X X' x)
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B) (hch : Ch3 B X X' s s' x)
    {L L' : Bool} (hLL : L = L') (j : TagW a) (l : BitWord g) (k : Fin (2 ^ b)) :
    (outputState B ready X s L).network.Payload ((outFib (outputState B ready X s L) ((x, j), l)).symm k).1 =
      (outputState B ready X' s' L').network.Payload
        ((outFib (outputState B ready X' s' L') ((pb X X' x, j), l)).symm k).1 := by
  subst L'
  exact outWidth hg s s' hch L j l k

theorem inWidth_pair {x : X.Base} (hg : Good3 X X' x)
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B) (hch : Ch3 B X X' s s' x)
    {L L' : Bool} (hLL : L = L') (j : TagW a) (l : BitWord g) (k : Fin (2 ^ b)) :
    (outputState B ready X s L).network.Payload ((inFib (outputState B ready X s L) ((x, j), l)).symm k).1 =
      (outputState B ready X' s' L').network.Payload
        ((inFib (outputState B ready X' s' L') ((pb X X' x, j), l)).symm k).1 := by
  subst L'
  exact inWidth hg s s' hch L j l k

end Slots

end P1P7.SolKernloc
