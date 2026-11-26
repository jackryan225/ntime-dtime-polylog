import P1SolGreedy.MotifGeometry

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

section At

variable (all : Bool) (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y key : NumberWord)

local notation "ctx" => (activeMotif all D ℓ a g len Y key)
local notation "bases" => (savedMotifBases ctx u)
local notation "near" => (savedMotifNear bases u)
local notation "leaf" => (savedMotifFields all near u)

theorem root_base_mem : Y ∈ bases.2 := List.mem_cons_self

theorem rootWire_base (w : WireWords) (hw : w ∈ arcRoots all ctx) : w.1 = Y := by
  cases all
  · change w ∈ [indexedWire (activeMotif false D ℓ a g len Y key)] at hw
    rw [List.mem_singleton] at hw
    rw [hw]
    rfl
  · obtain ⟨p, _, h⟩ := List.mem_map.mp hw
    exact (congrArg Prod.fst h).symm

theorem near_slot_reads (w : WireWords) (hbase : w.1 ∈ bases.2)
    (hk : P1Batch.bval w.2.1 < 2 ^ a) (c : Mem)
    (hc : c ∈ [Mem.outAddr, .inAddr, .outFar, .inFar, .outDisp, .inDisp]) :
    P1Batch.bval (cacheRead (near.2, slotAt c (levelRow D ℓ, w.1, w.2.1))) =
      readField D u (secLev ℓ c) (P1Batch.bval w.1 * (D.lv ℓ).slots + P1Batch.bval w.2.1) := by
  apply cacheRead_slot D u ℓ c _ _ _ hk
  intro r hr
  rw [slotsAt_eq, List.mem_map] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  exact motSecondRaw_slot bases w.1 j hbase hj c hc

theorem nearOffset_reads (Z : NumberWord) (hZ : Z ∈ bases.2) :
    P1Batch.bval (nearOffset (near, Z)) = rdOffset D u ℓ (P1Batch.bval Z) :=
  cacheRead_field D u ℓ .offset (motSecondRaw bases) Z (motSecondRaw_offset bases Z hZ)

theorem root_hop_base_mem (w : WireWords) (hy : w.1 = Y)
    (hk : P1Batch.bval w.2.1 < 2 ^ a) (out : Bool) :
    (nearHop out (near, w)).1 ∈ bases.2 := by
  let r := slotAt (if out then .outAddr else .inAddr) (levelRow D ℓ, Y, w.2.1)
  let j := Carry.born (P1Batch.bval w.2.1)
  let r' := slotAt (if out then .outAddr else .inAddr) (levelRow D ℓ, Y, j)
  let rs := motFirstRaw ctx
  let cr := rs.map (fun q => (q, P1Batch.fetch u q))
  let hs : MotifContext := ctx
  have hJ : j ∈ motifSlots ctx := born_mem_wordRange hk
  have hr₁ : r' ∈ rs := by
    change r' ∈ addrRaw (ctx, Y)
    cases out
    · exact addrRaw_in ctx Y j hJ
    · exact addrRaw_out ctx Y j hJ
  have hr₂ : r' ∈ motSecondRaw bases := by
    apply motSecondRaw_slot bases Y j (root_base_mem all D u ℓ a g len Y key) hJ
    cases out <;> simp
  have he : requestNumbers r = requestNumbers r' := by
    unfold r r'
    rw [requestNumbers_slotAt, requestNumbers_slotAt,
      show P1Batch.bval j = _ from bval_born _]
  have hcopy : cacheRead (near.2, r) = cacheRead (cr, r) :=
    (cacheRead_fetch _ _ _ ⟨r', hr₂, he⟩).trans (cacheRead_fetch _ _ _ ⟨r', hr₁, he⟩).symm
  have hAddr (c : FieldCache) : (hop out (hs, c, w)).1 = cacheRead (c, r) := by
    cases out
    · change cacheRead (c, slotAt .inAddr (levelRow D ℓ, w.1, w.2.1)) = _
      rw [hy]
      rfl
    · change cacheRead (c, slotAt .outAddr (levelRow D ℓ, w.1, w.2.1)) = _
      rw [hy]
      rfl
  change (hop out (hs, near.2, w)).1 ∈ Y :: addrWords (hs, cr, Y)
  rw [hAddr near.2, hcopy, ← hAddr cr]
  apply List.mem_cons_of_mem
  rw [← hy]
  exact addrWords_hop_mem_value all D ℓ a g len Y key cr w out hk

set_option maxHeartbeats 600000 in
theorem nearHop_code (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (hb : w.1 ∈ bases.2) (out : Bool) :
    MatchesWire (nearHop out (near, w))
      (if out then sOut a g D u ℓ e else sIn a g D u ℓ e) := by
  obtain ⟨hY, hk, _⟩ := (matchesWire_parts w e).mp hw
  have hk' : P1Batch.bval w.2.1 < 2 ^ a := hk.symm ▸ e.1.2.isLt
  have H (m : Mem) (hm : m ∈ [Mem.outAddr, .inAddr, .outFar, .inFar, .outDisp, .inDisp]) :
    P1Batch.bval (cacheRead (near.2, slotAt m (levelRow D ℓ, w.1, w.2.1))) =
      readField D u (secLev ℓ m) (e.1.1.1 * (D.lv ℓ).slots + e.1.2.val) := by
    rw [near_slot_reads all D u ℓ a g len Y key w hb hk' m hm, hY, hk]
  cases out
  · let addr := cacheRead (near.2, slotAt .inAddr (levelRow D ℓ, w.1, w.2.1))
    let far := cacheRead (near.2, slotAt .inFar (levelRow D ℓ, w.1, w.2.1))
    let disp := cacheRead (near.2, slotAt .inDisp (levelRow D ℓ, w.1, w.2.1))
    change MatchesWire (shiftedWire (wireRadices a g, w, addr, far, disp)) (sIn a g D u ℓ e)
    have hs := shiftedWire_code w e hw addr far disp
    rw [show P1Batch.bval addr = _ from H .inAddr (by simp),
        show P1Batch.bval far = _ from H .inFar (by simp),
        show P1Batch.bval disp = _ from H .inDisp (by simp)] at hs
    have he (x y : BitWord (packingLaneBits a g)) : x + y = x - y := by
      apply (bitWordFinEquiv _).injective
      apply Fin.ext
      rw [bitWord_code_add, bitWord_code_sub]
    rw [he] at hs
    exact hs
  · let addr := cacheRead (near.2, slotAt .outAddr (levelRow D ℓ, w.1, w.2.1))
    let far := cacheRead (near.2, slotAt .outFar (levelRow D ℓ, w.1, w.2.1))
    let disp := cacheRead (near.2, slotAt .outDisp (levelRow D ℓ, w.1, w.2.1))
    change MatchesWire (shiftedWire (wireRadices a g, w, addr, far, disp)) (sOut a g D u ℓ e)
    have hs := shiftedWire_code w e hw addr far disp
    rw [show P1Batch.bval addr = _ from H .outAddr (by simp),
        show P1Batch.bval far = _ from H .outFar (by simp),
        show P1Batch.bval disp = _ from H .outDisp (by simp)] at hs
    exact hs

theorem leafColourAt_reads (Z : NumberWord)
    (hZ : motifColourRequest (levelRow D ℓ, Z) ∈ leafColours near) :
    P1Batch.bval (cacheRead (leaf.2, motifColourRequest (levelRow D ℓ, Z))) =
      rdColour D u ℓ (P1Batch.bval Z) := by
  apply cacheRead_field D u ℓ .colour
  change motifColourRequest (levelRow D ℓ, Z) ∈ motThirdRaw all near
  change motifColourRequest (levelRow D ℓ, Z) ∈ leafColours near ++ leafWires all near ++
    (if all then leafEnergies ctx else [])
  exact List.mem_append_left _ (List.mem_append_left _ hZ)

theorem wordThick_reads (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (hZ : motifColourRequest (levelRow D ℓ, w.1) ∈ leafColours near) :
    wordThick (leaf, w) = decide (sThick D u ℓ e) := by
  let mw := (splitLane (wireRadices a g, w.2.2)).1
  let cw := cacheRead (leaf.2, motifColourRequest (levelRow D ℓ, w.1))
  have hm : P1Batch.bval mw = bwNum e.2.1 := congrArg Prod.fst (wireLane_code w e hw)
  have hc := leafColourAt_reads all D u ℓ a g len Y key w.1 hZ
  change P1Batch.bval cw = _ at hc
  change maskBit (motifRow all D ℓ a g, mw, cw) = _
  rw [maskBit_value all D ℓ a g mw cw e.2.1 hm, hc, ((matchesWire_parts w e).mp hw).1]
  rfl

theorem wordThick_here (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (h : w.1 ∈ bases.2) :
    wordThick (leaf, w) = decide (sThick D u ℓ e) :=
  wordThick_reads all D u ℓ a g len Y key w e hw (leafColours_mem near h List.mem_cons_self)

theorem wordThick_hop (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (h : w.1 ∈ bases.2) (out : Bool) :
    wordThick (leaf, nearHop out (near, w)) = decide (sThick D u ℓ (if out then sOut a g D u ℓ e else sIn a g D u ℓ e)) := by
  apply wordThick_reads all D u ℓ a g len Y key _ _ (nearHop_code all D u ℓ a g len Y key w e hw h out)
  have hk := ((matchesWire_parts w e).mp hw).2.1.symm ▸ e.1.2.isLt
  apply leafColours_mem near h (List.mem_cons_of_mem _ ?_)
  exact addrWords_hop_mem_value all D ℓ a g len Y key near.2 w out hk

theorem wordWidth_reads (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (hW : nearWidthRequest (near, w) ∈ motThirdRaw all near) :
    P1Batch.bval (wordWidth (leaf, w)) = sWidth D u ℓ e := by
  let p := (packingArcEquiv ℕ a g).symm e
  have H := (matchesWire_parts w e).mp hw
  have hr := widthRequest_value D ℓ w
  change requestNumbers (nearWidthRequest (near, w)) = _ at hr
  rw [H.1, H.2.1, H.2.2] at hr
  exact cacheRead_field' D u _ _ _ _ ⟨_, hW, rfl⟩ hr

theorem leafWireRequest_mem (w : WireWords) (hw : w ∈ arcRoots all ctx) {r : P1Batch.Req}
    (hr : r ∈ leafWireFields (near, w)) : r ∈ motThirdRaw all near := by
  change r ∈ leafColours near ++ leafWires all near ++ (if all then leafEnergies ctx else [])
  exact List.mem_append_left _ (List.mem_append_right _ (leafWires_mem all near hw hr))

theorem wordWidth_root (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (h : w ∈ arcRoots all ctx) : P1Batch.bval (wordWidth (leaf, w)) = sWidth D u ℓ e :=
  wordWidth_reads all D u ℓ a g len Y key w e hw (leafWireRequest_mem all D u ℓ a g len Y key w h
    (List.mem_append_left _ List.mem_cons_self))

end At

end P1SolGreedy.SolDemand
