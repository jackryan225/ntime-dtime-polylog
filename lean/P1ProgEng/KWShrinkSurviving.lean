import P1ProgEng.KWShrinkWordLayout
import P1ProgEng.KWShrinkResidents
import P1P7.SolKernlocSupply

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkPayload
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open P1P7 P1P5.KW
open C10
open scoped P1ChkFinal.AstraC10
open P1ProgEng.SolKWR (HalfCode wordAt wordAt_halfCode)
attribute [local instance] P1P7.SolKernloc.instDecEqBaseT

noncomputable section

abbrev SurviveArgs := ResidentFrame × HalfCode × ArcRow

/-- Read one subdivision in its numbered output slot. The numbering is
computed in the incoming or outgoing fibre at the requested base and tag. -/
def survivingSlice (a b : ℕ) (incoming : Bool) (t : Fin 4) (i : Fin (SD a b t))
    (p : SurviveArgs) : List Bool :=
  let z : IdRow := (t.val, withLane p.2.2 0, i.val)
  let f := p.1.1
  let zs := localFibre a b f.1 f.2.1 incoming f.2.2 (childCode a p.1.2)
  let port := idRank a (∑ t, SD a b t) zs z
  wordAt p.2.1 (!incoming) port

theorem survivingSlice_poly (a b : ℕ) (incoming : Bool) (t : Fin 4) (i : Fin (SD a b t)) :
    Poly (survivingSlice a b incoming t i) := by
  unfold survivingSlice localFibre ballIds
  dsimp only
  apply P1ProgEng.SolKWR.poly_wordAt <;> fun_prop

/-- Read a complete surviving label in ordinal subdivision order. -/
def survivingWord (a b : ℕ) (incoming : Bool) (t : Fin 4) (p : SurviveArgs) : List Bool :=
  (List.ofFn fun i : Fin (SD a b t) => survivingSlice a b incoming t i p).flatten

theorem survivingWord_poly (a b : ℕ) (incoming : Bool) (t : Fin 4) :
    Poly (survivingWord a b incoming t) :=
  (fixedList_poly (fun p i => survivingSlice a b incoming t i p)
    (survivingSlice_poly a b incoming t)).compose flatten_poly

theorem concat_slices {n q : ℕ} (hq : 0 < q) (w : ∀ i : Fin q, Fin (splitWidth n q i) → Bool) :
    (List.ofFn fun i => List.ofFn (w i)).flatten =
      List.ofFn ((sliceWords n q hq).symm w) := by
  let rows (i : Fin q) := List.ofFn (w i)
  have hlen : (List.ofFn rows).flatten.length = n := by
    rw [flatten_ofFn_lengths]
    simpa only [rows, List.length_ofFn] using sum_splitWidth n q hq
  apply List.ext_getElem
  · exact hlen.trans List.length_ofFn.symm
  · intro r hr hr'
    change r < (List.ofFn rows).flatten.length at hr
    let bit : Fin n := ⟨r,hlen ▸ hr⟩
    let a := (sliceBits n q hq).symm bit
    have ha : sliceBits n q hq a = bit := Equiv.apply_symm_apply _ _
    have hval : (∑ k : Fin a.1.val, splitWidth n q (Fin.castLE a.1.isLt.le k)) + a.2.val = r :=
      (sliceBits_offset n q hq a.1 a.2).symm.trans (congrArg Fin.val ha)
    have hread := read_flatten_ofFn_at false rows a.1
      (Fin.cast (List.length_ofFn (f := w a.1)).symm a.2)
    simp only [rows, List.length_ofFn, Fin.val_cast, List.getElem_ofFn] at hread
    rw [hval] at hread
    change C10.read false (List.ofFn rows).flatten r = w a.1 a.2 at hread
    rw [C10.read, List.getElem?_eq_getElem hr, Option.getD_some] at hread
    rw [List.getElem_ofFn]
    exact hread

section Slices

set_option maxHeartbeats 500000
set_option maxRecDepth 2500

variable {a b g : ℕ} {δ factor : ℝ} {k : Type} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
variable {x : X.Base} {db : BallRows} (hdb : LocalRows X x db)
variable (layout : Bool) (j : TagW a) (l : BitWord g)
variable (m : X.packingData.Motif) (t : Fin 4) (i : Fin (SD a b t))

local notation "Y₀" => P1P7.SolKernloc.outputState (g := g) B ready X s layout
local notation "Q" => (X.shrinkStateIndex ready layout)
local notation "arc" => P1P7.SolKernloc.actualArc (ready := ready) X layout m t i


theorem withLane_zero_spec :
    withLane (arcCode X m.val) 0 = arcCode X (X.packingData.baseMotif m).val.val := by
  change withLane (arcCode X m.val) 0 = arcCode X (translateArc m.val (-m.val.1.1.2.2))
  simp only [withLane, arcCode, bundleCode, siteCode, translateArc, translateSite,
    add_neg_cancel, wordNum_zero]

include hdb in
theorem survivingSlot_spec (incoming : Bool)
    (hp : packedBase (X.packingData.survivingRole layout (pickRole incoming layout t) m) = (x,j)) :
    idRank a (∑ t, SD a b t)
      (localFibre a b (2 ^ g) db incoming layout (childCode a (siteCode X (x,j,l))))
      (t.val, withLane (arcCode X m.val) 0, i.val) =
      (bif incoming then ((Y₀).slots.actualGraph.target arc).2.val else (arc).2.val) := by
  let id : OldId X (SD a b) := ⟨t, X.packingData.baseMotif m, i⟩
  have hb : typedEnd X (SD a b) incoming layout id = (x,j) := by
    change packedBase (X.packingData.survivingRole layout (pickRole incoming layout t)
      (X.packingData.translateMotif m (-X.packingData.sourceLane m))) = _
    rw [PackingData.survivingRole_translate]
    exact hp
  rw [withLane_zero_spec X m]
  change idRank a (∑ t, SD a b t)
    (localFibre a b (2 ^ g) db incoming layout (packedCode X (x,j))) (idCode X id) = _
  rw [← numberSide_rank X hdb ready incoming layout (x,j) (by simp) id hb]
  cases incoming
  · rfl
  · change ((Q).incoming (.inl id)).2.val = ((Q).graph.base.target ((Q).outgoing (.inl id))).2.val
    rw [(Q).match_eq]

include hdb in
theorem survivingSource_spec {v : (Y₀).network.Site} (z : (Y₀).network.Half v)
    (hv : v = ((x,j),l))
    (hs : v = packedSiteEquiv (X.packingData.survivingRole layout (sourceRole layout t) m)) :
    survivingWord a b false t (((2 ^ g,db,layout),siteCode X (x,j,l)),@halfCode b g (Y₀) v z,arcCode X m.val) =
      List.ofFn (X.packingData.localSurvivingSource layout (SD a b) (fun n t => selW B X s n (layout,t))
        Q ready.count_pos m t (⟨fun e he => z.1 e (hs.trans he), fun e he => z.2 e (hs.trans he)⟩)) := by
  unfold survivingWord PackingData.localSurvivingSource
  rw [← concat_slices]
  congr 2
  funext i
  let e := P1P7.SolKernloc.actualArc (ready := ready) X layout m t i
  have hp : packedBase (X.packingData.survivingRole layout (pickRole false layout t) m) = (x,j) :=
    (congrArg Prod.fst (hv.symm.trans hs)).symm
  have he : v = (Y₀).network.src e := hs.trans (X.packingData.shrinkArc_endpoints layout (SD a b) Q ⟨t,m,i⟩).1.symm
  unfold survivingSlice
  dsimp only
  rw [survivingSlot_spec B ready X s hdb layout j l m t i false hp]
  refine ((wordAt_halfCode Y₀ v z (e).2).1).trans ?_
  apply P1ProgEng.SolKWR.ofFn_heq
  exact (P1P7.SolKernloc.halfReadOut (Y := Y₀) (u := v) z e he (e).2 rfl).symm.trans (cast_heq _ _).symm

include hdb in
theorem survivingTarget_spec {v : (Y₀).network.Site} (z : (Y₀).network.Half v)
    (hv : v = ((x,j),l))
    (hs : v = packedSiteEquiv (X.packingData.survivingRole layout (targetRole layout t) m)) :
    survivingWord a b true t (((2 ^ g,db,layout),siteCode X (x,j,l)),@halfCode b g (Y₀) v z,arcCode X m.val) =
      List.ofFn (X.packingData.localSurvivingTarget layout (SD a b) (fun n t => selW B X s n (layout,t))
        Q ready.count_pos m t (⟨fun e he => z.1 e (hs.trans he), fun e he => z.2 e (hs.trans he)⟩)) := by
  unfold survivingWord PackingData.localSurvivingTarget
  rw [← concat_slices]
  congr 2
  funext i
  let e := P1P7.SolKernloc.actualArc (ready := ready) X layout m t i
  have hp : packedBase (X.packingData.survivingRole layout (pickRole true layout t) m) = (x,j) :=
    (congrArg Prod.fst (hv.symm.trans hs)).symm
  have he : v = (Y₀).network.dst e := hs.trans (X.packingData.shrinkArc_endpoints layout (SD a b) Q ⟨t,m,i⟩).2.symm
  let k := ((Y₀).slots.actualGraph.target e).2
  unfold survivingSlice
  dsimp only
  rw [survivingSlot_spec B ready X s hdb layout j l m t i true hp]
  refine ((wordAt_halfCode Y₀ v z k).2).trans ?_
  apply P1ProgEng.SolKWR.ofFn_heq
  exact (P1P7.SolKernloc.halfReadIn (Y := Y₀) (u := v) z e he k rfl).symm.trans (cast_heq _ _).symm

end Slices

end
end P1ProgEng.SolKWS
