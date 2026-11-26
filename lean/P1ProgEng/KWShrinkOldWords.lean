import P1ProgEng.KWShrinkResidents
import P1P7.SolKernlocPlaced

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.NetworkKernel
open P1P7 P1P5.KW P1ChkFinal
open C10
open scoped P1ChkFinal.AstraC10
open P1ProgEng.SolKWR (HalfCode wordAt wordAt_halfCode)

def positionMatches (p : (ℕ × ℕ) × PosCode) : Bool :=
  decide (p.1.1 = p.2.1.1) && decide (p.1.2 = p.2.1.2)

theorem positionMatches_poly : Poly positionMatches := by
  unfold positionMatches
  exact ((C10.eqOn_poly (by fun_prop) (by fun_prop)).pair
    (C10.eqOn_poly (by fun_prop) (by fun_prop))).compose bool_and_poly

def oldHalfAt (p : (ℕ × ℕ) × List PosCode) : HalfCode :=
  ((p.2.filter fun q => positionMatches (p.1,q)).headD default).2

@[fun_prop] theorem oldHalfAt_poly : Poly oldHalfAt :=
  ((filterWith_poly _ positionMatches_poly).compose (head_poly (default : PosCode))).sndCompose

/-- The same list relation as PlacedList with the target site type abstracted
from its network. -/
def PositionList {a G : ℕ} (X : State a G) {V : Type}
    (place : X.network.Site → V) (v : V)
    (pa : Placed place X.network.Half v) (ps : List PosCode) : Prop :=
  ∃ us : List {u : X.network.Site // v = place u}, us.Nodup ∧ (∀ u, u ∈ us) ∧
    ps = us.map fun u => ((addr X u.val.1,bwNum u.val.2),halfCode X u.val (pa u.val u.property))

theorem oldHalfAt_spec {a G : ℕ} {V : Type}
    (X : State a G) (place : X.network.Site → V) (v : V)
    (pa : Placed place X.network.Half v) (ps : List PosCode)
    (hs : PositionList X place v pa ps) (p : X.network.Site) (hp : v = place p) :
    oldHalfAt ((addr X p.1,bwNum p.2),ps) = halfCode X p (pa p hp) := by
  obtain ⟨us, -, hall, rfl⟩ := hs
  let u : {u : X.network.Site // v = place u} := ⟨p,hp⟩
  let code (u : {u : X.network.Site // v = place u}) : PosCode :=
    ((addr X u.val.1,bwNum u.val.2),halfCode X u.val (pa u.val u.property))
  let selected := (us.map code).filter fun q => positionMatches ((addr X p.1,bwNum p.2),q)
  have hex : code u ∈ selected :=
    List.mem_filter.mpr ⟨List.mem_map_of_mem (hall u), by
      simp only [positionMatches, code, u, decide_true, Bool.and_self]⟩
  have hu (q : PosCode) (hq : q ∈ selected) : q = code u := by
    obtain ⟨hm, ht⟩ := List.mem_filter.mp hq
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hm
    simp only [positionMatches, code, Bool.and_eq_true, decide_eq_true_eq] at ht
    have hw : w = u := Subtype.ext (Prod.ext
      (P1ChkFinal.addr_injective X ht.1.symm)
      (C10.bitWord_number_injective G ht.2.symm))
    rw [hw]
  change (selected.headD default).2 = (code u).2
  cases h : selected with
  | nil => rw [h] at hex; cases hex
  | cons q qs => exact congrArg Prod.snd (hu q (h.symm ▸ List.mem_cons_self))

def packedWord (a : ℕ) (incoming : Bool) (p : RoleArgs × List PosCode × ArcRow) : List Bool :=
  let f := p.1
  let e := p.2.2
  let row := bif incoming then codedTarget a f.1 f.2.1 e else e
  let k := bif incoming then (outgoingRow f.2.1 e).2.2 else e.1.2
  wordAt (oldHalfAt ((row.1.1.1, oldLane a f.1 row),p.2.1)) (!incoming) k

@[fun_prop] theorem packedWord_poly (a : ℕ) (incoming : Bool) : Poly (packedWord a incoming) := by
  cases incoming <;> unfold packedWord wordAt <;>
    simp only [Bool.cond_true, Bool.cond_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] <;>
    exact P1ChkFinal.AstraC10.poly_readAt [] (by fun_prop) (by fun_prop)

section Spec

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

variable {a g : ℕ} (X : State a (packingLaneBits a g))
variable (layout : Bool) {v : (X.Base × TagW a) × BitWord g}
variable (pa : Placed (oplace (g := g) X layout) X.network.Half v) (ps : List PosCode)
variable (hps : PositionList X (oplace (g := g) X layout) v pa ps)

noncomputable def packedPull : P1P7.SolKernloc.PH X layout v :=
  fun p hp => X.packingInputIso.pullHalf p (pa (X.packingInputIso.site p) (by
    refine hp.trans ?_
    change X.packingData.shrinkPlace layout p =
      X.packingData.shrinkPlace layout ((packingInputSites X.Base a g).symm
        (packingInputSites X.Base a g p))
    exact congrArg (X.packingData.shrinkPlace layout)
      ((packingInputSites X.Base a g).symm_apply_apply p).symm))

variable {db : BallRows} (hdb : GraphRows X db) (e : OldArc X)

include hps in
theorem packedWord_out (hp : v = X.packingData.shrinkPlace layout (sourcePosition e)) :
    packedWord a false ((2 ^ g,db,layout),ps,arcCode X e) =
      List.ofFn ((packedPull (g := g) X layout pa (sourcePosition e) hp).1 e rfl) := by
  have hu : v = (oplace (g := g) X layout) (e.1.1.1,oldLaneWord X e) := by
    refine hp.trans ?_
    change X.packingData.shrinkPlace layout (sourcePosition e) =
      X.packingData.shrinkPlace layout ((packingInputSites X.Base a g).symm (e.1.1.1,oldLaneWord X e))
    rw [show (e.1.1.1,oldLaneWord X e) = packingInputSites X.Base a g (sourcePosition e) from rfl,
      Equiv.symm_apply_apply]
  unfold packedWord
  dsimp only
  rw [Bool.cond_false, Bool.cond_false, Bool.not_false, oldLane_code]
  change wordAt (oldHalfAt ((addr X e.1.1.1,bwNum (oldLaneWord X e)),ps)) true e.1.2.val = _
  rw [oldHalfAt_spec X (oplace (g := g) X layout) v pa ps hps _ hu]
  exact (wordAt_halfCode X _ _ e.1.2).1

include hps hdb in
theorem packedWord_in (hs : hasRow db (addr X e.1.1.1) = true)
    (hp : v = X.packingData.shrinkPlace layout (sourcePosition (X.packingData.actual e))) :
    packedWord a true ((2 ^ g,db,layout),ps,arcCode X e) =
      List.ofFn ((packedPull (g := g) X layout pa (sourcePosition (X.packingData.actual e)) hp).2 e rfl) := by
  let q := X.packingData.actual e
  let u := packingInputSites X.Base a g (sourcePosition q)
  let eo := X.packingInputIso.edge e
  have hu : v = (oplace (g := g) X layout) u := by
    refine hp.trans ?_
    change X.packingData.shrinkPlace layout (sourcePosition q) =
      X.packingData.shrinkPlace layout ((packingInputSites X.Base a g).symm u)
    rw [Equiv.symm_apply_apply]
  have he : u = X.network.dst eo := X.packingInputIso.dst e
  have hk : (X.slots.actualGraph.target eo).2 = q.1.2 := rfl
  unfold packedWord
  dsimp only
  rw [Bool.cond_true, Bool.cond_true, Bool.not_true, codedTarget_spec hdb e hs, oldLane_code]
  change wordAt (oldHalfAt ((addr X q.1.1.1,bwNum (oldLaneWord X q)),ps)) false
    (outgoingRow db (arcCode X e)).2.2 = _
  have hslot : (outgoingRow db (arcCode X e)).2.2 = q.1.2.val := by
    unfold outgoingRow
    change ((slotAt db (addr X e.1.1.1) e.1.2.val).1).2.2 = q.1.2.val
    rw [hdb.out _ _ hs]
    rfl
  rw [hslot]
  change wordAt (oldHalfAt ((addr X u.1,bwNum u.2),ps)) false q.1.2.val = _
  rw [oldHalfAt_spec X (oplace (g := g) X layout) v pa ps hps u hu]
  refine ((wordAt_halfCode X u (pa u hu) q.1.2).2).trans ?_
  exact P1ProgEng.SolKWR.ofFn_heq ((P1P7.SolKernloc.halfReadIn (Y := X) (u := u)
    (pa u hu) eo he q.1.2 hk).symm)

end Spec

end P1ProgEng.SolKWS
