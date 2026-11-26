import P1P7.SolKernlocDemand
import P1P7.SolKernlocSlots

namespace P1P7.SolKernloc

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.NetworkKernel

attribute [local instance] instDecEqBaseT

section Half

variable {a G G' : ℕ} {Y : State a G} {Y' : State a G'}
variable {u : Y.network.Site} {u' : Y'.network.Site}

def SlotOut (z : Y.network.Half u) (z' : Y'.network.Half u') : Prop :=
  ∀ k, HEq (z'.1 (outEdge Y' u' k) (outEdge_src Y' u' k))
    (z.1 (outEdge Y u k) (outEdge_src Y u k))

def SlotIn (z : Y.network.Half u) (z' : Y'.network.Half u') : Prop :=
  ∀ k, HEq (z'.2 (inEdge Y' u' k) (inEdge_dst Y' u' k))
    (z.2 (inEdge Y u k) (inEdge_dst Y u k))

theorem halfReadOut (z : Y.network.Half u) (e : Y.network.Edge) (he : u = Y.network.src e)
    (k : Fin (2 ^ a)) (hk : e.2 = k) :
    HEq (z.1 e he) (z.1 (outEdge Y u k) (outEdge_src Y u k)) := by
  obtain ⟨p, i⟩ := e
  change u = p at he
  subst p
  change i = k at hk
  subst i
  rfl

theorem halfReadIn (z : Y.network.Half u) (e : Y.network.Edge) (he : u = Y.network.dst e)
    (k : Fin (2 ^ a)) (hk : (Y.slots.actualGraph.target e).2 = k) :
    HEq (z.2 e he) (z.2 (inEdge Y u k) (inEdge_dst Y u k)) := by
  have h : e = inEdge Y u k := by
    apply Y.slots.actualGraph.target.injective
    change Y.slots.actualGraph.target e = Y.slots.actualGraph.target (Y.slots.actualGraph.target.symm (u, k))
    rw [Equiv.apply_symm_apply]
    exact Prod.ext he.symm hk
  subst e
  rfl

theorem halfEquiv_slotOut (Y : State a G) (Y' : State a G') (u : Y.network.Site) (u' : Y'.network.Site)
    (hout : ∀ k, Y.network.Payload ((outFib Y u).symm k).1 = Y'.network.Payload ((outFib Y' u').symm k).1)
    (hin : ∀ k, Y.network.Payload ((inFib Y u).symm k).1 = Y'.network.Payload ((inFib Y' u').symm k).1)
    (z : Y.network.Half u) :
    @SlotOut a G G' Y Y' u u' z (halfEquiv Y Y' u u' hout hin z) := by
  intro k
  exact halfEquiv_out Y Y' u u' hout hin z k

theorem halfEquiv_slotIn (Y : State a G) (Y' : State a G') (u : Y.network.Site) (u' : Y'.network.Site)
    (hout : ∀ k, Y.network.Payload ((outFib Y u).symm k).1 = Y'.network.Payload ((outFib Y' u').symm k).1)
    (hin : ∀ k, Y.network.Payload ((inFib Y u).symm k).1 = Y'.network.Payload ((inFib Y' u').symm k).1)
    (z : Y.network.Half u) :
    @SlotIn a G G' Y Y' u u' z (halfEquiv Y Y' u u' hout hin z) := by
  intro k
  exact halfEquiv_in Y Y' u u' hout hin z k

end Half

section Place

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}
variable {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
variable {L L' : Bool} (hLL : L = L') (j : TagW a) (l : BitWord g)

noncomputable def oldPlacedEquiv :
    Placed (oplace X L) X.network.Half ((x, j), l) ≃
      Placed (oplace X' L') X'.network.Half ((pb X X' x, j), l) :=
  placedCongr (posEquiv hg hg' L L' hLL j l) (fun u =>
    oldHalfEquiv u.1 (placed_good hg L j l u.1 u.2).1 (placed_good hg L j l u.1 u.2).2)

theorem oldPlaced_out (pa : Placed (oplace X L) X.network.Half ((x, j), l))
    (u : X.network.Site) (hu : ((x, j), l) = oplace X L u)
    (hu' : ((pb X X' x, j), l) = oplace X' L' (tPos X X' u)) :
    SlotOut (pa u hu) (oldPlacedEquiv hg hg' hLL j l pa (tPos X X' u) hu') := by
  intro k
  have e : oldPlacedEquiv hg hg' hLL j l pa (tPos X X' u) hu' =
      oldHalfEquiv u (placed_good hg L j l u hu).1 (placed_good hg L j l u hu).2 (pa u hu) :=
    placedCongr_apply (posEquiv hg hg' L L' hLL j l) _ pa u hu
  rw [e]
  exact halfEquiv_out X X' u (tPos X X' u) _ _ (pa u hu) k

theorem oldPlaced_in (pa : Placed (oplace X L) X.network.Half ((x, j), l))
    (u : X.network.Site) (hu : ((x, j), l) = oplace X L u)
    (hu' : ((pb X X' x, j), l) = oplace X' L' (tPos X X' u)) :
    SlotIn (pa u hu) (oldPlacedEquiv hg hg' hLL j l pa (tPos X X' u) hu') := by
  intro k
  have e : oldPlacedEquiv hg hg' hLL j l pa (tPos X X' u) hu' =
      oldHalfEquiv u (placed_good hg L j l u hu).1 (placed_good hg L j l u hu).2 (pa u hu) :=
    placedCongr_apply (posEquiv hg hg' L L' hLL j l) _ pa u hu
  rw [e]
  exact halfEquiv_in X X' u (tPos X X' u) _ _ (pa u hu) k

end Place

section Pull

variable {a b g : ℕ} {δ factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
variable {X X' : State a (packingLaneBits a g)}

theorem pull_out (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    {v : (X.Base × TagW a) × BitWord g} {v' : (X'.Base × TagW a) × BitWord g}
    (pa : Placed ((oplace X (layoutBit B X s))) X.network.Half v) (pa' : Placed ((oplace X' (layoutBit B X' s'))) X'.network.Half v')
    (hc : ∀ u (hu : v = (oplace X (layoutBit B X s)) u) (hu' : v' = (oplace X' (layoutBit B X' s')) (tPos X X' u)),
      SlotOut (pa u hu) (pa' (tPos X X' u) hu')) :
    OutCanon (pullPlaced B ready κ hκ X s v pa) (pullPlaced B ready κ hκ X' s' v' pa') := by
  intro p hp hp' α hα
  subst p
  exact hc (packingInputSites X.Base a g (sourcePosition α)) _ _ α.1.2

theorem pull_in {x : X.Base} (hg : Good3 X X' x) (j : TagW a) (l : BitWord g)
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (pa : Placed ((oplace X (layoutBit B X s))) X.network.Half ((x, j), l))
    (pa' : Placed ((oplace X' (layoutBit B X' s'))) X'.network.Half ((pb X X' x, j), l))
    (hc : ∀ u (hu : ((x, j), l) = (oplace X (layoutBit B X s)) u)
      (hu' : ((pb X X' x, j), l) = (oplace X' (layoutBit B X' s')) (tPos X X' u)),
      SlotIn (pa u hu) (pa' (tPos X X' u) hu')) :
    InCanon (pullPlaced B ready κ hκ X s ((x, j), l) pa)
      (pullPlaced B ready κ hκ X' s' ((pb X X' x, j), l) pa') := by
  intro p hp hp' α hα hα'
  let u := packingInputSites X.Base a g p
  have hu : ((x, j), l) = (oplace X (layoutBit B X s)) u := by
    change _ = X.packingData.shrinkPlace (layoutBit B X s) ((packingInputSites X.Base a g).symm u)
    rw [Equiv.symm_apply_apply]
    exact hp
  have hu' : ((pb X X' x, j), l) = (oplace X' (layoutBit B X' s')) (tPos X X' u) := by
    change _ = X'.packingData.shrinkPlace (layoutBit B X' s')
      ((packingInputSites X'.Base a g).symm (packingInputSites X'.Base a g (tP X X' p)))
    rw [Equiv.symm_apply_apply]
    exact hp'
  let e := X.packingInputIso.edge α
  let e' := X'.packingInputIso.edge (tA X X' α)
  have he : u = X.network.dst e :=
    (congrArg X.packingInputIso.site hα).trans (X.packingInputIso.dst α)
  have he' : tPos X X' u = X'.network.dst e' :=
    (congrArg X'.packingInputIso.site hα').trans (X'.packingInputIso.dst (tA X X' α))
  let k := (X.slots.actualGraph.target e).2
  have hout : SGood X X' e.1.1 := by
    have q := (placed_good hg (layoutBit B X s) j l u hu).2 k
    have h : X.slots.base.target (e.1.1, e.2) = (u.1, k) :=
      Prod.ext (congrArg Prod.fst he).symm rfl
    have hb := (Equiv.symm_apply_eq X.slots.base.target).mpr h.symm
    have hbase := congrArg Prod.fst hb
    exact hbase ▸ q
  have hk' : (X'.slots.actualGraph.target e').2 = k := hout.tgt2 e.2 |>.symm
  change HEq ((pa' (tPos X X' u) hu').2 e' he') ((pa u hu).2 e he)
  exact (halfReadIn _ e' he' k hk').trans ((hc u hu hu' k).trans (halfReadIn _ e he k rfl).symm)

end Pull

end P1P7.SolKernloc
