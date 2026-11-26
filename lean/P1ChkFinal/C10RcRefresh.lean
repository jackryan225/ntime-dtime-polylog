import P1ChkFinal.C10RcPoly

/-! The uniform refresh program on the list of radius-one data. -/

namespace P1ChkFinal.AstraC10

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.SpectralGeometry

noncomputable section

abbrev RefreshFrame := ℕ × List (ℕ × Option RefreshDatumCode)
abbrev RefreshInput := RefreshFrame × ℕ

def datumAt (z : RefreshFrame) (pos : ℕ) : RefreshDatumCode :=
  (readAt (0, none) z.2 pos).2.elim default id

def rowAt (z : RefreshFrame) (pos slot : ℕ) : SlotCode :=
  readAt default (datumAt z pos).1 slot

def widthAt (z : RefreshFrame) (pos slot lane : ℕ) : ℕ :=
  readAt 0 (rowAt z pos slot).2.2 lane

def termAt (z : RefreshFrame) (lane port slot : ℕ) : ℕ :=
  readAt 0 (readAt [] (readAt [] (datumAt z 0).2 lane) port) slot

/-- The parent contains one term row for each remaining lane. -/
def laneCount (z : RefreshFrame) : ℕ := (datumAt z 0).2.length

/-- The original coordinate before undoing the displacement of an incoming slot. -/
def fullLane (z : RefreshFrame) (port lane : ℕ) : ℕ := port * laneCount z + lane

/-- The incoming slots follow the parent and all its outgoing slots in the BFS list. -/
def inPos (a : ℕ) (slot : Fin (2 ^ a)) : ℕ := 1 + (2 ^ a + slot.val)

def tieCell (a : ℕ) (t : Tie (2 ^ a)) (z : RefreshFrame) (lane : ℕ) : ℕ :=
  let k := t.2.val.2
  let u := fullLane z t.2.val.1.val lane
  if t.1 then widthAt z 0 k.val u
  else
    let e := (rowAt z 0 k.val).2.1
    widthAt z (inPos a k) e.2.2 (u ^^^ e.2.1)

def externalEnd (D n slot : ℕ) (old : EndCode) : EndCode :=
  (old.2.2 + D * old.1, old.2.1 % n, slot)

def localEnd (D base port slot : ℕ) : EndCode := (port + D * base, 0, slot)

variable {a a₀ dH : ℕ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH)
variable (hd : dH + 1 ≤ 2 ^ a₀)

def refreshEnds (j : Fin (2 ^ a)) (r : RefreshSlot dH (2 ^ a₀)) (z : RefreshFrame) :
    EndCode × EndCode :=
  match r with
  | .inl i =>
    let old := rowAt z 0 j.val
    let s := (refreshSlots hd (.inl i)).val
    (externalEnd (2 ^ a) (laneCount z) s old.1, externalEnd (2 ^ a) (laneCount z) s old.2.1)
  | .inr (.inl h) =>
    let o := P.toSlotGraph.target (j, h)
    let i := P.toSlotGraph.target.symm (j, h)
    (localEnd (2 ^ a) z.1 o.1.val (refreshSlots hd (.inr (.inl o.2))).val,
     localEnd (2 ^ a) z.1 i.1.val (refreshSlots hd (.inr (.inl i.2))).val)
  | .inr (.inr h) =>
    let s := (refreshSlots hd (.inr (.inr h))).val
    (localEnd (2 ^ a) z.1 (finRotate (2 ^ a) j).val s,
     localEnd (2 ^ a) z.1 ((finRotate (2 ^ a)).symm j).val s)

variable {k : Type*} [Field k] {K K' : ℝ}
variable (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
variable (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

def refreshWidth (j : Fin (2 ^ a)) (r : RefreshSlot dH (2 ^ a₀)) (v : RefreshFrame × ℕ) : ℕ :=
  match r with
  | .inl _ => ∑ i : Fin (2 ^ a), widthAt v.1 0 j.val (fullLane v.1 i.val v.2)
  | .inr (.inl h) =>
    MotifConversion.supplyWidths F (fun t => tieCell a t v.1 v.2)
      (fun e => termAt v.1 v.2 e.1.val e.2.val) (j, h)
  | .inr (.inr _) => 0

def refreshRow (j : Fin (2 ^ a)) (s : Fin (2 ^ a₀)) (z : RefreshFrame) : SlotCode :=
  let r := (refreshSlots hd).symm s
  let e := refreshEnds P hd j r z
  (e.1, e.2, tabLike (fun v : RefreshFrame => (datumAt v 0).2) (refreshWidth P hdH hconn F j r) z)

def panelFor (j : Fin (2 ^ a)) (z : RefreshFrame) : PanelCode :=
  List.ofFn fun s => refreshRow P hd hdH hconn F j s z

/-- Port and slot tables are fixed once the template is fixed. The sole variable-size
tabulation follows the parent term rows, also on malformed data. -/
def refreshRc (v : RefreshInput) : Option PanelCode :=
  some (readAt [] (List.ofFn fun j => panelFor P hd hdH hconn F j v.1) v.2)

section Cost
variable {U : Type} [Codec U]

@[fun_prop] theorem poly_datumAt {z : U → RefreshFrame} {i : U → ℕ} (hz : Poly z) (hi : Poly i) :
    Poly (fun u => datumAt (z u) (i u)) := by
  unfold datumAt
  exact poly_defaultOption _ (poly_readAt _ hz.sndCompose hi).sndCompose

@[fun_prop] theorem poly_rowAt {z : U → RefreshFrame} {i s : U → ℕ} (hz : Poly z) (hi : Poly i) (hs : Poly s) :
    Poly (fun u => rowAt (z u) (i u) (s u)) :=
  poly_readAt default (poly_datumAt hz hi).fstCompose hs

@[fun_prop] theorem poly_widthAt {z : U → RefreshFrame} {i s l : U → ℕ}
    (hz : Poly z) (hi : Poly i) (hs : Poly s) (hl : Poly l) :
    Poly (fun u => widthAt (z u) (i u) (s u) (l u)) :=
  poly_readAt 0 (poly_rowAt hz hi hs).sndCompose.sndCompose hl

@[fun_prop] theorem poly_termAt {z : U → RefreshFrame} {l j h : U → ℕ}
    (hz : Poly z) (hl : Poly l) (hj : Poly j) (hh : Poly h) :
    Poly (fun u => termAt (z u) (l u) (j u) (h u)) :=
  poly_readAt 0 (poly_readAt [] (poly_readAt [] (poly_datumAt hz (poly_const 0)).sndCompose hl) hj) hh

@[fun_prop] theorem poly_laneCount {z : U → RefreshFrame} (hz : Poly z) :
    Poly (fun u => laneCount (z u)) := poly_lengthNat (poly_datumAt hz (poly_const 0)).sndCompose

@[fun_prop] theorem poly_fullLane {z : U → RefreshFrame} {p l : U → ℕ}
    (hz : Poly z) (hp : Poly p) (hl : Poly l) :
    Poly (fun u => fullLane (z u) (p u) (l u)) := poly_addNat (poly_mulNat hp (poly_laneCount hz)) hl

theorem poly_tieCell (t : Tie (2 ^ a)) : Poly (fun v : RefreshFrame × ℕ => tieCell a t v.1 v.2) := by
  cases ht : t.1 <;> simp only [tieCell, ht, Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem poly_refreshEnds (j : Fin (2 ^ a)) (r : RefreshSlot dH (2 ^ a₀)) :
    Poly (refreshEnds P hd j r) := by
  show Poly (fun z => refreshEnds P hd j r z)
  rcases r with i | h | h <;> simp only [refreshEnds, externalEnd, localEnd] <;> fun_prop

theorem poly_refreshWidth (j : Fin (2 ^ a)) (r : RefreshSlot dH (2 ^ a₀)) :
    Poly (refreshWidth P hdH hconn F j r) := by
  rcases r with i | h | h
  · apply poly_fixedSum
    intro p
    fun_prop
  · have copies := poly_copies (Refresh.tieMass (D := 2 ^ a)) F.scale
        (fun t (v : RefreshFrame × ℕ) => tieCell a t v.1 v.2) (fun t => poly_tieCell t)
    exact poly_addNat (poly_termAt (by fun_prop) (by fun_prop) (poly_const j.val) (poly_const h.val))
      (poly_mulNat copies (poly_const F.selectorBits))
  · exact poly_const 0

theorem poly_refreshRow (j : Fin (2 ^ a)) (s : Fin (2 ^ a₀)) :
    Poly (refreshRow P hd hdH hconn F j s) := by
  let r := (refreshSlots hd).symm s
  have p := poly_refreshEnds P hd j r
  have rows : Poly (fun z : RefreshFrame => (datumAt z 0).2) :=
    (poly_datumAt Poly.identity (poly_const 0)).sndCompose
  exact p.fstCompose.pair (p.sndCompose.pair (poly_tabLike rows (poly_refreshWidth P hdH hconn F j r)))

theorem poly_panelFor (j : Fin (2 ^ a)) : Poly (panelFor P hd hdH hconn F j) :=
  poly_fixedTab _ (poly_refreshRow P hd hdH hconn F j)

theorem poly_refreshRc : Poly (refreshRc P hd hdH hconn F) := by
  have ports : Poly (fun z : RefreshFrame => List.ofFn fun j => panelFor P hd hdH hconn F j z) :=
    poly_fixedTab _ (poly_panelFor P hd hdH hconn F)
  exact poly_someValue (poly_readAt [] (Easy.fst.poly.compose ports) Easy.snd.poly)

end Cost
end
end P1ChkFinal.AstraC10
