import P1ProgEng.KWShrinkC10Primitives
import P1ProgEng.KWShrinkC10Lanes

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication Code

/-- The products used by the C10 finite-axis codec. -/
abbrev EndRow := ℕ × ℕ × ℕ
abbrev SlotRow := EndRow × EndRow × List ℕ
abbrev DatumRow := List SlotRow × ℕ × ℕ × List (List (List ℕ))
abbrev BallRows := List (ℕ × Option DatumRow)

abbrev SiteRow := ℕ × ℕ × ℕ
abbrev PlaceRow := SiteRow × ℕ × ℕ
abbrev ArcRow := (SiteRow × ℕ) × ℕ × ℕ
abbrev BundleRow := SiteRow × ℕ

abbrev oldDegree (a : ℕ) : ℕ := 2 ^ a
abbrev colourBits (a : ℕ) : ℕ := 2 * oldDegree a + 1
abbrev tagCount (a : ℕ) : ℕ := 2 ^ packingTagBits (oldDegree a)

def rowAt (db : BallRows) (x : ℕ) : DatumRow := (lookup none db x).getD default

def hasRow (db : BallRows) (x : ℕ) : Bool := (lookup none db x).isSome

def slotAt (db : BallRows) (x i : ℕ) : SlotRow := read default (rowAt db x).1 i

def siteOf (e : ArcRow) : SiteRow := e.1.1

def outgoingRow (db : BallRows) (e : ArcRow) : EndRow := (slotAt db e.1.1.1 e.1.2).1

def sourceRow (e : ArcRow) : PlaceRow := (siteOf e, e.2)

def codedSiteTarget (a l : ℕ) (db : BallRows) (e : BundleRow) : BundleRow :=
  let out := (slotAt db e.1.1 e.2).1
  let shift := splitLane (oldDegree a) (tagCount a) l out.2.1
  ((out.1, e.1.2.1 ^^^ shift.2.2.1, e.1.2.2 ^^^ shift.2.2.2), out.2.2)

def codedTarget (a l : ℕ) (db : BallRows) (e : ArcRow) : ArcRow :=
  let shift := splitLane (oldDegree a) (tagCount a) l (outgoingRow db e).2.1
  (codedSiteTarget a l db e.1, e.2.1 ^^^ shift.1, e.2.2 ^^^ shift.2.1)

def thickPowers (a : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (colourBits a) => 2 ^ (colourBits a - 1 - i.val)

def codedThick (a : ℕ) (db : BallRows) (p : PlaceRow) : Bool :=
  let divisor := read 1 (thickPowers a) (rowAt db p.1.1).2.1
  decide ((p.2.1 / divisor) % 2 = 1)

def assignedRow (db : BallRows) (p : PlaceRow) : BundleRow :=
  ((p.1.1, p.1.2.1 ^^^ (rowAt db p.1.1).2.2.1, p.1.2.2), p.2.2)

def codedPlacement (a l : ℕ) (db : BallRows) (layout : Bool) (p : PlaceRow) : SiteRow :=
  bif codedThick a db p then p.1 else
    bif layout then (codedSiteTarget a l db (assignedRow db p)).1 else (assignedRow db p).1

def motifTest (a l : ℕ) (db : BallRows) (e : ArcRow) : Bool :=
  let target := codedTarget a l db e
  hasRow db e.1.1.1 && hasRow db target.1.1.1 &&
    !(codedThick a db (sourceRow e) && codedThick a db (sourceRow target))

def rolesRow (a l : ℕ) (db : BallRows) (layout : Bool) (e : ArcRow) :
    BundleRow × SiteRow × SiteRow :=
  let src := sourceRow e
  let dst := sourceRow (codedTarget a l db e)
  let srcThick := codedThick a db src
  let c := bif srcThick then dst else src
  let d := bif srcThick then src else dst
  let bundle := assignedRow db c
  (bundle, (codedSiteTarget a l db bundle).1, codedPlacement a l db layout d)

/-- Old address, old tag, outgoing slot, colour word, slot label. -/
def motifKey (a : ℕ) (e : ArcRow) : ℕ :=
  (((e.1.1.1 * tagCount a + e.1.1.2.1) * oldDegree a + e.1.2) * 2 ^ colourBits a +
    e.2.1) * oldDegree a + e.2.2

def oldLane (a l : ℕ) (e : ArcRow) : ℕ :=
  joinLane (oldDegree a) (tagCount a) l (e.2.1, e.2.2, e.1.1.2)

def oldWidth (a l : ℕ) (db : BallRows) (e : ArcRow) : ℕ :=
  read 0 (slotAt db e.1.1.1 e.1.2).2.2 (oldLane a l e)

def oldTerm (a l : ℕ) (db : BallRows) (e : ArcRow) : List ℕ :=
  let lane := read [] (rowAt db e.1.1.1).2.2.2 (oldLane a l e)
  read [] lane e.1.2

abbrev ArcCoordinates (a : ℕ) :=
  Fin (tagCount a) × Fin (oldDegree a) × Fin (2 ^ colourBits a) × Fin (oldDegree a)

def candidateArc (a x : ℕ) (t : ArcCoordinates a) : ArcRow :=
  (((x, t.1.val, 0), t.2.1.val), t.2.2.1.val, t.2.2.2.val)

/-- The finite colour, slot and tag coordinates depend only on the fixed degree. -/
noncomputable def baseMotifCandidates (a : ℕ) (x : ℕ) : List ArcRow :=
  List.ofFn fun j => candidateArc a x ((Fintype.equivFin (ArcCoordinates a)).symm j)

noncomputable def baseMotifRows (a l : ℕ) (db : BallRows) : List ArcRow :=
  ((unique (db.map Prod.fst)).flatMap (baseMotifCandidates a)).filter (motifTest a l db)

@[fun_prop] theorem rowAt_poly : Poly (fun p : BallRows × ℕ => rowAt p.1 p.2) := by
  exact (lookup_poly none).compose (getD_poly (default : DatumRow))

@[fun_prop] theorem hasRow_poly : Poly (fun p : BallRows × ℕ => hasRow p.1 p.2) :=
  (lookup_poly none).compose isSome_poly

@[fun_prop] theorem slotAt_poly : Poly (fun p : BallRows × ℕ × ℕ => slotAt p.1 p.2.1 p.2.2) := by
  unfold slotAt
  fun_prop

@[fun_prop] theorem siteOf_poly : Poly siteOf := by unfold siteOf; fun_prop

@[fun_prop] theorem outgoingRow_poly : Poly (fun p : BallRows × ArcRow => outgoingRow p.1 p.2) := by
  unfold outgoingRow
  fun_prop

@[fun_prop] theorem sourceRow_poly : Poly sourceRow := by unfold sourceRow; fun_prop

@[fun_prop] theorem joinLane_poly (d j l : ℕ) : Poly (joinLane d j l) := by unfold joinLane; fun_prop

@[fun_prop] theorem splitLane_poly (d j : ℕ) : Poly (fun p : ℕ × ℕ => splitLane d j p.1 p.2) := by
  unfold splitLane
  dsimp only
  fun_prop

@[fun_prop] theorem codedSiteTarget_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × BundleRow => codedSiteTarget a p.1 p.2.1 p.2.2) := by
  unfold codedSiteTarget
  dsimp only
  fun_prop

@[fun_prop] theorem codedTarget_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × ArcRow => codedTarget a p.1 p.2.1 p.2.2) := by
  unfold codedTarget
  dsimp only
  fun_prop

@[fun_prop] theorem codedThick_poly (a : ℕ) :
    Poly (fun p : BallRows × PlaceRow => codedThick a p.1 p.2) := by
  unfold codedThick
  have hc : Poly (fun p : BallRows × PlaceRow => (rowAt p.1 p.2.1.1).2.1) := by fun_prop
  have hd := ((Code.Poly.const (thickPowers a)).pair hc).compose (read_poly (1 : ℕ))
  have hv : Poly (fun p : BallRows × PlaceRow => p.2.2.1) := by fun_prop
  have hq := (hv.pair hd).compose div_poly
  have hm := (hq.pair (Code.Poly.const (2 : ℕ))).compose mod_poly
  exact (hm.pair (Code.Poly.const (1 : ℕ))).compose eq_poly

@[fun_prop] theorem assignedRow_poly :
    Poly (fun p : BallRows × PlaceRow => assignedRow p.1 p.2) := by
  unfold assignedRow
  fun_prop

@[fun_prop] theorem codedPlacement_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × Bool × PlaceRow => codedPlacement a p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold codedPlacement
  fun_prop

@[fun_prop] theorem motifTest_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × ArcRow => motifTest a p.1 p.2.1 p.2.2) := by
  unfold motifTest
  dsimp only
  fun_prop

@[fun_prop] theorem rolesRow_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × Bool × ArcRow => rolesRow a p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rolesRow
  dsimp only
  fun_prop

@[fun_prop] theorem motifKey_poly (a : ℕ) : Poly (motifKey a) := by unfold motifKey; fun_prop

@[fun_prop] theorem oldLane_poly (a : ℕ) : Poly (fun p : ℕ × ArcRow => oldLane a p.1 p.2) := by
  unfold oldLane joinLane
  fun_prop

@[fun_prop] theorem oldWidth_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × ArcRow => oldWidth a p.1 p.2.1 p.2.2) := by
  unfold oldWidth
  fun_prop

@[fun_prop] theorem oldTerm_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × ArcRow => oldTerm a p.1 p.2.1 p.2.2) := by
  unfold oldTerm
  dsimp only
  fun_prop

@[fun_prop] theorem baseMotifCandidates_poly (a : ℕ) : Poly (baseMotifCandidates a) := by
  unfold baseMotifCandidates
  apply fixedList_poly
  intro j
  unfold candidateArc
  fun_prop

theorem mem_baseMotifCandidates {a x : ℕ} {e : ArcRow} :
    e ∈ baseMotifCandidates a x ↔ ∃ t, candidateArc a x t = e := by
  unfold baseMotifCandidates
  constructor
  · intro h
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    exact ⟨_, hj⟩
  · rintro ⟨t, rfl⟩
    let e := Fintype.equivFin (ArcCoordinates a)
    exact List.mem_ofFn.mpr ⟨e t, congrArg (candidateArc a x) (e.symm_apply_apply t)⟩

theorem baseMotifCandidates_nodup (a x : ℕ) : (baseMotifCandidates a x).Nodup := by
  unfold baseMotifCandidates candidateArc
  apply List.nodup_ofFn_ofInjective
  intro i j h
  apply (Fintype.equivFin (ArcCoordinates a)).symm.injective
  exact Prod.ext (Fin.ext (congrArg (fun e : ArcRow => e.1.1.2.1) h))
    (Prod.ext (Fin.ext (congrArg (fun e : ArcRow => e.1.2) h))
      (Prod.ext (Fin.ext (congrArg (fun e : ArcRow => e.2.1) h))
        (Fin.ext (congrArg (fun e : ArcRow => e.2.2) h))))

theorem baseMotifRows_nodup (a l : ℕ) (db : BallRows) : (baseMotifRows a l db).Nodup := by
  unfold baseMotifRows
  apply List.Nodup.filter
  apply List.nodup_flatMap.mpr
  refine ⟨fun x _ => baseMotifCandidates_nodup a x, (unique_spec _).1.imp ?_⟩
  intro x y hxy e hx hy
  obtain ⟨t, ht⟩ := mem_baseMotifCandidates.mp hx
  obtain ⟨u, hu⟩ := mem_baseMotifCandidates.mp hy
  exact hxy (congrArg (fun e : ArcRow => e.1.1.1) (ht.trans hu.symm))

@[fun_prop] theorem baseMotifRows_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows => baseMotifRows a p.1 p.2) := by
  unfold baseMotifRows
  have haddr : Poly (fun db : BallRows => unique (db.map Prod.fst)) :=
    (Code.Poly.maps _ poly_fst).compose unique_poly
  have hc : Poly (fun db : BallRows => (unique (db.map Prod.fst)).flatMap (baseMotifCandidates a)) :=
    (haddr.compose (Code.Poly.maps _ (baseMotifCandidates_poly a))).compose flatten_poly
  have ht : Poly (fun p : (ℕ × BallRows) × ArcRow => motifTest a p.1.1 p.1.2 p.2) := by
    fun_prop
  exact (Code.Poly.identity.pair (poly_snd.compose hc)).compose (filterWith_poly _ ht)

end P1ProgEng.SolKWS.C10
