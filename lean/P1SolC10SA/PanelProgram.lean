import P1SolC10SA.Numbered
import P1SolC10SA.WidthArithmetic

namespace P1SolC10SA.SolShrink

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7 (SD)

abbrev InputRows := ((ℕ × BallRows) × Bool) × ℕ
abbrev OldTerms := List (List (List ℕ))

def rootTerms (db : BallRows) (parent : ℕ) : OldTerms := (rowAt db parent).2.2.2

def laneCount (a : ℕ) (terms : OldTerms) : ℕ :=
  terms.length / (2 ^ colourBits a * oldDegree a * tagCount a)

def addressChild (a parent tag : ℕ) : ℕ := tagCount a * parent + tag

def rotateTag (a : ℕ) (incoming : Bool) (tag : ℕ) : ℕ :=
  (tag + (bif incoming then tagCount a - 1 else 1)) % tagCount a

def dummyEnd (a : ℕ) (incoming : Bool) (parent tag slot : ℕ) : EndRow :=
  (addressChild a parent (rotateTag a incoming tag), 0, slot)

def genuineEnd (a total : ℕ) (incoming : Bool) (args : RoleArgs) (ids : List IdRow)
    (z : IdRow) : EndRow :=
  let src := idEnd a false args z
  let dst := idEnd a true args z
  let w := childCode a (bif incoming then src else dst)
  let far := idFibre a (!incoming) args w ids
  (w, dst.2.2 ^^^ src.2.2, idRank a total far z)

def endRecord (a total : ℕ) (incoming : Bool) (args : RoleArgs) (ids : List IdRow)
    (parent tag slot : ℕ) (z : Option IdRow) : EndRow :=
  bif z.isSome then genuineEnd a total incoming args ids (z.getD default)
  else dummyEnd a incoming parent tag slot

def bundleKey (a : ℕ) (b : BundleRow) : ℕ := childCode a b.1 * oldDegree a + b.2

def bundleRankNum (a : ℕ) (args : RoleArgs) (motifs : List ArcRow)
    (b : BundleRow) (e : ArcRow) : ℕ :=
  (motifs.filter fun r =>
    decide (bundleKey a (rolesRow a args.1 args.2.1 args.2.2 r).1 = bundleKey a b) &&
    decide (motifKey a r < motifKey a e)).length

def widthIfThick (a l : ℕ) (db : BallRows) (e : ArcRow) : ℕ :=
  bif codedThick a db (sourceRow e) && codedThick a db (sourceRow (codedTarget a l db e))
  then oldWidth a l db e else 0

def bundleWidthNum (a l : ℕ) (db : BallRows) (b : BundleRow) : ℕ :=
  ∑ u : Fin (2 ^ colourBits a), ∑ h : Fin (oldDegree a),
    widthIfThick a l db (b, u.val, h.val)

def withLane (e : ArcRow) (l : ℕ) : ArcRow :=
  (((e.1.1.1, e.1.1.2.1, l), e.1.2), e.2)

def residualIndex (a : ℕ) (args : RoleArgs) (z : IdRow) (l : ℕ) : ℕ :=
  l ^^^ (idEnd a false args z).2.2

def termField (layout : Bool) (t : ℕ) : ℕ := (bif layout then 5 else 1) + t

section Widths

variable {k : Type*} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

noncomputable def genuineWidth (a : ℕ) (sd : Fin 4 → ℕ) (args : RoleArgs)
    (motifs : List ArcRow) (z : IdRow) (l : ℕ) : ℕ :=
  let e := withLane z.2.1 (residualIndex a args z l)
  let b := (rolesRow a args.1 args.2.1 args.2.2 e).1
  let ab := splitWidthNum (bundleWidthNum a args.1 args.2.1 b)
    (PackingData.pieceCount (oldDegree a) (colourBits a)) (bundleRankNum a args motifs b e)
  let cd := oldWidth a args.1 args.2.1 e
  let v := read 0 (oldTerm a args.1 args.2.1 e) (termField args.2.2 z.1)
  splitWidthNum (supplyWidthNum B ab cd v) (read 1 (List.ofFn sd) z.1) z.2.2

noncomputable def widthAt (a : ℕ) (sd : Fin 4 → ℕ) (args : RoleArgs)
    (motifs : List ArcRow) (z : Option IdRow) (l : ℕ) : ℕ :=
  bif z.isSome then genuineWidth B a sd args motifs (z.getD default) l else 0

noncomputable def widthColumn (a : ℕ) (sd : Fin 4 → ℕ) (args : RoleArgs)
    (motifs : List ArcRow) (z : Option IdRow) (lanes : List ℕ) : List ℕ :=
  lanes.map (fun l => widthAt B a sd args motifs z l)

abbrev PanelArgs := RoleArgs × List ArcRow × List IdRow × List ℕ × (ℕ × ℕ)

noncomputable def panelSlot (a : ℕ) (sd : Fin 4 → ℕ) (p : PanelArgs) (slot : ℕ) : SlotRow :=
  let args := p.1
  let motifs := p.2.1
  let ids := p.2.2.1
  let lanes := p.2.2.2.1
  let parent := p.2.2.2.2.1
  let tag := p.2.2.2.2.2
  let total := ∑ t, sd t
  let child := addressChild a parent tag
  let out := idAt a total (idFibre a false args child ids) slot
  let inc := idAt a total (idFibre a true args child ids) slot
  (endRecord a total false args ids parent tag slot out,
    endRecord a total true args ids parent tag slot inc,
    widthColumn B a sd args motifs out lanes)

noncomputable def recompute (a b : ℕ) (p : InputRows) : Option (List SlotRow) :=
  let parent := p.1.1.1
  let db := p.1.1.2
  let terms := rootTerms db parent
  let l := laneCount a terms
  let args : RoleArgs := (l, db, p.1.2)
  let motifs := baseMotifRows a l db
  let sd := SD a b
  let ids := idRows sd motifs
  let lanes := limitedPositions terms l
  some (List.ofFn fun i : Fin (2 ^ b) =>
    panelSlot B a sd (args, motifs, ids, lanes, parent, p.2) i.val)

end Widths

@[fun_prop] theorem rootTerms_poly : Poly (fun p : BallRows × ℕ => rootTerms p.1 p.2) := by
  unfold rootTerms
  fun_prop

@[fun_prop] theorem laneCount_poly (a : ℕ) : Poly (laneCount a) := by unfold laneCount; fun_prop

@[fun_prop] theorem addressChild_poly (a : ℕ) :
    Poly (fun p : ℕ × ℕ => addressChild a p.1 p.2) := by unfold addressChild; fun_prop

@[fun_prop] theorem rotateTag_poly (a : ℕ) (incoming : Bool) : Poly (rotateTag a incoming) := by
  unfold rotateTag
  fun_prop

@[fun_prop] theorem dummyEnd_poly (a : ℕ) (incoming : Bool) :
    Poly (fun p : ℕ × ℕ × ℕ => dummyEnd a incoming p.1 p.2.1 p.2.2) := by
  unfold dummyEnd
  fun_prop

@[fun_prop] theorem genuineEnd_poly (a total : ℕ) (incoming : Bool) :
    Poly (fun p : RoleArgs × List IdRow × IdRow => genuineEnd a total incoming p.1 p.2.1 p.2.2) := by
  unfold genuineEnd
  dsimp only
  fun_prop

@[fun_prop] theorem endRecord_poly (a total : ℕ) (incoming : Bool) :
    Poly (fun p : RoleArgs × List IdRow × ℕ × ℕ × ℕ × Option IdRow =>
      endRecord a total incoming p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold endRecord
  fun_prop

@[fun_prop] theorem bundleKey_poly (a : ℕ) : Poly (bundleKey a) := by unfold bundleKey; fun_prop

@[fun_prop] theorem bundleRankNum_poly (a : ℕ) :
    Poly (fun p : RoleArgs × List ArcRow × BundleRow × ArcRow =>
      bundleRankNum a p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let hit (p : (RoleArgs × BundleRow × ArcRow) × ArcRow) :=
    decide (bundleKey a (rolesRow a p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2).1 = bundleKey a p.1.2.1) &&
    decide (motifKey a p.2 < motifKey a p.1.2.2)
  have ph : Poly hit := by
    unfold hit
    exact ((eqOn_poly (by fun_prop) (by fun_prop)).pair
      (ltOn_poly (by fun_prop) (by fun_prop))).compose bool_and_poly
  have hi : Poly (fun p : RoleArgs × List ArcRow × BundleRow × ArcRow => ((p.1,p.2.2),p.2.1)) := by
    fun_prop
  exact (hi.compose (filterWith_poly hit ph)).compose length_poly

@[fun_prop] theorem widthIfThick_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × ArcRow => widthIfThick a p.1 p.2.1 p.2.2) := by
  unfold widthIfThick
  fun_prop

theorem fixedSum_poly {I : Type} [Codec I] {n : ℕ} (f : I → Fin n → ℕ)
    (hf : ∀ j, Poly (fun i => f i j)) : Poly (fun i => ∑ j, f i j) := by
  induction n with
  | zero => simpa only [Fin.sum_univ_zero] using (Code.Poly.const (X := I) (0 : ℕ))
  | succ n ih =>
    simpa only [Fin.sum_univ_succ] using
      ((hf 0).pair (ih (fun i j => f i j.succ) (fun j => hf j.succ))).compose add_poly

@[fun_prop] theorem bundleWidthNum_poly (a : ℕ) :
    Poly (fun p : ℕ × BallRows × BundleRow => bundleWidthNum a p.1 p.2.1 p.2.2) := by
  unfold bundleWidthNum
  apply fixedSum_poly
  intro u
  apply fixedSum_poly
  intro h
  fun_prop

@[fun_prop] theorem withLane_poly : Poly (fun p : ArcRow × ℕ => withLane p.1 p.2) := by
  unfold withLane
  fun_prop

@[fun_prop] theorem residualIndex_poly (a : ℕ) :
    Poly (fun p : RoleArgs × IdRow × ℕ => residualIndex a p.1 p.2.1 p.2.2) := by
  unfold residualIndex
  fun_prop

@[fun_prop] theorem termField_poly : Poly (fun p : Bool × ℕ => termField p.1 p.2) := by
  unfold termField
  fun_prop

section Program

variable {k : Type*} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

@[fun_prop] theorem genuineWidth_poly (a : ℕ) (sd : Fin 4 → ℕ) :
    Poly (fun p : RoleArgs × List ArcRow × IdRow × ℕ => genuineWidth B a sd p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold genuineWidth
  dsimp only
  fun_prop

@[fun_prop] theorem widthAt_poly (a : ℕ) (sd : Fin 4 → ℕ) :
    Poly (fun p : RoleArgs × List ArcRow × Option IdRow × ℕ =>
      widthAt B a sd p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold widthAt
  fun_prop

@[fun_prop] theorem widthColumn_poly (a : ℕ) (sd : Fin 4 → ℕ) :
    Poly (fun p : RoleArgs × List ArcRow × Option IdRow × List ℕ =>
      widthColumn B a sd p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hm : Poly (fun p : (RoleArgs × List ArcRow × Option IdRow) × ℕ => widthAt B a sd p.1.1 p.1.2.1 p.1.2.2 p.2) := by fun_prop
  have hi : Poly (fun p : RoleArgs × List ArcRow × Option IdRow × List ℕ =>
    ((p.1, p.2.1, p.2.2.1), p.2.2.2)) := by fun_prop
  exact hi.compose (mapWith_poly _ hm)

@[fun_prop] theorem panelSlot_poly (a : ℕ) (sd : Fin 4 → ℕ) :
    Poly (fun p : PanelArgs × ℕ => panelSlot B a sd p.1 p.2) := by
  unfold panelSlot
  dsimp only
  fun_prop

theorem recompute_poly (a b : ℕ) : Poly (recompute B a b) := by
  unfold recompute
  dsimp only
  apply Code.Poly.compose _ poly_some
  apply fixedList_poly
  intro i
  fun_prop

end Program

end P1SolC10SA.SolShrink
