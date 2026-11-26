import P1ProgEng.KWShrinkC10Numbered
import P1ProgEng.KWShrinkC10WidthArithmetic

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7 (SD)

abbrev OldTerms := List (List (List ℕ))

def rootTerms (db : BallRows) (parent : ℕ) : OldTerms := (rowAt db parent).2.2.2

def laneCount (a : ℕ) (terms : OldTerms) : ℕ :=
  terms.length / (2 ^ colourBits a * oldDegree a * tagCount a)

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

def termField (layout : Bool) (t : ℕ) : ℕ := (bif layout then 5 else 1) + t

@[fun_prop] theorem rootTerms_poly : Poly (fun p : BallRows × ℕ => rootTerms p.1 p.2) := by
  unfold rootTerms
  fun_prop

@[fun_prop] theorem laneCount_poly (a : ℕ) : Poly (laneCount a) := by unfold laneCount; fun_prop

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

@[fun_prop] theorem termField_poly : Poly (fun p : Bool × ℕ => termField p.1 p.2) := by
  unfold termField
  fun_prop

end P1ProgEng.SolKWS.C10
