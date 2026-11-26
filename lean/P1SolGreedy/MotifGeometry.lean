import P1SolGreedy.MotifLeaf
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

theorem sumWordRange (n : ℕ) (f : NumberWord → ℕ) :
    ((wordRange (tally n)).map f).sum = ∑ j : Fin n, f (Carry.born j.val) := by
  rw [wordRange_tally, List.map_map]
  have h : (List.range n).map (f ∘ Carry.born) = List.ofFn (fun j : Fin n => f (Carry.born j.val)) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, List.length_ofFn]
    · intro j hj hk
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Function.comp_apply]
  rw [h, List.sum_ofFn]

theorem sumWordProduct (n m : ℕ) (f : NumberWord × NumberWord → ℕ) :
    (((wordRange (tally n)).product (wordRange (tally m))).map f).sum =
      ∑ j : Fin n, ∑ k : Fin m, f (Carry.born j.val, Carry.born k.val) := by
  change ((((wordRange (tally n)).map (fun j => (wordRange (tally m)).map (Prod.mk j))).flatten).map f).sum = _
  rw [List.map_flatten, List.sum_flatten, List.map_map, List.map_map, sumWordRange]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Function.comp_apply, List.map_map]
    exact sumWordRange m (fun k => f (Carry.born j.val, k))

def fieldContext (x : MotifFields) : MotifContext := nearContext x.1

@[fun_prop] theorem fieldContext_poly : Poly fieldContext := by unfold fieldContext; fun_prop

def wordThick (p : MotifFields × WireWords) : Bool :=
  let q := fieldContext p.1
  let f := splitLane (q.2.1.1, p.2.2.2)
  let col := cacheRead (p.1.2, motifColourRequest (motifLevel q, p.2.1))
  maskBit (q.2.1, f.1, col)

@[fun_prop] theorem wordThick_poly : Poly wordThick := by unfold wordThick; dsimp only; fun_prop

def bitAnd (p : Bool × Bool) : Bool := p.1 && p.2

@[fun_prop] theorem bitAnd_poly : Poly bitAnd := (Easy.finite _).poly

def bitNand (p : Bool × Bool) : Bool := !(p.1 && p.2)

@[fun_prop] theorem bitNand_poly : Poly bitNand := (Easy.finite _).poly

def wordMotif (p : MotifFields × WireWords) : Bool :=
  bitNand (wordThick p, wordThick (p.1, nearHop true (p.1.1, p.2)))

@[fun_prop] theorem wordMotif_poly : Poly wordMotif := by unfold wordMotif; fun_prop

def wordThin (p : MotifFields × WireWords) : WireWords :=
  bif wordThick p then nearHop true (p.1.1, p.2) else p.2

@[fun_prop] theorem wordThin_poly : Poly wordThin := by unfold wordThin; fun_prop

def wordWidth (p : MotifFields × WireWords) : NumberWord :=
  cacheRead (p.1.2, nearWidthRequest (p.1.1, p.2))

@[fun_prop] theorem wordWidth_poly : Poly wordWidth := by unfold wordWidth; fun_prop

abbrev RankInput := (MotifFields × WireWords × NumberWord) × NumberWord × NumberWord
abbrev RankWires := MotifFields × WireRadices × NumberWord × WireWords × WireWords

def rankWires (p : RankInput) : RankWires :=
  let rad := (fieldContext p.1.1).2.1.1
  let z := rankWireWords (rad, p.1.2.1, p.2)
  (p.1.1, rad, p.1.2.2, z, nearHop false (p.1.1.1, z))

@[fun_prop] theorem rankWires_poly : Poly rankWires := by unfold rankWires; dsimp only; fun_prop

def rankFlags (p : RankWires) : Bool × Bool × Bool × Bool :=
  let z := p.2.2.2.1
  let v := p.2.2.2.2
  let smaller := fun x => Carry.lt_ (wireRankKey (p.2.1, x), p.2.2.1)
  (!wordThick (p.1, z), smaller z, wordThick (p.1, v), smaller v)

@[fun_prop] theorem rankFlags_poly : Poly rankFlags := by unfold rankFlags; dsimp only; fun_prop

def flagsCount (p : Bool × Bool × Bool × Bool) : NumberWord :=
  Bits.add ((bif p.1 && p.2.1 then [true] else []),
    (bif p.1 && p.2.2.1 && p.2.2.2 then [true] else []))

def wordRankAt (p : RankInput) : NumberWord := flagsCount (rankFlags (rankWires p))

@[fun_prop] theorem wordRankAt_poly : Poly wordRankAt :=
  (rankWires_poly.compose rankFlags_poly).compose (Easy.finite flagsCount).poly

def emptyMotifFields : MotifFields := (((emptyMotifContext, []), []), [])

def emptyWireWords : WireWords := ([], [], [])

def wordRank (p : MotifFields × WireWords × WireWords) : NumberWord :=
  let q := fieldContext p.1
  let κ := wireRankKey (q.2.1.1, p.2.2)
  sumWords (Code.polyPush wordRankAt ((p.1, p.2.1, κ), (motifSlots q).product (motifMasks q)))

@[fun_prop] theorem wordRank_poly : Poly wordRank := by
  have hp := Poly.push (emptyMotifFields, emptyWireWords, ([] : NumberWord))
    (([], []) : NumberWord × NumberWord) wordRankAt_poly
  have hprod := product_poly ([] : NumberWord) ([] : NumberWord)
  unfold wordRank
  dsimp only
  fun_prop

def wordTotalAt (p : (MotifFields × WireWords) × NumberWord × NumberWord) : NumberWord :=
  let z := bundleAB (p.1.1.1, p.1.2, p.2)
  let v := nearHop true (p.1.1.1, z)
  bif bitAnd (wordThick (p.1.1, z), wordThick (p.1.1, v)) then wordWidth (p.1.1, z) else []

set_option maxHeartbeats 950000 in
@[fun_prop] theorem wordTotalAt_poly : Poly wordTotalAt := by unfold wordTotalAt; dsimp only; fun_prop

def wordTotal (p : MotifFields × WireWords) : NumberWord :=
  let q := fieldContext p.1
  sumWords (Code.polyPush wordTotalAt (p, (motifMasks q).product (motifSlots q)))

@[fun_prop] theorem wordTotal_poly : Poly wordTotal := by
  have hp := Poly.push (emptyMotifFields, emptyWireWords) (([], []) : NumberWord × NumberWord) wordTotalAt_poly
  have hprod := product_poly ([] : NumberWord) ([] : NumberWord)
  unfold wordTotal
  dsimp only
  fun_prop

def wordDemand (p : MotifFields × WireWords) : NumberWord × NumberWord :=
  let t := wordThin p
  let q := fieldContext p.1
  let qr := Carry.nat_div (wordTotal (p.1, t), q.2.1.2.2.2.2.2.1)
  let r := wordRank (p.1, t, p.2)
  ((bif Carry.lt_ (r, qr.2) then Bits.add (qr.1, [true]) else qr.1), wordWidth p)

@[fun_prop] theorem wordDemand_poly : Poly wordDemand := by unfold wordDemand; dsimp only; fun_prop

end P1SolGreedy.SolDemand
