import P1SolGreedy.MotifCandidates

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev MotifFields := MotifNear × FieldCache

def nearContext (s : MotifNear) : MotifContext := s.1.1

@[fun_prop] theorem nearContext_poly : Poly nearContext := by unfold nearContext; fun_prop

def nearHop (b : Bool) (p : MotifNear × WireWords) : WireWords :=
  hop b (nearContext p.1, p.1.2, p.2)

@[fun_prop] theorem nearHop_poly (b : Bool) : Poly (nearHop b) := by unfold nearHop; fun_prop

def nearOffset (p : MotifNear × NumberWord) : NumberWord :=
  cacheRead (p.1.2, offsetAt (motifLevel (nearContext p.1), p.2))

@[fun_prop] theorem nearOffset_poly : Poly nearOffset := by unfold nearOffset; fun_prop

def nearWidthRequest (p : MotifNear × WireWords) : P1Batch.Req :=
  let q := nearContext p.1
  widthRequest (motifLevel q, (motifLayout q).1, p.2)

@[fun_prop] theorem nearWidthRequest_poly : Poly nearWidthRequest := by unfold nearWidthRequest; dsimp only; fun_prop

def leafColourAt (p : MotifNear × NumberWord) : List P1Batch.Req :=
  let q := nearContext p.1
  let ask := fun Y => motifColourRequest (motifLevel q, Y)
  (p.2 :: addrWords (q, p.1.2, p.2)).map ask

@[fun_prop] theorem leafColourAt_poly : Poly leafColourAt := by
  let ask (p : BaseRow × NumberWord) := motifColourRequest p
  have h := Poly.push defaultRow ([] : NumberWord) motifColourRequest_poly
  unfold leafColourAt
  change Poly (fun p : MotifNear × NumberWord =>
    Code.polyPush ask (motifLevel (nearContext p.1), p.2 :: addrWords (nearContext p.1, p.1.2, p.2)))
  exact (by fun_prop : Poly (fun p : MotifNear × NumberWord =>
    (motifLevel (nearContext p.1), p.2 :: addrWords (nearContext p.1, p.1.2, p.2)))).compose h

def leafColours (s : MotifNear) : List P1Batch.Req :=
  (Code.polyPush leafColourAt (s, s.1.2)).flatten

@[fun_prop] theorem leafColours_poly : Poly leafColours := by
  have h := Poly.push (((emptyMotifContext, []), []) : MotifNear) ([] : NumberWord) leafColourAt_poly
  have hf : Poly (fun xs : List (List P1Batch.Req) => xs.flatten) := Easy.flatten.poly
  unfold leafColours
  fun_prop

def bundleAB (p : MotifNear × WireWords × NumberWord × NumberWord) : WireWords :=
  let q := nearContext p.1
  totalWireWords (q.2.1.1, p.2.1, nearOffset (p.1, p.2.1.1), p.2.2.1, p.2.2.2)

@[fun_prop] theorem bundleAB_poly : Poly bundleAB := by unfold bundleAB; dsimp only; fun_prop

theorem bundleAB_base (p : MotifNear × WireWords × NumberWord × NumberWord) :
    (bundleAB p).1 = p.2.1.1 := rfl

def bundleCostsAt (p : MotifNear × WireWords) : List P1Batch.Req :=
  let q := nearContext p.1
  let f := fun z : (MotifNear × WireWords) × (NumberWord × NumberWord) =>
    nearWidthRequest (z.1.1, bundleAB (z.1.1, z.1.2, z.2))
  Code.polyPush f (p, (motifMasks q).product (motifSlots q))

@[fun_prop] theorem bundleCostsAt_poly : Poly bundleCostsAt := by
  let f := fun z : (MotifNear × WireWords) × (NumberWord × NumberWord) =>
    nearWidthRequest (z.1.1, bundleAB (z.1.1, z.1.2, z.2))
  have hf : Poly f := by unfold f; fun_prop
  have hm := Poly.push (((emptyMotifContext, []), []), ([], [], [])) (([], []) : NumberWord × NumberWord) hf
  have hprod := product_poly ([] : NumberWord) ([] : NumberWord)
  unfold bundleCostsAt
  dsimp only
  fun_prop

def leafWidthsAt (p : MotifNear × WireWords) : List P1Batch.Req :=
  nearWidthRequest p :: (bundleCostsAt p ++ bundleCostsAt (p.1, nearHop true p))

@[fun_prop] theorem leafWidthsAt_poly : Poly leafWidthsAt := by unfold leafWidthsAt; fun_prop

def leafTermAt (p : (MotifNear × WireWords) × NumberWord) : P1Batch.Req :=
  let q := nearContext p.1.1
  let key := arcWordKey (q.2.1.1, p.1.2)
  termRequest (motifLevel q, motifLayout q, p.1.2.1, key, p.2)

@[fun_prop] theorem leafTermAt_poly : Poly leafTermAt := by unfold leafTermAt; dsimp only; fun_prop

def leafTermsAt (p : MotifNear × WireWords) : List P1Batch.Req :=
  Code.polyPush leafTermAt (p, wordRange (tally 9))

@[fun_prop] theorem leafTermsAt_poly : Poly leafTermsAt := by
  exact (by fun_prop : Poly (fun p : MotifNear × WireWords => (p, wordRange (tally 9)))).compose
    (Poly.push (((emptyMotifContext, []), []), ([], [], [])) ([] : NumberWord) leafTermAt_poly)

def leafWireFields (p : MotifNear × WireWords) : List P1Batch.Req :=
  leafWidthsAt p ++ leafTermsAt p

@[fun_prop] theorem leafWireFields_poly : Poly leafWireFields := by
  unfold leafWireFields
  fun_prop

def leafWires (all : Bool) (s : MotifNear) : List P1Batch.Req :=
  (Code.polyPush leafWireFields (s, arcRoots all (nearContext s))).flatten

@[fun_prop] theorem leafWires_poly (all : Bool) : Poly (leafWires all) := by
  have hp := Poly.push (((emptyMotifContext, []), []) : MotifNear) (([], [], []) : WireWords) leafWireFields_poly
  have hf : Poly (fun xs : List (List P1Batch.Req) => xs.flatten) := Easy.flatten.poly
  unfold leafWires
  fun_prop

def prevAddress (Y : NumberWord) : NumberWord := Carry.sub0 (Y, [true])

@[fun_prop] theorem prevAddress_poly : Poly prevAddress := by unfold prevAddress; fun_prop

theorem prevAddress_value (Y : NumberWord) : P1Batch.bval (prevAddress Y) = P1Batch.bval Y - 1 := by
  rw [prevAddress, ← value_bval, Carry.sub0_v, value_bval]
  rfl

def leafEnergies (q : MotifContext) : List P1Batch.Req :=
  let Y := motifRoot q
  let R := motifLevel q
  [energyRequest (R, Y, []), energyRequest (R, Y, [true]),
    energyRequest (R, prevAddress Y, []), energyRequest (R, prevAddress Y, [true])]

@[fun_prop] theorem leafEnergies_poly : Poly leafEnergies := by unfold leafEnergies; dsimp only; fun_prop

def motThirdRaw (all : Bool) (s : MotifNear) : List P1Batch.Req :=
  let q := nearContext s
  bif q.1.2.1 then
    leafColours s ++ leafWires all s ++ (if all then leafEnergies q else [])
  else []

@[fun_prop] theorem motThirdRaw_poly (all : Bool) : Poly (motThirdRaw all) := by
  cases all <;> unfold motThirdRaw <;> dsimp only <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

def motThird (all : Bool) (s : MotifNear) : List P1Batch.Req :=
  clipRequests ((nearContext s).1.1, motThirdRaw all s)

theorem motThird_poly (all : Bool) : Poly (motThird all) := by unfold motThird; fun_prop

def motThirdNext (all : Bool) (p : MotifNear × List NumberWord) : MotifFields :=
  (p.1, cacheFields (motThirdRaw all p.1, p.2))

theorem motThirdNext_poly (all : Bool) : Poly (motThirdNext all) := by unfold motThirdNext; fun_prop

def savedMotifFields (all : Bool) (s : MotifNear) (u : List Bool) : MotifFields :=
  (s, (motThirdRaw all s).map (fun r => (r, P1Batch.fetch u r)))

theorem motThirdNext_reads (all : Bool) (s : MotifNear) (u : List Bool)
    (hlen : P1Batch.bval (nearContext s).1.1 = u.length) :
    motThirdNext all (s, (motThird all s).map (P1Batch.fetch u)) = savedMotifFields all s u := by
  unfold motThirdNext motThird savedMotifFields
  dsimp only
  rw [cacheFields_fetch _ _ hlen]

theorem leafColours_mem (s : MotifNear) {Y Z : NumberWord} (hY : Y ∈ s.1.2)
    (hZ : Z ∈ Y :: addrWords (nearContext s, s.2, Y)) :
    motifColourRequest (motifLevel (nearContext s), Z) ∈ leafColours s := by
  unfold leafColours Code.polyPush
  exact List.mem_flatten.mpr ⟨leafColourAt (s, Y), List.mem_map_of_mem hY, List.mem_map_of_mem hZ⟩

theorem leafWires_mem (all : Bool) (s : MotifNear) {w : WireWords}
    (hw : w ∈ arcRoots all (nearContext s)) {r : P1Batch.Req} (hr : r ∈ leafWireFields (s, w)) :
    r ∈ leafWires all s := by
  unfold leafWires Code.polyPush
  exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hw, hr⟩

theorem bundleCostsAt_mem (s : MotifNear) (w : WireWords) {m j : NumberWord}
    (hm : m ∈ motifMasks (nearContext s)) (hj : j ∈ motifSlots (nearContext s)) :
    nearWidthRequest (s, bundleAB (s, w, m, j)) ∈ bundleCostsAt (s, w) := by
  unfold bundleCostsAt Code.polyPush
  exact List.mem_map_of_mem (List.mem_product.mpr ⟨hm, hj⟩)

theorem leafTermsAt_mem (s : MotifNear) (w : WireWords) {c : NumberWord}
    (hc : c ∈ wordRange (tally 9)) : leafTermAt ((s, w), c) ∈ leafTermsAt (s, w) := by
  unfold leafTermsAt Code.polyPush
  exact List.mem_map_of_mem hc

end P1SolGreedy.SolDemand
