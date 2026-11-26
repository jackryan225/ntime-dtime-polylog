import P1SolGreedy.C6Format
import P1SolGreedy.SlotCache

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev PortWord := Bool × NumberWord
abbrev TagState := TagContext × FieldCache
abbrev TagFields := TagContext × FieldCache × FieldCache

def emptyTagContext : TagContext := (([], false, [], defaultRow), defaultTagRow)

def activeTag (D : Dims) (ℓ a g : ℕ) (len y : NumberWord) : TagContext :=
  ((len, true, y, levelRow D ℓ), tagRow a g)

def tagPorts (t : TagRow) : List PortWord :=
  [false, true].product (wordRange t.2.1)

@[fun_prop] theorem tagPorts_poly : Poly tagPorts := by
  have h := product_poly false ([] : NumberWord)
  unfold tagPorts
  fun_prop

def offsetAt (p : BaseRow × NumberWord) : P1Batch.Req :=
  fieldWords (rowSection .offset p.1, p.2)

@[fun_prop] theorem offsetAt_poly : Poly offsetAt := by unfold offsetAt; fun_prop

def tagRootRaw (q : TagContext) : List P1Batch.Req :=
  let y := q.1.2.2.1
  let r := q.1.2.2.2
  let ks := wordRange q.2.2.1
  bif q.1.2.1 then
    offsetAt (r, y) :: (slotsAt .outAddr (r, y, ks) ++ slotsAt .inAddr (r, y, ks) ++
      slotsAt .outDisp (r, y, ks) ++ slotsAt .inDisp (r, y, ks))
  else []

@[fun_prop] theorem tagRootRaw_poly : Poly tagRootRaw := by
  unfold tagRootRaw
  dsimp only
  fun_prop

def tagRoot (q : TagContext) : List P1Batch.Req := clipRequests (q.1.1, tagRootRaw q)

theorem tagRoot_poly : Poly tagRoot := by unfold tagRoot; fun_prop

def tagNext (p : TagContext × List NumberWord) : TagState :=
  (p.1, cacheFields (tagRootRaw p.1, p.2))

theorem tagNext_poly : Poly tagNext := by unfold tagNext; fun_prop

def neighborAt (p : TagState × PortWord) : NumberWord :=
  let y := p.1.1.1.2.2.1
  let r := p.1.1.1.2.2.2
  let k := p.2.2
  let req := bif p.2.1 then slotAt .outAddr (r, y, k) else slotAt .inAddr (r, y, k)
  cacheRead (p.1.2, req)

@[fun_prop] theorem neighborAt_poly : Poly neighborAt := by
  unfold neighborAt
  dsimp only
  fun_prop

def tagNeighbors (s : TagState) : List NumberWord :=
  Code.polyPush neighborAt (s, tagPorts s.1.2)

@[fun_prop] theorem tagNeighbors_poly : Poly tagNeighbors := by
  have h := Poly.push ((emptyTagContext, []) : TagState) (false, []) neighborAt_poly
  unfold tagNeighbors
  fun_prop

def neighborFields (p : TagContext × NumberWord) : List P1Batch.Req :=
  let r := p.1.1.2.2.2
  offsetAt (r, p.2) :: slotsAt .outDisp (r, p.2, wordRange p.1.2.2.1)

@[fun_prop] theorem neighborFields_poly : Poly neighborFields := by
  unfold neighborFields
  dsimp only
  fun_prop

def tagSecondRaw (s : TagState) : List P1Batch.Req :=
  bif s.1.1.2.1 then
    (Code.polyPush neighborFields (s.1, tagNeighbors s)).flatten
  else []

@[fun_prop] theorem tagSecondRaw_poly : Poly tagSecondRaw := by
  have h := Poly.push emptyTagContext ([] : NumberWord) neighborFields_poly
  unfold tagSecondRaw
  have hflat : Poly (fun l : List (List P1Batch.Req) => l.flatten) := Easy.flatten.poly
  fun_prop

def tagSecond (s : TagState) : List P1Batch.Req :=
  clipRequests (s.1.1.1, tagSecondRaw s)

theorem tagSecond_poly : Poly tagSecond := by unfold tagSecond; fun_prop

def tagFinish (p : TagState × List NumberWord) : TagFields :=
  (p.1.1, p.1.2, cacheFields (tagSecondRaw p.1, p.2))

theorem tagFinish_poly : Poly tagFinish := by unfold tagFinish; fun_prop

def tagRootSections : List Mem := [.outAddr, .inAddr, .outDisp, .inDisp]

theorem tagRootRaw_active (D : Dims) (ℓ a g : ℕ) (len y : NumberWord) :
    tagRootRaw (activeTag D ℓ a g len y) =
      offsetAt (levelRow D ℓ, y) :: tagRootSections.flatMap (fun c =>
        slotsAt c (levelRow D ℓ, y, wordRange (tally (2 ^ a)))) := by
  simp only [activeTag, tagRow, tagRootRaw, Bool.cond_true, tagRootSections, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

theorem tagRootSlot_mem (D : Dims) (ℓ a g : ℕ) (len y : NumberWord) {c : Mem}
    (hc : c ∈ tagRootSections) {q : P1Batch.Req}
    (hq : q ∈ slotsAt c (levelRow D ℓ, y, wordRange (tally (2 ^ a)))) :
    q ∈ tagRootRaw (activeTag D ℓ a g len y) := by
  rw [tagRootRaw_active]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, hq⟩)

theorem tagRootOffset_mem (D : Dims) (ℓ a g : ℕ) (len y : NumberWord) :
    offsetAt (levelRow D ℓ, y) ∈ tagRootRaw (activeTag D ℓ a g len y) := by
  rw [tagRootRaw_active]
  exact List.mem_cons_self

theorem tagSecondRaw_active (D : Dims) (ℓ a g : ℕ) (len y : NumberWord) (c : FieldCache) :
    tagSecondRaw (activeTag D ℓ a g len y, c) =
      (tagNeighbors (activeTag D ℓ a g len y, c)).flatMap (fun z =>
        offsetAt (levelRow D ℓ, z) :: slotsAt .outDisp (levelRow D ℓ, z, wordRange (tally (2 ^ a)))) := by
  simp only [tagSecondRaw, activeTag, Bool.cond_true, Code.polyPush, List.flatMap_def,
    neighborFields, tagRow]

theorem neighborAt_mem (s : TagState) (b : Bool) (k : NumberWord) (hk : k ∈ wordRange s.1.2.2.1) :
    neighborAt (s, b, k) ∈ tagNeighbors s := by
  unfold tagNeighbors Code.polyPush
  apply List.mem_map_of_mem
  unfold tagPorts
  exact List.mem_product.mpr ⟨by cases b <;> simp, hk⟩

theorem tagSecond_mem (D : Dims) (ℓ a g : ℕ) (len y : NumberWord)
    (c : FieldCache) {z : NumberWord}
    (hz : z ∈ tagNeighbors (activeTag D ℓ a g len y, c)) {r : P1Batch.Req}
    (hr : r ∈ offsetAt (levelRow D ℓ, z) :: slotsAt .outDisp (levelRow D ℓ, z, wordRange (tally (2 ^ a)))) :
    r ∈ tagSecondRaw (activeTag D ℓ a g len y, c) := by
  rw [tagSecondRaw_active]
  exact List.mem_flatMap.mpr ⟨z, hz, hr⟩

def extractedTag (p : TagRow × NumberWord) : NumberWord :=
  tagOfDispWords (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)

@[fun_prop] theorem extractedTag_poly : Poly extractedTag := by unfold extractedTag; fun_prop

theorem extractedTag_spec (a g : ℕ) (w : NumberWord) :
    P1Batch.bval (extractedTag (tagRow a g, w)) =
      (bitWordFinEquiv _ (tagOfDisp a g (P1Batch.bval w)) : ℕ) :=
  bval_tagOfDispWords a g w

end P1SolGreedy.SolDemand
