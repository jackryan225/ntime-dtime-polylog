import P1SolGreedy.MotifFields

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev MotifBases := MotifContext × List NumberWord
abbrev MotifNear := MotifBases × FieldCache

def emptyMotifContext : MotifContext := (([], false, [], defaultRow), emptyMotifRow, [])

def motifRoot (q : MotifContext) : NumberWord := q.1.2.2.1
def motifLevel (q : MotifContext) : BaseRow := q.1.2.2.2
def motifLayout (q : MotifContext) : MotifStride := q.2.1.2.2.2.2.2.2.2
def motifSlots (q : MotifContext) : List NumberWord := wordRange q.2.1.2.2.1
def motifMasks (q : MotifContext) : List NumberWord := wordRange q.2.1.2.2.2.1

@[fun_prop] theorem motifRoot_poly : Poly motifRoot := by unfold motifRoot; fun_prop
@[fun_prop] theorem motifLevel_poly : Poly motifLevel := by unfold motifLevel; fun_prop
@[fun_prop] theorem motifLayout_poly : Poly motifLayout := by unfold motifLayout; fun_prop
@[fun_prop] theorem motifSlots_poly : Poly motifSlots := by unfold motifSlots; fun_prop
@[fun_prop] theorem motifMasks_poly : Poly motifMasks := by unfold motifMasks; fun_prop

def addrRaw (p : MotifContext × NumberWord) : List P1Batch.Req :=
  let r := motifLevel p.1
  let k := motifSlots p.1
  slotsAt .outAddr (r, p.2, k) ++ slotsAt .inAddr (r, p.2, k)

@[fun_prop] theorem addrRaw_poly : Poly addrRaw := by unfold addrRaw; dsimp only; fun_prop

def motFirstRaw (q : MotifContext) : List P1Batch.Req :=
  bif q.1.2.1 then addrRaw (q, motifRoot q) else []

@[fun_prop] theorem motFirstRaw_poly : Poly motFirstRaw := by unfold motFirstRaw; fun_prop

def motFirst (q : MotifContext) : List P1Batch.Req := clipRequests (q.1.1, motFirstRaw q)

theorem motFirst_poly : Poly motFirst := by unfold motFirst; fun_prop

def addrWords (p : MotifContext × FieldCache × NumberWord) : List NumberWord :=
  Code.polyPush cacheRead (p.2.1, addrRaw (p.1, p.2.2))

@[fun_prop] theorem addrWords_poly : Poly addrWords := by
  have h := Poly.push ([] : FieldCache) (([], []) : P1Batch.Req) cacheRead_poly
  unfold addrWords
  fun_prop

def motFirstNext (p : MotifContext × List NumberWord) : MotifBases :=
  let cache := cacheFields (motFirstRaw p.1, p.2)
  let Y := motifRoot p.1
  (p.1, bif p.1.1.2.1 then Y :: addrWords (p.1, cache, Y) else [])

theorem motFirstNext_poly : Poly motFirstNext := by unfold motFirstNext; dsimp only; fun_prop

def neighborPanelRaw (p : MotifContext × NumberWord) : List P1Batch.Req :=
  let r := motifLevel p.1
  let k := motifSlots p.1
  offsetAt (r, p.2) :: (addrRaw p ++ slotsAt .outFar (r, p.2, k) ++ slotsAt .inFar (r, p.2, k) ++
    slotsAt .outDisp (r, p.2, k) ++ slotsAt .inDisp (r, p.2, k))

@[fun_prop] theorem neighborPanelRaw_poly : Poly neighborPanelRaw := by
  unfold neighborPanelRaw
  dsimp only
  fun_prop

def motSecondRaw (p : MotifBases) : List P1Batch.Req :=
  (Code.polyPush neighborPanelRaw p).flatten

@[fun_prop] theorem motSecondRaw_poly : Poly motSecondRaw :=
  (Poly.push emptyMotifContext ([] : NumberWord) neighborPanelRaw_poly).compose Easy.flatten.poly

def motSecond (p : MotifBases) : List P1Batch.Req :=
  clipRequests (p.1.1.1, motSecondRaw p)

theorem motSecond_poly : Poly motSecond := by unfold motSecond; fun_prop

def motSecondNext (p : MotifBases × List NumberWord) : MotifNear :=
  (p.1, cacheFields (motSecondRaw p.1, p.2))

theorem motSecondNext_poly : Poly motSecondNext := by unfold motSecondNext; fun_prop

def savedMotifBases (q : MotifContext) (u : List Bool) : MotifBases :=
  let Y := motifRoot q
  let requests := motFirstRaw q
  (q, bif q.1.2.1 then
    Y :: addrWords (q, requests.map (fun r => (r, P1Batch.fetch u r)), Y)
  else [])

def savedMotifNear (p : MotifBases) (u : List Bool) : MotifNear :=
  (p, (motSecondRaw p).map (fun r => (r, P1Batch.fetch u r)))

theorem motFirstNext_reads (q : MotifContext) (u : List Bool) (hl : P1Batch.bval q.1.1 = u.length) :
    motFirstNext (q, (motFirst q).map (P1Batch.fetch u)) = savedMotifBases q u := by
  unfold motFirstNext motFirst savedMotifBases
  dsimp only
  rw [cacheFields_fetch _ _ hl]

theorem motSecondNext_reads (p : MotifBases) (u : List Bool) (hl : P1Batch.bval p.1.1.1 = u.length) :
    motSecondNext (p, (motSecond p).map (P1Batch.fetch u)) = savedMotifNear p u := by
  unfold motSecondNext motSecond savedMotifNear
  dsimp only
  rw [cacheFields_fetch _ _ hl]

def hop (out : Bool) (p : MotifContext × FieldCache × WireWords) : WireWords :=
  let r := motifLevel p.1
  let addr := bif out then slotAt .outAddr (r, p.2.2.1, p.2.2.2.1)
    else slotAt .inAddr (r, p.2.2.1, p.2.2.2.1)
  let far := bif out then slotAt .outFar (r, p.2.2.1, p.2.2.2.1)
    else slotAt .inFar (r, p.2.2.1, p.2.2.2.1)
  let disp := bif out then slotAt .outDisp (r, p.2.2.1, p.2.2.2.1)
    else slotAt .inDisp (r, p.2.2.1, p.2.2.2.1)
  shiftedWire (p.1.2.1.1, p.2.2, cacheRead (p.2.1, addr), cacheRead (p.2.1, far), cacheRead (p.2.1, disp))

@[fun_prop] theorem hop_poly (out : Bool) : Poly (hop out) := by
  unfold hop
  dsimp only
  fun_prop

theorem addrRaw_out (q : MotifContext) (y k : NumberWord) (hk : k ∈ motifSlots q) :
    slotAt .outAddr (motifLevel q, y, k) ∈ addrRaw (q, y) := by
  unfold addrRaw
  dsimp only
  rw [slotsAt_eq, slotsAt_eq]
  exact List.mem_append_left _ (List.mem_map_of_mem hk)

theorem addrRaw_in (q : MotifContext) (y k : NumberWord) (hk : k ∈ motifSlots q) :
    slotAt .inAddr (motifLevel q, y, k) ∈ addrRaw (q, y) := by
  unfold addrRaw
  dsimp only
  rw [slotsAt_eq, slotsAt_eq]
  exact List.mem_append_right _ (List.mem_map_of_mem hk)

theorem addrWords_hop_mem (q : MotifContext) (c : FieldCache) (z : WireWords) (out : Bool)
    (hk : z.2.1 ∈ motifSlots q) : (hop out (q, c, z)).1 ∈ addrWords (q, c, z.1) := by
  unfold addrWords Code.polyPush
  cases out
  · exact List.mem_map_of_mem (addrRaw_in q z.1 z.2.1 hk)
  · exact List.mem_map_of_mem (addrRaw_out q z.1 z.2.1 hk)

theorem motSecondRaw_mem (p : MotifBases) {Z : NumberWord} (hz : Z ∈ p.2)
    {r : P1Batch.Req} (hr : r ∈ neighborPanelRaw (p.1, Z)) : r ∈ motSecondRaw p := by
  simp only [motSecondRaw, Code.polyPush, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨Z, hz, rfl⟩, hr⟩

theorem motSecondRaw_offset (p : MotifBases) (Z : NumberWord) (hz : Z ∈ p.2) :
    offsetAt (motifLevel p.1, Z) ∈ motSecondRaw p :=
  motSecondRaw_mem p hz List.mem_cons_self

theorem motSecondRaw_slot (p : MotifBases) (Z k : NumberWord) (hz : Z ∈ p.2) (hk : k ∈ motifSlots p.1) :
    ∀ c ∈ [Mem.outAddr, .inAddr, .outFar, .inFar, .outDisp, .inDisp],
      slotAt c (motifLevel p.1, Z, k) ∈ motSecondRaw p := by
  intro c hc
  apply motSecondRaw_mem p hz
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [List.mem_append]
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (Or.inl (addrRaw_out _ _ _ hk))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (addrRaw_in _ _ _ hk))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [slotsAt_eq]; exact List.mem_map_of_mem hk))))
  · exact Or.inl (Or.inl (Or.inr (by rw [slotsAt_eq]; exact List.mem_map_of_mem hk)))
  · exact Or.inl (Or.inr (by rw [slotsAt_eq]; exact List.mem_map_of_mem hk))
  · exact Or.inr (by rw [slotsAt_eq]; exact List.mem_map_of_mem hk)

theorem addrWords_hop_mem_value (all : Bool) (D : Dims) (ℓ a g : ℕ) (len Y key : NumberWord)
    (c : FieldCache) (w : WireWords) (out : Bool) (hk : P1Batch.bval w.2.1 < 2 ^ a) :
    let q := activeMotif all D ℓ a g len Y key
    (hop out (q, c, w)).1 ∈ addrWords (q, c, w.1) := by
  let q := activeMotif all D ℓ a g len Y key
  let j := Carry.born (P1Batch.bval w.2.1)
  let v : WireWords := (w.1, j, w.2.2)
  have hm : j ∈ motifSlots q := born_mem_wordRange hk
  have hnum (mem : Mem) : requestNumbers (slotAt mem (motifLevel q, w.1, w.2.1)) =
      requestNumbers (slotAt mem (motifLevel q, w.1, j)) := by
    change requestNumbers (slotAt mem (levelRow D ℓ, w.1, w.2.1)) =
      requestNumbers (slotAt mem (levelRow D ℓ, w.1, j))
    rw [requestNumbers_slotAt, requestNumbers_slotAt, show P1Batch.bval j = _ from bval_born _]
  have hopEq : (hop out (q, c, w)).1 = (hop out (q, c, v)).1 := by
    cases out
    · exact cacheRead_congr _ _ _ (hnum .inAddr)
    · exact cacheRead_congr _ _ _ (hnum .outAddr)
  change (hop out (q, c, w)).1 ∈ addrWords (q, c, w.1)
  rw [hopEq]
  exact addrWords_hop_mem q c v out hm

end P1SolGreedy.SolDemand
