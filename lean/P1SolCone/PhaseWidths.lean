import P1SolCone.PhaseWalk

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def phaseWidthKey (h : PhaseHeader) (y lane slot : ℕ) : FieldKey :=
  let f := h.2.2.2.2
  phaseFieldKey false .width h ((y * packetNat f 5 + lane) * packetNat f 4 + slot)

@[fun_prop] theorem phaseWidthKey_poly :
    Poly (fun p : PhaseHeader × ℕ × ℕ × ℕ => phaseWidthKey p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold phaseWidthKey
  exact (show Poly (fun p : PhaseHeader × ℕ × ℕ × ℕ =>
    (p.1, (p.2.1 * packetNat p.1.2.2.2.2 5 + p.2.2.1) * packetNat p.1.2.2.2.2 4 + p.2.2.2)) from
    by fun_prop).compose (phaseFieldKey_poly false .width)

theorem phaseWidthKey_read (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally)
    (z lane slot : ℕ) (hw : D.width (secLev l .width) ≤ clock.length) :
    phaseFieldAt u (phaseWidthKey (actualPhaseHeader D u l y clock) z lane slot) = rdWidth D u l z lane slot := by
  have h4 : packetNat (phaseFormat D l) 4 = (D.lv l).slots := by rw [packetNat_phaseFormat]; rfl
  have h5 : packetNat (phaseFormat D l) 5 = (D.lv l).lanes := by rw [packetNat_phaseFormat]; rfl
  unfold phaseWidthKey rdWidth
  rw [read_phaseFieldKey D u l y clock false .width _ hw]
  dsimp only [actualPhaseHeader]
  rw [h4,h5]
  rfl

def outWidthKey (h : PhaseHeader) (p : PositionCode) (j : ℕ) : FieldKey :=
  phaseWidthKey h p.1 p.2 j

def inWidthKey (h : PhaseHeader) (cache : FieldCache) (p : PositionCode) (j : ℕ) : FieldKey :=
  phaseWidthKey h (rawIncidence h cache .inAddr p.1 j)
    (p.2 ^^^ rawIncidence h cache .inDisp p.1 j) (rawIncidence h cache .inFar p.1 j)

theorem outWidthKey_poly :
    Poly (fun p : PhaseHeader × PositionCode × ℕ => outWidthKey p.1 p.2.1 p.2.2) := by
  exact (show Poly (fun p : PhaseHeader × PositionCode × ℕ => (p.1,p.2.1.1,p.2.1.2,p.2.2))
    from by fun_prop).compose phaseWidthKey_poly

theorem inWidthKey_poly :
    Poly (fun p : PhaseHeader × FieldCache × PositionCode × ℕ => inWidthKey p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := PhaseHeader × FieldCache × PositionCode × ℕ
  have h : Poly (fun p : A => ((p.1,p.2.1),p.2.2.1.1,p.2.2.2)) := by unfold A; fun_prop
  have lane : Poly (fun p : A => p.2.2.1.2) := by unfold A; fun_prop
  exact (Easy.fst.poly.pair ((h.compose (rawIncidence_poly .inAddr)).pair
    ((poly_xorNat lane (h.compose (rawIncidence_poly .inDisp))).pair (h.compose (rawIncidence_poly .inFar))))).compose
    phaseWidthKey_poly

def phaseHalfWidthKeys (h : PhaseHeader) (c : FieldCache) (p : PositionCode) :
    List FieldKey × List FieldKey :=
  ((rawSlots h).map (outWidthKey h p), (rawSlots h).map (inWidthKey h c p))

theorem phaseHalfWidthKeys_poly :
    Poly (fun p : PhaseHeader × FieldCache × PositionCode => phaseHalfWidthKeys p.1 p.2.1 p.2.2) := by
  unfold phaseHalfWidthKeys
  let A := PhaseHeader × FieldCache × PositionCode
  have slots := (Easy.fst.poly : Poly (Prod.fst : A → PhaseHeader)).compose rawSlots_poly
  have out : Poly (fun q : A × ℕ => (q.1.1,q.1.2.2,q.2)) := by unfold A; fun_prop
  have inn : Poly (fun q : A × ℕ => (q.1.1,q.1.2.1,q.1.2.2,q.2)) := by unfold A; fun_prop
  exact (poly_mapParameter slots (out.compose outWidthKey_poly)).pair (poly_mapParameter slots (inn.compose inWidthKey_poly))

def rawHalfWidths (h : PhaseHeader) (inc widths : FieldCache) (p : PositionCode) :
    List ℕ × List ℕ :=
  let keys := phaseHalfWidthKeys h inc p
  (keys.1.map widths.read, keys.2.map widths.read)

theorem rawHalfWidths_poly :
    Poly (fun p : PhaseHeader × FieldCache × FieldCache × PositionCode => rawHalfWidths p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rawHalfWidths
  let A := PhaseHeader × FieldCache × FieldCache × PositionCode
  have keys := (show Poly (fun p : A => (p.1,p.2.1,p.2.2.2)) from by unfold A; fun_prop).compose phaseHalfWidthKeys_poly
  have k : Poly (fun p : A × FieldKey => (p.1.2.2.1,p.2)) := by unfold A; fun_prop
  exact (poly_mapParameter keys.fstCompose (k.compose fieldCache_read_poly)).pair
    (poly_mapParameter keys.sndCompose (k.compose fieldCache_read_poly))

theorem rawHalfWidths_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (p : PositionCode) (hp : p.1 ∈ ys)
    (hc : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length)
    (widthCache : FieldCache)
    (he : let h := actualPhaseHeader D u l y clock
      let keys := phaseHalfWidthKeys h (rawRoundCache extra u h ys) p
      ∀ k ∈ keys.1 ++ keys.2, widthCache.read k = phaseFieldAt u k) :
    let h := actualPhaseHeader D u l y clock
    rawHalfWidths h (rawRoundCache extra u h ys) widthCache p = readHalfWidths D u l p := by
  let h := actualPhaseHeader D u l y clock
  let cache := rawRoundCache extra u h ys
  let keys := phaseHalfWidthKeys h cache p
  have rng : rawSlots h = List.range (D.lv l).slots := rawSlots_eq D u l y clock hc
  change (keys.1.map widthCache.read, keys.2.map widthCache.read) = readHalfWidths D u l p
  apply Prod.ext
  · simp only [keys, phaseHalfWidthKeys, List.map_map, rng, readHalfWidths]
    apply List.map_congr_left
    intro j hj
    have hk : outWidthKey h p j ∈ keys.1 := by
      change outWidthKey h p j ∈ (rawSlots h).map (outWidthKey h p)
      rw [rng]
      exact List.mem_map_of_mem hj
    change widthCache.read (outWidthKey h p j) = _
    rw [he _ (List.mem_append_left _ hk)]
    exact phaseWidthKey_read D u l y clock p.1 p.2 j (hw _)
  · simp only [keys, phaseHalfWidthKeys, List.map_map, rng, readHalfWidths]
    apply List.map_congr_left
    intro j hj
    have hk : inWidthKey h cache p j ∈ keys.2 := by
      change inWidthKey h cache p j ∈ (rawSlots h).map (inWidthKey h cache p)
      rw [rng]
      exact List.mem_map_of_mem hj
    change widthCache.read (inWidthKey h cache p j) = _
    rw [he _ (List.mem_append_right _ hk)]
    unfold inWidthKey
    rw [phaseWidthKey_read D u l y clock _ _ _ (hw _)]
    have eq (m : Mem) (hm : m ∈ [Mem.outAddr,.outDisp,.outFar,.inAddr,.inDisp,.inFar]) :=
      rawRoundCache_incidence extra D u l y clock ys p.1 j hp hc (List.mem_range.mp hj) m hm (hw _)
    rw [eq .inAddr (by simp), eq .inDisp (by simp), eq .inFar (by simp)]
    rfl

/-- All half-width fields used by the next frontier, including malformed source indices. -/
def phaseWidthRequests (h : PhaseHeader) (inc : FieldCache) (positions : List PositionCode) : List FieldKey :=
  positions.flatMap fun p =>
    let (o,i) := phaseHalfWidthKeys h inc p
    o ++ i

theorem phaseWidthRequests_poly :
    Poly (fun p : PhaseHeader × FieldCache × List PositionCode => phaseWidthRequests p.1 p.2.1 p.2.2) := by
  let A := PhaseHeader × FieldCache × List PositionCode
  have sites : Poly (fun p : A => p.2.2) := by unfold A; fun_prop
  have part : Poly (fun q : A × PositionCode => (q.1.1,q.1.2.1,q.2)) := by unfold A; fun_prop
  exact (poly_mapParameter sites ((part.compose phaseHalfWidthKeys_poly).compose Easy.append.poly)).compose
    Easy.flatten.poly

theorem phaseWidthRequests_bounds {h : PhaseHeader} {inc : FieldCache} {positions : List PositionCode}
    {k : FieldKey} (hk : k ∈ phaseWidthRequests h inc positions) :
    k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length := by
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hk
  rcases List.mem_append.mp hp with ho | hi
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp ho
    exact phaseFieldKey_bounds false .width _ _
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact phaseFieldKey_bounds false .width _ _

theorem phaseWidthRequests_read (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (positions : List PositionCode) (p : PositionCode)
    (hp : p ∈ positions) (hy : p.1 ∈ ys) (hc : (D.lv l).slots ≤ clock.length)
    (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    let inc := rawRoundCache extra u h ys
    let wc := fetchPhaseFields u (phaseWidthRequests h inc positions)
    rawHalfWidths h inc wc p = readHalfWidths D u l p := by
  dsimp only
  apply rawHalfWidths_eq extra D u l y clock ys p hy hc hw
  dsimp only
  intro k hk
  exact fetchPhaseFields_read _ _ _ (List.mem_flatMap.mpr ⟨p,hp,hk⟩)

end P1SolCone.SolCone
