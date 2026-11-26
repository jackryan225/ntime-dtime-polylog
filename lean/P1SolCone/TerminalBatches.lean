import P1SolCone.TerminalReads
import P1SolCone.FieldPrograms
import P1SolCone.ConeFormat

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1ProgEng.SolKWR
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Enumeration clock, witness length, width cap, ordinal, final phase row and C11 format. -/
abbrev TerminalHeader := Tally × ℕ × ℕ × ℕ × List Bits.Word × List Bits.Word

def actualTerminalHeader (D : Dims) (m cap v : ℕ) (clock : Tally) : TerminalHeader :=
  (clock, m, cap, v, phaseFormat D D.top, fmt D)

def terminalBases (h : TerminalHeader) : ℕ := packetNat h.2.2.2.2.1 3
def terminalSlots (h : TerminalHeader) : ℕ := packetNat h.2.2.2.2.1 4
def terminalLanes (h : TerminalHeader) : ℕ := packetNat h.2.2.2.2.1 5
def terminalPos (h : TerminalHeader) : PositionCode :=
  (h.2.2.2.1 / terminalLanes h, h.2.2.2.1 % terminalLanes h)

@[fun_prop] theorem terminalBases_poly : Poly terminalBases := by unfold terminalBases; fun_prop
@[fun_prop] theorem terminalSlots_poly : Poly terminalSlots := by unfold terminalSlots; fun_prop
@[fun_prop] theorem terminalLanes_poly : Poly terminalLanes := by unfold terminalLanes; fun_prop
@[fun_prop] theorem terminalPos_poly : Poly terminalPos := by unfold terminalPos; fun_prop

@[simp] theorem terminalBases_actual (D : Dims) (m w v : ℕ) (clock : Tally) :
    terminalBases (actualTerminalHeader D m w v clock) = (D.lv D.top).bases := by
  unfold terminalBases actualTerminalHeader
  rw [packetNat_phaseFormat]
  rfl

@[simp] theorem terminalSlots_actual (D : Dims) (m w v : ℕ) (clock : Tally) :
    terminalSlots (actualTerminalHeader D m w v clock) = (D.lv D.top).slots := by
  unfold terminalSlots actualTerminalHeader
  rw [packetNat_phaseFormat]
  rfl

@[simp] theorem terminalLanes_actual (D : Dims) (m w v : ℕ) (clock : Tally) :
    terminalLanes (actualTerminalHeader D m w v clock) = (D.lv D.top).lanes := by
  unfold terminalLanes actualTerminalHeader
  rw [packetNat_phaseFormat]
  rfl

/-- A key uses one of the twelve row sections, or kind 12 for Ω. -/
def terminalPhysicalKey (D : Dims) (k : FieldKey) : FieldKey :=
  if k.1 = 12 then (D.secOmega, k.2) else (secLev D.top (Mem.ofCode k.1), k.2)

private def finalSection (h : TerminalHeader) (i : ℕ) : ℕ × ℕ :=
  bif decide (i = 12) then (packetNat h.2.2.2.2.2 4, packetNat h.2.2.2.2.2 5)
  else packetSection h.2.2.2.2.1 i

theorem finalSection_poly : Poly (fun p : TerminalHeader × ℕ => finalSection p.1 p.2) := by
  have h : Poly (fun p : TerminalHeader × ℕ => (p.1.2.2.2.2.1, p.2)) := by fun_prop
  have pref : Poly (fun p : TerminalHeader × ℕ =>
      (packetNat p.1.2.2.2.2.2 4, packetNat p.1.2.2.2.2.2 5)) := by fun_prop
  exact Poly.choose (poly_eqNat Easy.snd.poly (Code.Poly.const 12)) pref (h.compose packetSection_poly)

def terminalFieldReq (h : TerminalHeader) (k : FieldKey) : P1Batch.Req :=
  let (o, w) := finalSection h k.1
  clipConeRequest h.2.1 (numericFieldReq (o,w,k.2))

theorem terminalFieldReq_poly : Poly (fun p : TerminalHeader × FieldKey => terminalFieldReq p.1 p.2) := by
  have hk : Poly (fun p : TerminalHeader × FieldKey => (p.1, p.2.1)) := by fun_prop
  have i : Poly (fun p : TerminalHeader × FieldKey => p.2.2) := by fun_prop
  have sections := hk.compose finalSection_poly
  have trip := sections.fstCompose.pair (sections.sndCompose.pair i)
  exact ((show Poly (fun p : TerminalHeader × FieldKey => p.1.2.1) from by fun_prop).pair
    (trip.compose numericFieldReq_poly)).compose clipConeRequest_poly

theorem terminalFieldReq_addr (h : TerminalHeader) (k : FieldKey) :
    P1Batch.bval (terminalFieldReq h k).1 ≤ h.2.1 :=
  clipConeRequest_offset _ _

private theorem bitValue (n : ℕ) : P1Batch.bval n.bits = n := by rw [← bin_eq_bits, bval_bin]

theorem terminalFieldReq_eq (D : Dims) (m w v : ℕ) (clock : Tally) (k : FieldKey) (hk : k.1 < 13) :
    let q := terminalPhysicalKey D k
    terminalFieldReq (actualTerminalHeader D m w v clock) k = clipConeRequest m (fieldReq D q.1 q.2) := by
  unfold terminalPhysicalKey terminalFieldReq finalSection
  by_cases ho : k.1 = 12
  · simp only [ho, decide_true, Bool.cond_true, actualTerminalHeader, ite_true]
    have e4 : packetNat (fmt D) 4 = P1Batch.bval (Nat.bits (D.off D.secOmega)) := rfl
    have e5 : packetNat (fmt D) 5 = P1Batch.bval (Nat.bits (D.width D.secOmega)) := rfl
    rw [e4, e5, bitValue, bitValue, numericFieldReq_eq]
  · have hl : k.1 < 12 := by omega
    have he := Mem.toNat_ofNat k.1 hl
    simp only [ho, decide_false, Bool.cond_false, actualTerminalHeader, ite_false]
    have h := packetSection_phaseFormat D D.top (Mem.ofCode k.1)
    rw [he] at h
    rw [h, numericFieldReq_eq]

def terminalIncidenceKeys (h : TerminalHeader) : List FieldKey :=
  (capRange (h.1, terminalSlots h)).flatMap fun j =>
    let i := (terminalPos h).1 * terminalSlots h + j
    [(Mem.inAddr.toNat, i), (Mem.inDisp.toNat, i), (Mem.inFar.toNat, i)]

theorem terminalIncidenceKeys_poly : Poly terminalIncidenceKeys := by
  unfold terminalIncidenceKeys
  have h := (Easy.fst.poly.pair terminalSlots_poly).compose capRange_poly
  have key : Poly (fun p : TerminalHeader × ℕ =>
      let i := (terminalPos p.1).1 * terminalSlots p.1 + p.2
      [(Mem.inAddr.toNat, i), (Mem.inDisp.toNat, i), (Mem.inFar.toNat, i)]) := by
    dsimp only
    fun_prop
  exact (poly_mapParameter h key).compose Easy.flatten.poly

/-- One prefix and the complete width row at the specified base. -/
def terminalWidthKeys (h : TerminalHeader) (y : ℕ) : List FieldKey :=
  let count := terminalLanes h * terminalSlots h
  (12,y) :: (capRange (h.1,count)).map (fun j => (Mem.width.toNat,y*count+j))

theorem terminalWidthKeys_poly : Poly (fun p : TerminalHeader × ℕ => terminalWidthKeys p.1 p.2) := by
  unfold terminalWidthKeys
  have count : Poly (fun p : TerminalHeader × ℕ => terminalLanes p.1 * terminalSlots p.1) := by fun_prop
  have rng := ((Easy.fst.compose Easy.fst).poly.pair count).compose capRange_poly
  have e : Poly (fun p : (TerminalHeader × ℕ) × ℕ =>
      (Mem.width.toNat,p.1.2 * (terminalLanes p.1.1 * terminalSlots p.1.1) + p.2)) := by fun_prop
  exact ((show Poly (fun p : TerminalHeader × ℕ => (12,p.2)) from by fun_prop).pair
    (poly_mapParameter rng e)).compose Poly.cons

theorem readCachedTerminal (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally) (ks : List FieldKey)
    (hks : ∀ k ∈ ks, k.1 < 13) (k : FieldKey) (hk : k ∈ ks) :
    let h := actualTerminalHeader D u.length w v clock
    (fieldCache ks ((ks.map (terminalFieldReq h)).map (P1Batch.fetch u))).read k =
      readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2 := by
  dsimp only
  rw [List.map_map, fieldCache_read_on ks _ k hk]
  change bitsVal (P1Batch.fetch u (terminalFieldReq _ k)) = _
  rw [terminalFieldReq_eq _ _ _ _ _ _ (hks k hk), fetch_clipConeRequest, readField_eq]

private def incidenceAt (h : TerminalHeader) (c : FieldCache) (m k : ℕ) : ℕ :=
  c.read (m, (terminalPos h).1 * terminalSlots h + k)

@[fun_prop] private theorem incidenceAt_poly :
    Poly (fun p : TerminalHeader × FieldCache × ℕ × ℕ => incidenceAt p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold incidenceAt
  exact (show Poly (fun p : TerminalHeader × FieldCache × ℕ × ℕ =>
    (p.2.1, p.2.2.1, (terminalPos p.1).1 * terminalSlots p.1 + p.2.2.2)) from by fun_prop).compose
    fieldCache_read_poly

/-- Locate the payload in the source lane using the incoming displacement. -/
def cachedTerminalArcs (h : TerminalHeader) (c : FieldCache) : List ArcCode × List ArcCode :=
  let slots := capRange (h.1, terminalSlots h)
  let p := terminalPos h
  (slots.map (fun k => (p.1,p.2,k)), slots.map fun k =>
    (incidenceAt h c Mem.inAddr.toNat k, p.2 ^^^ incidenceAt h c Mem.inDisp.toNat k,
      incidenceAt h c Mem.inFar.toNat k))

theorem cachedTerminalArcs_poly : Poly (fun p : TerminalHeader × FieldCache => cachedTerminalArcs p.1 p.2) := by
  unfold cachedTerminalArcs
  have slots : Poly (fun p : TerminalHeader × FieldCache => capRange (p.1.1, terminalSlots p.1)) :=
    ((show Poly (fun p : TerminalHeader × FieldCache => p.1.1) from by fun_prop).pair
      (Easy.fst.poly.compose terminalSlots_poly)).compose capRange_poly
  apply (poly_mapParameter slots (show Poly (fun p : (TerminalHeader × FieldCache) × ℕ =>
    ((terminalPos p.1.1).1,(terminalPos p.1.1).2,p.2)) from by fun_prop)).pair
  have f (m : Mem) : Poly (fun p : (TerminalHeader × FieldCache) × ℕ => incidenceAt p.1.1 p.1.2 m.toNat p.2) :=
    (show Poly (fun p : (TerminalHeader × FieldCache) × ℕ => (p.1.1,p.1.2,m.toNat,p.2)) from by fun_prop).compose
      incidenceAt_poly
  have lane : Poly (fun p : (TerminalHeader × FieldCache) × ℕ => (terminalPos p.1.1).2) := by fun_prop
  exact poly_mapParameter slots ((f .inAddr).pair ((poly_xorNat lane (f .inDisp)).pair (f .inFar)))

theorem cachedTerminalArcs_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally)
    (hc : (D.lv D.top).slots ≤ clock.length) (cache : FieldCache)
    (he : ∀ k ∈ terminalIncidenceKeys (actualTerminalHeader D u.length w v clock),
      cache.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2) :
    cachedTerminalArcs (actualTerminalHeader D u.length w v clock) cache = terminalArcCodes D u v := by
  let L := D.lv D.top
  let y := v / L.lanes
  let h := actualTerminalHeader D u.length w v clock
  have range : capRange (h.1, terminalSlots h) = List.range L.slots := by
    change List.range (min (terminalSlots h) clock.length) = _
    rw [show terminalSlots h = L.slots from terminalSlots_actual .., min_eq_left hc]
  have index : (terminalPos h).1 = y := by simp only [h, y, terminalPos, terminalLanes_actual, L]; rfl
  have lane : (terminalPos h).2 = v % L.lanes := by simp only [h, terminalPos, terminalLanes_actual, L]; rfl
  have get (m : Mem) (k : ℕ) (hk : k ∈ List.range L.slots)
      (hm : m ∈ [Mem.inAddr, Mem.inDisp, Mem.inFar]) :
      incidenceAt h cache m.toNat k = readField D u (secLev D.top m) (y * L.slots + k) := by
    unfold incidenceAt
    rw [index, show terminalSlots h = L.slots from terminalSlots_actual ..]
    have key : (m.toNat, y * L.slots + k) ∈ terminalIncidenceKeys h := by
      unfold terminalIncidenceKeys
      rw [range]
      refine List.mem_flatMap.mpr ⟨k, hk, ?_⟩
      rw [index, show terminalSlots h = L.slots from terminalSlots_actual ..]
      exact (List.mem_map_of_mem hm :
        (m.toNat,y * L.slots + k) ∈ [Mem.inAddr, Mem.inDisp, Mem.inFar].map
          (fun n => (n.toNat,y * L.slots + k)))
    rw [he _ key]
    have hneq : m.toNat ≠ 12 := by have := m.toNat_lt; omega
    simp only [terminalPhysicalKey, hneq, ite_false, Mem.ofCode_toNat]
  unfold cachedTerminalArcs terminalArcCodes
  dsimp only
  rw [range, index, lane]
  apply Prod.ext
  · rfl
  apply List.map_congr_left
  intro k hk
  rw [get .inAddr _ hk (by simp), get .inDisp _ hk (by simp), get .inFar _ hk (by simp)]
  rfl

end P1SolCone.SolCone
