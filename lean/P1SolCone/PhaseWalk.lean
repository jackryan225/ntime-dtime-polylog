import P1SolCone.PhaseRead

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Extra fields may include the C10 kernel panel for each reached base. -/
def rawRoundKeys (extra : PhaseHeader × ℕ → List FieldKey) (h : PhaseHeader) (ys : List ℕ) : List FieldKey :=
  phaseFieldKey false .layout h 0 ::
    ys.flatMap fun y => rawBaseFields h y ++ extra (h,y)

theorem rawRoundKeys_poly {extra : PhaseHeader × ℕ → List FieldKey} (he : Poly extra) :
    Poly (fun p : PhaseHeader × List ℕ => rawRoundKeys extra p.1 p.2) := by
  unfold rawRoundKeys
  have head : Poly (fun p : PhaseHeader × List ℕ => (p.1,0)) := by fun_prop
  have arg : Poly (fun p : (PhaseHeader × List ℕ) × ℕ => (p.1.1,p.2)) := by fun_prop
  have data := arg.compose (rawBaseFields_poly.app he)
  exact ((head.compose (phaseFieldKey_poly false .layout)).pair
    ((poly_mapParameter Easy.snd.poly data).compose Easy.flatten.poly)).compose Poly.cons

theorem mem_rawRoundKeys_base (extra : PhaseHeader × ℕ → List FieldKey) {h : PhaseHeader} {ys : List ℕ}
    {y : ℕ} (hy : y ∈ ys) {k : FieldKey} (hk : k ∈ rawBaseFields h y) : k ∈ rawRoundKeys extra h ys :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨y,hy,List.mem_append_left _ hk⟩)

theorem mem_rawRoundKeys_extra (extra : PhaseHeader × ℕ → List FieldKey) {h : PhaseHeader} {ys : List ℕ}
    {y : ℕ} (hy : y ∈ ys) {k : FieldKey} (hk : k ∈ extra (h,y)) : k ∈ rawRoundKeys extra h ys :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨y,hy,List.mem_append_right _ hk⟩)

def rawLayoutKey (h : PhaseHeader) : FieldKey := phaseFieldKey false .layout h 0

def rawRoundCache (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool) (h : PhaseHeader) (ys : List ℕ) :
    FieldCache :=
  fetchPhaseFields u (rawRoundKeys extra h ys)

theorem rawRoundCache_read (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool) (h : PhaseHeader)
    (ys : List ℕ) (k : FieldKey) (hk : k ∈ rawRoundKeys extra h ys) :
    (rawRoundCache extra u h ys).read k = phaseFieldAt u k :=
  fetchPhaseFields_read _ _ _ hk

theorem rawRoundCache_layout (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ)
    (hw : D.width (secLev l .layout) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    rawRead h (rawRoundCache extra u h ys) .layout 0 = rdLayout D u l := by
  dsimp only
  unfold rawRead rdLayout
  rw [rawRoundCache_read _ _ _ _ _ List.mem_cons_self]
  exact read_phaseFieldKey D u l y clock false .layout 0 hw

theorem rawBaseFields_mem (h : PhaseHeader) (y j : ℕ) (hj : j ∈ rawSlots h) (m : Mem)
    (hm : m ∈ [Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar]) :
    phaseFieldKey false m h (y * packetNat h.2.2.2.2 4 + j) ∈ rawBaseFields h y := by
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨j,hj,?_⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rawSlotFields]

theorem rawRoundCache_incidence (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (z j : ℕ) (hz : z ∈ ys)
    (hc : (D.lv l).slots ≤ clock.length) (hj : j < (D.lv l).slots) (m : Mem)
    (hm : m ∈ [Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar])
    (hw : D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    rawIncidence h (rawRoundCache extra u h ys) m z j =
      readField D u (secLev l m) (z * (D.lv l).slots + j) := by
  let h := actualPhaseHeader D u l y clock
  have hs : packetNat h.2.2.2.2 4 = (D.lv l).slots := by
    change packetNat (phaseFormat D l) 4 = _
    rw [packetNat_phaseFormat]
    rfl
  have hslot : j ∈ rawSlots h := by
    rw [rawSlots_eq D u l y clock hc]
    exact List.mem_range.mpr hj
  have hk := mem_rawRoundKeys_base extra hz (rawBaseFields_mem h z j hslot m hm)
  change rawIncidence h _ m z j = _
  unfold rawIncidence rawRead
  rw [rawRoundCache_read _ _ _ _ _ hk, read_phaseFieldKey D u l y clock false m _ hw, hs]
  rfl

def actualRawNeighbors (D : Dims) (u : List Bool) (l z : ℕ) : List ℕ :=
  let js := List.range (D.lv l).slots
  js.map (rdOutAddr D u l z) ++ js.map (rdInAddr D u l z)

theorem rawNeighbors_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (z : ℕ) (hz : z ∈ ys)
    (hc : (D.lv l).slots ≤ clock.length)
    (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    rawNeighbors h (rawRoundCache extra u h ys) z = actualRawNeighbors D u l z := by
  dsimp only
  unfold rawNeighbors actualRawNeighbors
  rw [rawSlots_eq D u l y clock hc]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact rawRoundCache_incidence extra D u l y clock ys z j hz hc (List.mem_range.mp hj) .outAddr (by simp) (hw _)
  · apply List.map_congr_left
    intro j hj
    exact rawRoundCache_incidence extra D u l y clock ys z j hz hc (List.mem_range.mp hj) .inAddr (by simp) (hw _)

def extendRaw (h : PhaseHeader) (c : FieldCache) (ys : List ℕ) : List ℕ :=
  ys ++ ys.flatMap (rawNeighbors h c)

theorem extendRaw_poly : Poly (fun p : (PhaseHeader × FieldCache) × List ℕ => extendRaw p.1.1 p.1.2 p.2) := by
  unfold extendRaw
  have args : Poly (fun p : ((PhaseHeader × FieldCache) × List ℕ) × ℕ => (p.1.1.1,p.1.1.2,p.2)) := by fun_prop
  exact Easy.snd.poly.app ((poly_mapParameter Easy.snd.poly (args.compose rawNeighbors_poly)).compose Easy.flatten.poly)

def rawWalk (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool) (h : PhaseHeader) (roots : List ℕ) :
    ℕ → List ℕ
  | 0 => roots
  | r+1 =>
    let ys := rawWalk extra u h roots r
    extendRaw h (rawRoundCache extra u h ys) ys

def walkAddresses (next : ℕ → List ℕ) (roots : List ℕ) : ℕ → List ℕ
  | 0 => roots
  | r+1 =>
    let ys := walkAddresses next roots r
    ys ++ ys.flatMap next

theorem rawWalk_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (roots : List ℕ) (r : ℕ)
    (hc : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    rawWalk extra u (actualPhaseHeader D u l y clock) roots r =
      walkAddresses (actualRawNeighbors D u l) roots r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [rawWalk, walkAddresses, extendRaw, ih]
    congr 1
    apply List.flatMap_congr
    intro z hz
    exact rawNeighbors_eq extra D u l y clock _ z hz hc hw

end P1SolCone.SolCone
