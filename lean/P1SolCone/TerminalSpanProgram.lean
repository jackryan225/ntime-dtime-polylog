import P1SolCone.TerminalBatches

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1ProgEng.SolKWR
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Read the complete row in its lane-major order from the retained batch. -/
def cachedWidthRow (h : TerminalHeader) (c : FieldCache) (y : ℕ) : List ℕ :=
  let count := terminalLanes h * terminalSlots h
  (capRange (h.1, count)).map fun j => c.read (Mem.width.toNat, y * count + j)

theorem cachedWidthRow_poly :
    Poly (fun p : TerminalHeader × FieldCache × ℕ => cachedWidthRow p.1 p.2.1 p.2.2) := by
  unfold cachedWidthRow
  have cnt : Poly (fun p : TerminalHeader × FieldCache × ℕ => terminalLanes p.1 * terminalSlots p.1) := by fun_prop
  have clock : Poly (fun p : TerminalHeader × FieldCache × ℕ => p.1.1) := by fun_prop
  have reads : Poly (fun q : (TerminalHeader × FieldCache × ℕ) × ℕ =>
      (q.1.2.1, Mem.width.toNat, q.1.2.2 * (terminalLanes q.1.1 * terminalSlots q.1.1) + q.2)) := by fun_prop
  exact poly_mapParameter ((clock.pair cnt).compose capRange_poly) (reads.compose fieldCache_read_poly)

private theorem arcW_linear (D : Dims) (u : List Bool) (y j : ℕ) :
    arcW D u y j = readField D u (secLev D.top .width) (y * finArcs D + j) := by
  unfold arcW rdWidth finArcs
  congr 1
  rw [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, div_mul_add_mod]

theorem cachedWidthRow_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally) (cache : FieldCache) (y : ℕ)
    (hc : finArcs D ≤ clock.length)
    (hr : ∀ k ∈ terminalWidthKeys (actualTerminalHeader D u.length w v clock) y,
      cache.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2) :
    cachedWidthRow (actualTerminalHeader D u.length w v clock) cache y =
      (List.range (finArcs D)).map (arcW D u y) := by
  have rng : capRange ((actualTerminalHeader D u.length w v clock).1, finArcs D) =
      List.range (finArcs D) := by
    change List.range (min (finArcs D) clock.length) = _
    rw [min_eq_left hc]
  have mult : terminalLanes (actualTerminalHeader D u.length w v clock) *
      terminalSlots (actualTerminalHeader D u.length w v clock) = finArcs D := by
    rw [terminalLanes_actual, terminalSlots_actual]
    rfl
  unfold cachedWidthRow
  simp only [mult, rng]
  apply List.map_congr_left
  intro j hj
  rw [arcW_linear]
  have hm : (Mem.width.toNat, y * finArcs D + j) ∈ terminalWidthKeys
      (actualTerminalHeader D u.length w v clock) y := by
    unfold terminalWidthKeys
    simp only [mult, rng]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hj)
  rw [hr _ hm]
  rfl

theorem pre_eq_sumRange (f : ℕ → ℕ) (j : ℕ) : pre f j = ((List.range j).map f).sum := by
  induction j with
  | zero => simp [pre]
  | succ j ih =>
    simp only [pre, Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton] at ih ⊢
    rw [ih]

/-- Once both source addresses and width rows are available, only local arithmetic remains. -/
def cachedArcSpan (h : TerminalHeader) (c : FieldCache) (a : ArcCode) : Span :=
  let j := a.2.1 * terminalSlots h + a.2.2
  let row := cachedWidthRow h c a.1
  let start := packetNat h.2.2.2.2.1 2 + c.read (12,a.1) + (row.take j).sum
  (start, readAt 0 row j)

theorem cachedArcSpan_poly :
    Poly (fun p : TerminalHeader × FieldCache × ArcCode => cachedArcSpan p.1 p.2.1 p.2.2) := by
  unfold cachedArcSpan
  have index : Poly (fun p : TerminalHeader × FieldCache × ArcCode =>
      p.2.2.2.1 * terminalSlots p.1 + p.2.2.2.2) := by fun_prop
  have row := (show Poly (fun p : TerminalHeader × FieldCache × ArcCode => (p.1,p.2.1,p.2.2.1)) from
    by fun_prop).compose cachedWidthRow_poly
  have pref := (poly_take index row).compose sumNats_poly
  have start : Poly (fun p : TerminalHeader × FieldCache × ArcCode => packetNat p.1.2.2.2.2.1 2) := by fun_prop
  have om := (show Poly (fun p : TerminalHeader × FieldCache × ArcCode => (p.2.1,(12,p.2.2.1))) from
    by fun_prop).compose fieldCache_read_poly
  exact (poly_addNat (poly_addNat start om) pref).pair (poly_readAt 0 row index)

theorem cachedArcSpan_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally) (cache : FieldCache)
    (a : ArcCode) (hc : finArcs D ≤ clock.length) (ha : arcValid (D.lv D.top) a = true)
    (hr : ∀ k ∈ terminalWidthKeys (actualTerminalHeader D u.length w v clock) a.1,
      cache.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2) :
    cachedArcSpan (actualTerminalHeader D u.length w v clock) cache a = arcSpan D u a := by
  rcases a with ⟨y,l,k⟩
  simp only [arcValid, decide_eq_true_eq] at ha
  let L := D.lv D.top
  let j := l * L.slots + k
  have hj : j < finArcs D := idx_lt ha.2.1 ha.2.2
  have pref : (((List.range (finArcs D)).map (arcW D u y)).take j).sum = pre (arcW D u y) j := by
    rw [pre_eq_sumRange]
    congr 1
    apply List.ext_getElem
    · simp only [List.length_take, List.length_map, List.length_range, Nat.min_eq_left hj.le]
    · intros
      simp only [List.getElem_take, List.getElem_map, List.getElem_range]
  have word : readAt 0 ((List.range (finArcs D)).map (arcW D u y)) j = rdWidth D u D.top y l k := by
    have hlt : j < ((List.range (finArcs D)).map (arcW D u y)).length := by simpa only [List.length_map, List.length_range] using hj
    simp only [readAt, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_map, List.getElem_range]
    unfold arcW
    change rdWidth D u D.top y (j / L.slots) (j % L.slots) = _
    dsimp only [j]
    rw [idx_div ha.2.2, idx_mod ha.2.2]
  have prefixKey : (12,y) ∈ terminalWidthKeys (actualTerminalHeader D u.length w v clock) y :=
    List.mem_cons_self
  have om : cache.read (12,y) = rdOmega D u y := by
    rw [hr _ prefixKey]
    rfl
  have fixed : packetNat (phaseFormat D D.top) 2 = D.fixedLen := by rw [packetNat_phaseFormat]; rfl
  unfold cachedArcSpan
  simp only [terminalSlots_actual, cachedWidthRow_eq D u w v clock cache y hc hr, om]
  change (packetNat (phaseFormat D D.top) 2 + rdOmega D u y + _,
    readAt 0 ((List.range (finArcs D)).map (arcW D u y)) j) = _
  rw [fixed, pref, word]
  rfl

end P1SolCone.SolCone
