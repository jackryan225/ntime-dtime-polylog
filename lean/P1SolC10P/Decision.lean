import P1SolC10P.Walk

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.Compression
open P1Wit P1C10 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

set_option maxHeartbeats 1600000

def eqList {A : Type} [Inhabited A] (cmp : A × A → Bool) (p : List A × List A) : Bool :=
  decide (p.1.length = p.2.length) &&
    (List.ofFn (fun i : Fin p.1.length =>
      (readAt default p.1 i.val, readAt default p.2 i.val))).all cmp

theorem poly_eqList {A : Type} [Inhabited A] [Codec A]
    {cmp : A × A → Bool} (hcmp : Poly cmp) : Poly (eqList cmp) := by
  have q := poly_tabLike (l := Prod.fst)
    (f := fun z : (List A × List A) × ℕ =>
      (readAt default z.1.1 z.2, readAt default z.1.2 z.2))
    Easy.fst.poly (by fun_prop)
  exact poly_and (poly_eqNat (poly_lengthNat Easy.fst.poly) (poly_lengthNat Easy.snd.poly))
    (poly_all q hcmp)

theorem readAt_get {A : Type} (d : A) {l : List A} {i : ℕ} (hi : i < l.length) :
    readAt d l i = l[i] := by
  simp only [readAt, List.getElem?_eq_getElem hi, Option.getD_some]

theorem eqList_true {A : Type} [Inhabited A] {cmp : A × A → Bool}
    (hc : ∀ a b, cmp (a, b) = true ↔ a = b) (p : List A × List A) :
    eqList cmp p = true ↔ p.1 = p.2 := by
  unfold eqList
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨hlen, hh⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have he := hh (_, _) ⟨⟨i, hi⟩, rfl⟩
    rw [readAt_get default hi, readAt_get default hj] at he
    exact (hc _ _).mp he
  · rcases p with ⟨xs, ys⟩
    intro e
    change xs = ys at e
    subst ys
    refine ⟨rfl, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (hc _ _).mpr rfl

def eqEnds (z : EndCode × EndCode) : Bool :=
  (decide (z.1.1 = z.2.1) && decide (z.1.2.1 = z.2.2.1)) && decide (z.1.2.2 = z.2.2.2)

theorem poly_eqEnds : Poly eqEnds := by unfold eqEnds; fun_prop

theorem eqEnds_true (a b : EndCode) : eqEnds (a, b) = true ↔ a = b := by
  simp only [eqEnds, Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff, and_assoc]

def eqWidths : List ℕ × List ℕ → Bool :=
  eqList (fun p : ℕ × ℕ => decide (p.1 = p.2))

theorem poly_eqWidths : Poly eqWidths :=
  poly_eqList (poly_eqNat Easy.fst.poly Easy.snd.poly)

theorem eqWidths_true (a b : List ℕ) : eqWidths (a, b) = true ↔ a = b :=
  eqList_true (cmp := fun p : ℕ × ℕ => decide (p.1 = p.2))
    (fun _ _ => ⟨of_decide_eq_true, decide_eq_true⟩) (a, b)

def eqSlots (z : SlotCode × SlotCode) : Bool :=
  (eqEnds (z.1.1, z.2.1) && eqEnds (z.1.2.1, z.2.2.1)) &&
    eqWidths (z.1.2.2, z.2.2.2)

theorem poly_eqSlots : Poly eqSlots := by
  unfold eqSlots
  have a := (show Poly (fun z : SlotCode × SlotCode => (z.1.1, z.2.1)) from by fun_prop).compose poly_eqEnds
  have b := (show Poly (fun z : SlotCode × SlotCode => (z.1.2.1, z.2.2.1)) from by fun_prop).compose poly_eqEnds
  have c := (show Poly (fun z : SlotCode × SlotCode => (z.1.2.2, z.2.2.2)) from by fun_prop).compose poly_eqWidths
  exact poly_and (poly_and a b) c

theorem eqSlots_true (a b : SlotCode) : eqSlots (a, b) = true ↔ a = b := by
  simp only [eqSlots, Bool.and_eq_true, eqEnds_true, eqWidths_true, Prod.ext_iff, and_assoc]

def checkSlotDisp (z : ℕ × SlotCode) : Bool :=
  decide (z.2.1.2.1 < z.1) && decide (z.2.2.1.2.1 < z.1)

theorem poly_checkSlotDisp : Poly checkSlotDisp := by unfold checkSlotDisp; fun_prop

def checkPanelDisp (n : ℕ) (p : PanelCode) : Bool := p.all (fun s => checkSlotDisp (n, s))

theorem poly_checkPanelDisp : Poly (fun p : ℕ × PanelCode => checkPanelDisp p.1 p.2) := by
  have h := poly_mapRight poly_checkSlotDisp
  have q := poly_all h (Code.Poly.identity (X := Bool))
  simpa only [checkPanelDisp, List.all_map, Function.comp_def] using q

theorem checkPanelDisp_actual (D : Dims) (u : List Bool) (l y a g : ℕ) :
    checkPanelDisp (2 ^ g) (storedPanel D u l y a g) = true ↔ DispOK D u l y a g := by
  simp only [checkPanelDisp, List.all_eq_true, storedPanel, List.mem_ofFn, checkSlotDisp,
    Bool.and_eq_true, decide_eq_true_eq, DispOK]
  constructor
  · intro h k
    exact h _ ⟨k, rfl⟩
  · intro h s hs
    obtain ⟨k, rfl⟩ := hs
    exact h k

def compareResult (p : ℕ × PanelCode × Option PanelCode) : Bool :=
  p.2.2.isSome && eqList eqSlots (p.2.2.getD [], p.2.1) && checkPanelDisp p.1 p.2.1

theorem poly_compareResult : Poly compareResult := by
  have opt : Poly (fun p : ℕ × PanelCode × Option PanelCode => p.2.2) :=
    Easy.snd.poly.sndCompose
  have someTest : Easy (fun p : Option PanelCode => p.isSome) := by
    convert OAI.Computability.NearSquareRoot.PhaseTable.easyOption
      false (fun _ : PanelCode => true) (Easy.const true) using 1
    funext p
    cases p <;> rfl
  have panel : Poly (fun p : ℕ × PanelCode × Option PanelCode => p.2.1) :=
    Easy.snd.poly.fstCompose
  have p : Poly (fun q : ℕ × PanelCode × Option PanelCode => (q.2.2.getD [], q.2.1)) := by
    convert (poly_defaultOption [] opt).pair panel using 1
    funext q
    cases q.2.2 <;> rfl
  exact poly_and (poly_and (opt.compose someTest.poly) (p.compose (poly_eqList poly_eqSlots)))
    ((Easy.fst.poly.pair panel).compose poly_checkPanelDisp)

theorem compareResult_true (D : Dims) (u : List Bool) (l y a g : ℕ) (r : Option PanelCode) :
    compareResult (2 ^ g, storedPanel D u l y a g, r) = true ↔
      r = some (storedPanel D u l y a g) ∧ DispOK D u l y a g := by
  have no : (none : Option PanelCode) ≠ some (storedPanel D u l y a g) := by
    intro e
    cases e
  cases r <;> simp only [compareResult, Option.isSome_none, Option.isSome_some,
    Bool.false_and, Bool.true_and, Bool.false_eq_true, Bool.and_eq_true, Option.getD_some,
    eqList_true eqSlots_true, checkPanelDisp_actual, no, Option.some.injEq, false_and]

def getLayout (h : C10Head) (v : FetchTable) : Bool :=
  decide (tableRead v (fieldKey false .layout h 0) = 1)

theorem poly_getLayout : Poly (fun p : C10Head × FetchTable => getLayout p.1 p.2) := by
  unfold getLayout
  fun_prop

def readRefresh (dH : ℕ) (h : C10Head) (v : FetchTable) (y : ℕ) : Option RefreshDatumCode :=
  if oldValid h y then
    some (clipPanel (oldLanes h) (panelRead (tableRead v) false h y), termsRead (tableRead v) dH h y)
  else none

def readShrink (dH : ℕ) (h : C10Head) (v : FetchTable) (y : ℕ) : Option ShrinkDatumCode :=
  if oldValid h y then
    some (clipPanel (oldLanes h) (panelRead (tableRead v) false h y),
      inC10Range (2 * oldSlots h + 1) (tableRead v (fieldKey false .colour h y)),
      inC10Range (tagLanes h) (tableRead v (fieldKey false .offset h y)),
      termsRead (tableRead v) dH h y)
  else none

theorem poly_readRefresh (dH : ℕ) :
    Poly (fun p : (C10Head × FetchTable) × ℕ => readRefresh dH p.1.1 p.1.2 p.2) := by
  unfold readRefresh
  fun_prop

theorem poly_readShrink (dH : ℕ) :
    Poly (fun p : (C10Head × FetchTable) × ℕ => readShrink dH p.1.1 p.1.2 p.2) := by
  unfold readShrink
  fun_prop

theorem readRefresh_actual {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally} (fit : Fits D l t)
    (hr : (D.lv l).shrink = false) (dH y : ℕ) (v : FetchTable)
    (he : ∀ k ∈ oldKeyList dH (actualHead D u l Y t) y, tableRead v k = fieldAt u k) :
    readRefresh dH (actualHead D u l Y t) v y =
      (decR (slotBits D l) (D.lv (l + 1)).laneW dH D u l y).map codeRefreshDatum := by
  unfold readRefresh decR
  by_cases hv : y < (D.lv l).bases
  · simp only [oldValid_actual, hv, decide_true, ↓reduceIte, Option.map_some]
    have hp := panelRead_congr (tableRead v) (fieldAt u) false (actualHead D u l Y t) y
      (fun k hk => he k (panel_old_mem hk))
    have ht := termsRead_congr (tableRead v) (fieldAt u) dH (actualHead D u l Y t) y
      (fun k hk => he k (term_old_mem hk))
    simp only [hp, ht, panelRead_actual fit, Bool.false_eq_true, ↓reduceIte, oldLanes_actual fit,
      hr, clipPanel_storedPanel, refreshTerms_actual fit u Y y dH hr, codeRefreshDatum, laneList,
      bwNum, Equiv.apply_symm_apply]
  · simp only [oldValid_actual, hv, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_none]

theorem finOf_clip (n v : ℕ) (h : 0 < n) :
    (finOf n h v : ℕ) = inC10Range n v := by
  unfold finOf inC10Range
  split <;> simp only [*]

theorem readShrink_actual {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally} (fit : Fits D l t)
    (hs : (D.lv l).shrink = true) (dH y : ℕ) (v : FetchTable)
    (he : ∀ k ∈ oldKeyList dH (actualHead D u l Y t) y, tableRead v k = fieldAt u k) :
    readShrink dH (actualHead D u l Y t) v y =
      (decS (slotBits D l) (D.lv (l + 1)).laneW D u l y).map codeShrinkDatum := by
  unfold readShrink decS
  by_cases hv : y < (D.lv l).bases
  · simp only [oldValid_actual, hv, decide_true, ↓reduceIte, Option.map_some]
    have hp := panelRead_congr (tableRead v) (fieldAt u) false (actualHead D u l Y t) y
      (fun k hk => he k (panel_old_mem hk))
    have ht := termsRead_congr (tableRead v) (fieldAt u) dH (actualHead D u l Y t) y
      (fun k hk => he k (term_old_mem hk))
    have hc := he (fieldKey false .colour (actualHead D u l Y t) y) List.mem_cons_self
    have ho := he (fieldKey false .offset (actualHead D u l Y t) y)
      (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [hp, ht, hc, ho, panelRead_actual fit, Bool.false_eq_true, ↓reduceIte,
      oldLanes_actual fit, hs, clipPanel_storedPanel, oldSlots_actual fit, tagLanes_actual fit,
      fieldAt_fieldKey fit, rdColour, rdOffset, shrinkTerms_actual fit u Y y dH hs,
      codeShrinkDatum, finOf_clip, bwNum_bwOf_clip]
  · simp only [oldValid_actual, hv, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_none]

def shrinkArg (dH : ℕ) (h : C10Head) (ys : List ℕ) (v : FetchTable) : (ℕ × ℕ) × ShrinkIn :=
  ((oldBits h, childBits h), (((parent h, ys.map (fun y => (y, readShrink dH h v y))),
    getLayout h v), childIndex h))

def refreshArg (dH : ℕ) (h : C10Head) (ys : List ℕ) (v : FetchTable) : RefreshIn :=
  ((parent h, ys.map (fun y => (y, readRefresh dH h v y))), childIndex h)

theorem poly_shrinkArg (dH : ℕ) :
    Poly (fun p : C10State => shrinkArg dH p.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold shrinkArg
  have h : Poly (fun p : C10State => p.1) := Easy.fst.poly
  have t : Poly (fun p : C10State => p.2.2.2.2) := by fun_prop
  have map : Poly (fun p : C10State =>
      p.2.2.2.1.map (fun y => (y, readShrink dH p.1 p.2.2.2.2 y))) :=
    poly_mapWith (g := fun z : C10State × ℕ => (z.2, readShrink dH z.1.1 z.1.2.2.2.2 z.2))
      (by fun_prop) (Easy.snd.poly.pair
        (((Easy.fst.poly.compose (h.pair t)).pair Easy.snd.poly).compose (poly_readShrink dH)))
  have lay := (h.pair t).compose poly_getLayout
  exact ((h.compose poly_oldBits).pair (h.compose poly_childBits)).pair
    ((((h.compose poly_parent).pair map).pair lay).pair (h.compose poly_childIndex))

theorem poly_refreshArg (dH : ℕ) :
    Poly (fun p : C10State => refreshArg dH p.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold refreshArg
  have h : Poly (fun p : C10State => p.1) := Easy.fst.poly
  have t : Poly (fun p : C10State => p.2.2.2.2) := by fun_prop
  have map : Poly (fun p : C10State =>
      p.2.2.2.1.map (fun y => (y, readRefresh dH p.1 p.2.2.2.2 y))) :=
    poly_mapWith (g := fun z : C10State × ℕ => (z.2, readRefresh dH z.1.1 z.1.2.2.2.2 z.2))
      (by fun_prop) (Easy.snd.poly.pair
        (((Easy.fst.poly.compose (h.pair t)).pair Easy.snd.poly).compose (poly_readRefresh dH)))
  exact ((h.compose poly_parent).pair map).pair (h.compose poly_childIndex)

def finalCheck (fx : C10Fix) (s : C10State) : Bool :=
  let h := s.1
  let ys := s.2.2.2.1
  let v := s.2.2.2.2
  if enabled h then
    let out := panelRead (tableRead v) true h h.2.2.2.1
    let candidate := if shrinking h then
      let args := shrinkArg fx.dH h ys v
      fx.rcS args.1.1 args.1.2 args.2
      else fx.rcR (refreshArg fx.dH h ys v)
    compareResult (resLanes h, out, candidate)
  else true

theorem poly_finalCheck (fx : C10Fix)
    (hS : Poly (fun q : (ℕ × ℕ) × ShrinkIn => fx.rcS q.1.1 q.1.2 q.2))
    (hR : Poly fx.rcR) : Poly (finalCheck fx) := by
  unfold finalCheck
  have h : Poly (fun s : C10State => s.1) := Easy.fst.poly
  have out : Poly (fun s : C10State => panelRead (tableRead s.2.2.2.2) true s.1 s.1.2.2.2.1) := by fun_prop
  have candidate := poly_if (h.compose poly_shrinking)
    ((poly_shrinkArg fx.dH).compose hS) ((poly_refreshArg fx.dH).compose hR)
  exact poly_if (h.compose poly_enabled)
    (((h.compose poly_resLanes).pair (out.pair candidate)).compose poly_compareResult) (poly_const true)

theorem finalCheck_view (fx : C10Fix) {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) (en : enabled (actualHead D u l Y t) = true)
    (z : C10State) (hz : z.1 = actualHead D u l Y t)
    (walk : z.2.2.2.1 = bfs (decodedNbrs D u l) (parent (actualHead D u l Y t))
      (if (D.lv l).shrink then 6 else 1))
    (child : ∀ k ∈ childKeyList (actualHead D u l Y t), tableRead z.2.2.2.2 k = fieldAt u k)
    (old : ∀ {y : ℕ}, y ∈ z.2.2.2.1 → ∀ k ∈ oldKeyList fx.dH (actualHead D u l Y t) y,
      tableRead z.2.2.2.2 k = fieldAt u k) :
    finalCheck fx z = decide (C10at fx D u l Y) := by
  let h := actualHead D u l Y t
  let ys := z.2.2.2.1
  let v := z.2.2.2.2
  have cl : h.2.2.2.1 = Y := rfl
  have out : panelRead (tableRead v) true h h.2.2.2.1 =
      storedPanel D u (l + 1) Y (slotBits D (l + 1)) (D.lv (l + 1)).laneW := by
    have reads : ∀ k ∈ panelKeyList true h h.2.2.2.1, tableRead v k = fieldAt u k :=
      fun k hk => child k (List.mem_cons_of_mem _ hk)
    rw [panelRead_congr _ _ _ _ _ reads, cl]
    exact panelRead_actual fit u Y Y true
  have lay : getLayout h v = layoutOf D u l := by
    unfold getLayout layoutOf rdLayout
    rw [child _ List.mem_cons_self, fieldAt_fieldKey fit]
    rfl
  have check : finalCheck fx z = true ↔ C10at fx D u l Y := by
    change (if enabled z.1 then
      compareResult (resLanes z.1, panelRead (tableRead v) true z.1 z.1.2.2.2.1,
        if shrinking z.1 then
          fx.rcS (shrinkArg fx.dH z.1 ys v).1.1 (shrinkArg fx.dH z.1 ys v).1.2
            (shrinkArg fx.dH z.1 ys v).2
        else fx.rcR (refreshArg fx.dH z.1 ys v)) else true) = true ↔ C10at fx D u l Y
    have eh : z.1 = h := hz
    rw [eh]
    simp only [show enabled h = true from en, ↓reduceIte, out, C10at]
    cases mode : (D.lv l).shrink with
    | false =>
      have fac : childFactor h = 2 ^ slotBits D l := by
        simp only [h, childFactor_actual fit, mode, Bool.false_eq_true, ↓reduceIte]
      have par : parent h = Y / 2 ^ slotBits D l := by rw [parent, fac, cl]
      have idx : childIndex h = Y % 2 ^ slotBits D l := by rw [childIndex, fac, cl]
      have addrs : ys =
          bfs (nbOf refreshNbrs (decR (slotBits D l) (D.lv (l + 1)).laneW fx.dH D u l))
            (Y / 2 ^ slotBits D l) 1 := by
        change z.2.2.2.1 = _
        rw [walk, par, decodedNbrs_refresh _ _ _ (D.lv (l + 1)).laneW fx.dH, mode]
        rfl
      have ball : ys.map (fun y => (y, readRefresh fx.dH h v y)) =
          ballList (nbOf refreshNbrs (decR (slotBits D l) (D.lv (l + 1)).laneW fx.dH D u l))
            (fun y => (decR (slotBits D l) (D.lv (l + 1)).laneW fx.dH D u l y).map codeRefreshDatum)
            (Y / 2 ^ slotBits D l) 1 := by
        unfold ballList
        rw [← addrs]
        apply List.map_congr_left
        intro y hy
        exact congrArg (fun r => (y, r)) (readRefresh_actual fit mode fx.dH y v (old hy))
      simp only [show shrinking h = false by rw [shrinking_actual, mode], Bool.false_eq_true,
        ↓reduceIte, refreshArg, par, idx, ball, show resLanes h = _ from resLanes_actual fit u Y,
        compareResult_true, C10rCode]
    | true =>
      have fac : childFactor h = shrinkJ (slotBits D l) := by
        simp only [h, childFactor_actual fit, mode, ↓reduceIte]
      have par : parent h = Y / shrinkJ (slotBits D l) := by rw [parent, fac, cl]
      have idx : childIndex h = Y % shrinkJ (slotBits D l) := by rw [childIndex, fac, cl]
      have addrs : ys =
          bfs (nbOf shrinkNbrs (decS (slotBits D l) (D.lv (l + 1)).laneW D u l))
            (Y / shrinkJ (slotBits D l)) 6 := by
        change z.2.2.2.1 = _
        rw [walk, par, decodedNbrs_shrink _ _ _ (D.lv (l + 1)).laneW, mode]
        rfl
      have ball : ys.map (fun y => (y, readShrink fx.dH h v y)) =
          ballList (nbOf shrinkNbrs (decS (slotBits D l) (D.lv (l + 1)).laneW D u l))
            (fun y => (decS (slotBits D l) (D.lv (l + 1)).laneW D u l y).map codeShrinkDatum)
            (Y / shrinkJ (slotBits D l)) 6 := by
        unfold ballList
        rw [← addrs]
        apply List.map_congr_left
        intro y hy
        exact congrArg (fun r => (y, r)) (readShrink_actual fit mode fx.dH y v (old hy))
      simp only [show shrinking h = true by rw [shrinking_actual, mode], ↓reduceIte, shrinkArg,
        show oldBits h = _ from oldBits_actual D u l Y t,
        show childBits h = _ from childBits_actual D u l Y t, par, idx, ball, lay,
        show resLanes h = _ from resLanes_actual fit u Y,
        compareResult_true, C10sCode]
  change finalCheck fx z = _
  by_cases e : C10at fx D u l Y
  · exact (check.mpr e).trans (decide_eq_true e).symm
  · exact (Bool.eq_false_of_not_eq_true (fun h => e (check.mp h))).trans (decide_eq_false e).symm

def roundCount (h : C10Head) : ℕ := if shrinking h then 7 else 2

theorem finalCheck_after (fx : C10Fix) {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) (en : enabled (actualHead D u l Y t) = true) (r : ℕ)
    (depth : walkDepth (D.lv l).shrink r = if (D.lv l).shrink then 6 else 1) :
    finalCheck fx (stateAt fx.dH u (actualHead D u l Y t) (r + 1)) = decide (C10at fx D u l Y) := by
  let h := actualHead D u l Y t
  let s := stateAt fx.dH u h r
  let z := stateAt fx.dH u h (r + 1)
  have hs : s.1 = h := stateAt_head fx.dH u h r
  have hz : z.1 = h := stateAt_head fx.dH u h (r + 1)
  have es : enabled s.1 = true := by rw [hs]; exact en
  have data := stateAt_data fx.dH u h en r
  have prev : z.2.2.2.1 = s.2.2.1 := data.1
  have replies : z.2.2.2.2 = readRound fx.dH u s := data.2
  change finalCheck fx z = _
  refine finalCheck_view (D := D) (u := u) (l := l) (Y := Y) (t := t) fx fit en z hz ?_ ?_ ?_
  · have hbfs : s.2.2.1 = bfs (decodedNbrs D u l) (parent h) (walkDepth (D.lv l).shrink r) :=
      (stateAt_walk fit en fx.dH r).2
    exact prev.trans (hbfs.trans (congrArg (bfs (decodedNbrs D u l) (parent h)) depth))
  · intro k hk
    have mem : k ∈ childKeyList s.1 := by rw [hs]; exact hk
    exact (congrArg (fun v => tableRead v k) replies).trans (round_read_child es u k mem)
  · intro y hy k hk
    have mem : k ∈ oldKeyList fx.dH s.1 y := by rw [hs]; exact hk
    rw [prev] at hy
    exact (congrArg (fun v => tableRead v k) replies).trans (round_read_old es u hy k mem)

theorem finalCheck_valid (fx : C10Fix) {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) (en : enabled (actualHead D u l Y t) = true) :
    finalCheck fx (stateAt fx.dH u (actualHead D u l Y t) (roundCount (actualHead D u l Y t))) =
      decide (C10at fx D u l Y) := by
  let h := actualHead D u l Y t
  let r : ℕ := if (D.lv l).shrink then 6 else 1
  have hr : roundCount h = r + 1 := by
    unfold roundCount
    rw [show shrinking h = (D.lv l).shrink from shrinking_actual D u l Y t]
    dsimp only [r]
    cases (D.lv l).shrink <;> rfl
  have hd : walkDepth (D.lv l).shrink r = if (D.lv l).shrink then 6 else 1 := by
    dsimp only [r]
    cases (D.lv l).shrink <;> rfl
  change finalCheck fx (stateAt fx.dH u h (roundCount h)) = _
  rw [hr]
  exact finalCheck_after fx fit en r hd

end P1SolC10P.SolC10prog
