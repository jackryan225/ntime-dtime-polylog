import P1SolC10P.Table

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1Wit P1C10 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

set_option maxHeartbeats 1600000

abbrev EndRow (A : Type) := A × A × A
abbrev SlotRow (A : Type) := EndRow A × EndRow A × List A
abbrev PanelRows (A : Type) := List (SlotRow A)

def formatSlots (next : Bool) (h : C10Head) : ℕ := nget h (if next then 11 else 4)
def formatLanes (next : Bool) (h : C10Head) : ℕ := nget h (if next then 12 else 5)

@[fun_prop] theorem poly_formatSlots (next : Bool) : Poly (formatSlots next) := by
  unfold formatSlots
  fun_prop

@[fun_prop] theorem poly_formatLanes (next : Bool) : Poly (formatLanes next) := by
  unfold formatLanes
  fun_prop

theorem formatSlots_actual (next : Bool) (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    formatSlots next (actualHead D u l Y t) = (D.lv (if next then l + 1 else l)).slots := by
  cases next <;> change P1Batch.bval (Nat.bits _) = _ <;> rw [bval_bits] <;> rfl

theorem formatLanes_actual (next : Bool) (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    formatLanes next (actualHead D u l Y t) = (D.lv (if next then l + 1 else l)).lanes := by
  cases next <;> change P1Batch.bval (Nat.bits _) = _ <;> rw [bval_bits] <;> rfl

def widthKey (next : Bool) (h : C10Head) (y k ln : ℕ) : FieldKey :=
  fieldKey next .width h ((y * formatLanes next h + ln) * formatSlots next h + k)

@[fun_prop] theorem poly_widthKey (next : Bool) {X : Type} [Codec X]
    {h : X → C10Head} {y k ln : X → ℕ} (hh : Poly h) (hy : Poly y) (hk : Poly k) (hl : Poly ln) :
    Poly (fun x => widthKey next (h x) (y x) (k x) (ln x)) := by
  unfold widthKey
  fun_prop

def slotKeys (next : Bool) (h : C10Head) (y k : ℕ) : SlotRow FieldKey :=
  let i := y * formatSlots next h + k
  ((fieldKey next .outAddr h i, fieldKey next .outDisp h i, fieldKey next .outFar h i),
   (fieldKey next .inAddr h i, fieldKey next .inDisp h i, fieldKey next .inFar h i),
   tabN h.1 (if next then resLanes h else oldLanes h) (widthKey next h y k))

theorem poly_slotKeys (next : Bool) :
    Poly (fun p : (C10Head × ℕ) × ℕ => slotKeys next p.1.1 p.1.2 p.2) := by
  let Q := (C10Head × ℕ) × ℕ
  have ph : Poly (fun p : Q => p.1.1) := Easy.fst.poly.fstCompose
  have py : Poly (fun p : Q => p.1.2) := Easy.fst.poly.sndCompose
  have pk : Poly (fun p : Q => p.2) := Easy.snd.poly
  have i := poly_addNat (poly_mulNat py (ph.compose (poly_formatSlots next))) pk
  have p := poly_fieldKey next .outAddr ph i
  have q := poly_fieldKey next .outDisp ph i
  have r := poly_fieldKey next .outFar ph i
  have s := poly_fieldKey next .inAddr ph i
  have u := poly_fieldKey next .inDisp ph i
  have v := poly_fieldKey next .inFar ph i
  have w : Poly (fun x : Q × ℕ => widthKey next x.1.1.1 x.1.1.2 x.1.2 x.2) :=
    poly_widthKey next (Easy.fst.poly.compose ph) (Easy.fst.poly.compose py)
      (Easy.fst.poly.compose pk) Easy.snd.poly
  have n : Poly (fun x : Q => if next then resLanes x.1.1 else oldLanes x.1.1) := by
    cases next
    · exact ph.compose poly_oldLanes
    · exact ph.compose poly_resLanes
  have rows := poly_tabN ph.fstCompose n w
  exact (p.pair (q.pair r)).pair ((s.pair (u.pair v)).pair rows)

def panelShape (next : Bool) (h : C10Head) (y : ℕ) : PanelRows FieldKey :=
  tabN h.1 (if next then childSlots h else oldSlots h) (slotKeys next h y)

theorem poly_panelShape_pair (next : Bool) :
    Poly (fun p : C10Head × ℕ => panelShape next p.1 p.2) := by
  have n : Poly (fun p : C10Head × ℕ => if next then childSlots p.1 else oldSlots p.1) := by
    cases next
    · exact Easy.fst.poly.compose poly_oldSlots
    · exact Easy.fst.poly.compose poly_childSlots
  unfold panelShape
  exact poly_tabN Easy.fst.poly.fstCompose n (poly_slotKeys next)

@[fun_prop] theorem poly_panelShape (next : Bool) {X : Type} [Codec X]
    {h : X → C10Head} {y : X → ℕ} (hh : Poly h) (hy : Poly y) :
    Poly (fun x => panelShape next (h x) (y x)) :=
  (hh.pair hy).compose (poly_panelShape_pair next)

def slotKeyList (r : SlotRow FieldKey) : List FieldKey :=
  [r.1.1, r.1.2.1, r.1.2.2, r.2.1.1, r.2.1.2.1, r.2.1.2.2] ++ r.2.2

@[fun_prop] theorem poly_slotKeyList : Poly slotKeyList := by
  unfold slotKeyList
  fun_prop

def panelKeyList (next : Bool) (h : C10Head) (y : ℕ) : List FieldKey :=
  ((panelShape next h y).map slotKeyList).flatten

@[fun_prop] theorem poly_panelKeyList (next : Bool) {X : Type} [Codec X]
    {h : X → C10Head} {y : X → ℕ} (hh : Poly h) (hy : Poly y) :
    Poly (fun x => panelKeyList next (h x) (y x)) := by
  unfold panelKeyList
  exact poly_flatten ((poly_panelShape next hh hy).compose (Code.Poly.maps _ poly_slotKeyList))

def readSlot (f : FieldKey → ℕ) (s : SlotRow FieldKey) : SlotCode :=
  ((f s.1.1, f s.1.2.1, f s.1.2.2),
    (f s.2.1.1, f s.2.1.2.1, f s.2.1.2.2), s.2.2.map f)

def panelRead (f : FieldKey → ℕ) (next : Bool) (h : C10Head) (y : ℕ) : PanelCode :=
  (panelShape next h y).map (readSlot f)

theorem poly_readSlot_pair :
    Poly (fun q : FetchTable × SlotRow FieldKey => readSlot (tableRead q.1) q.2) := by
  unfold readSlot
  have w : Poly (fun q : FetchTable × SlotRow FieldKey => q.2.2.2.map (tableRead q.1)) :=
    poly_mapWith (g := fun p : (FetchTable × SlotRow FieldKey) × FieldKey => tableRead p.1.1 p.2)
      (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_panelRead (next : Bool) {X : Type} [Codec X] [Inhabited X]
    {xs : X → FetchTable} {h : X → C10Head} {y : X → ℕ}
    (hx : Poly xs) (hh : Poly h) (hy : Poly y) :
    Poly (fun x => panelRead (tableRead (xs x)) next (h x) (y x)) := by
  unfold panelRead
  exact (hx.pair (poly_panelShape next hh hy)).compose (poly_mapRight poly_readSlot_pair)

theorem panelRead_congr (f g : FieldKey → ℕ) (next : Bool) (h : C10Head) (y : ℕ)
    (he : ∀ k ∈ panelKeyList next h y, f k = g k) :
    panelRead f next h y = panelRead g next h y := by
  unfold panelRead
  apply List.map_congr_left
  intro row hr
  have e (k : FieldKey) (hk : k ∈ slotKeyList row) : f k = g k :=
    he k (by
      unfold panelKeyList
      exact List.mem_flatten.mpr ⟨slotKeyList row, List.mem_map_of_mem hr, hk⟩)
  have point := fun k (hk : k ∈ row.2.2) => e k (List.mem_append.mpr (Or.inr hk))
  simp only [readSlot, Prod.mk.injEq]
  have es : ∀ k ∈ [row.1.1, row.1.2.1, row.1.2.2, row.2.1.1, row.2.1.2.1, row.2.1.2.2],
      f k = g k := fun k hk => e k (List.mem_append.mpr (Or.inl hk))
  simp only [List.forall_mem_cons, List.not_mem_nil] at es
  exact ⟨⟨es.1, es.2.1, es.2.2.1⟩,
    ⟨es.2.2.2.1, es.2.2.2.2.1, es.2.2.2.2.2.1⟩, List.map_congr_left point⟩

def inC10Range (n x : ℕ) : ℕ := if x < n then x else 0

@[fun_prop] theorem poly_inC10Range {X : Type} [Codec X] {n v : X → ℕ}
    (hn : Poly n) (hv : Poly v) :
    Poly (fun x => inC10Range (n x) (v x)) := by
  unfold inC10Range
  exact Code.Poly.choose (poly_lt hv hn) hv (poly_const 0) |> fun h => by
    convert h using 1
    funext x
    by_cases e : v x < n x <;> simp only [e, ↓reduceIte, decide_true, decide_false,
      Bool.cond_true, Bool.cond_false]

def clipSlot (n : ℕ) (s : SlotCode) : SlotCode :=
  ((s.1.1, inC10Range n s.1.2.1, s.1.2.2),
    (s.2.1.1, inC10Range n s.2.1.2.1, s.2.1.2.2), s.2.2)

theorem poly_clipSlot : Poly (fun p : ℕ × SlotCode => clipSlot p.1 p.2) := by
  unfold clipSlot
  fun_prop

def clipPanel (n : ℕ) (p : PanelCode) : PanelCode := p.map (clipSlot n)

@[fun_prop] theorem poly_clipPanel {X : Type} [Inhabited X] [Codec X]
    {n : X → ℕ} {p : X → PanelCode} (hn : Poly n) (hp : Poly p) :
    Poly (fun x => clipPanel (n x) (p x)) := by
  unfold clipPanel
  exact (hn.pair hp).compose (poly_mapRight poly_clipSlot)

def codeNbrs (p : PanelCode) : List ℕ :=
  p.map (fun s => s.1.1) ++ p.map (fun s => s.2.1.1)

@[fun_prop] theorem poly_codeNbrs : Poly codeNbrs := by
  unfold codeNbrs
  exact (Code.Poly.maps _ Easy.fst.poly.fstCompose).app
    (Code.Poly.maps _ Easy.snd.poly.fstCompose.fstCompose)

theorem bwNum_bwOf_clip (g n : ℕ) : bwNum (bwOf g n) = inC10Range (2 ^ g) n := by
  unfold bwNum bwOf inC10Range
  split <;> simp only [Equiv.apply_symm_apply, *]

theorem clipPanel_storedPanel (D : Dims) (u : List Bool) (l y a g : ℕ) :
    clipPanel (2 ^ g) (storedPanel D u l y a g) = codePanel (decPanel D u l y a g) := by
  simp only [clipPanel, storedPanel, codePanel, List.map_ofFn, Function.comp_def, clipSlot]
  congr 1
  funext k
  simp only [codeSlot, decPanel, laneList]
  rw [bwNum_bwOf_clip, bwNum_bwOf_clip]
  simp only [bwNum, Equiv.apply_symm_apply]

theorem panelRead_actual {D : Dims} {l : ℕ} {t : Tally} (fit : Fits D l t) (u : List Bool)
    (Y y : ℕ) (next : Bool) :
    panelRead (fieldAt u) next (actualHead D u l Y t) y =
      if next then
        storedPanel D u (l + 1) y (slotBits D (l + 1)) (D.lv (l + 1)).laneW
      else
        storedPanel D u l y (slotBits D l)
          (if (D.lv l).shrink then
            OAI.Computability.VPVNP.Compression.packingLaneBits (slotBits D l) (D.lv (l + 1)).laneW
          else slotBits D l + (D.lv (l + 1)).laneW) := by
  have clock : (actualHead D u l Y t).1 = t := rfl
  have one (k : Mem) (i : ℕ) := fieldAt_fieldKey fit u Y next k i
  have shape (a g : ℕ)
      (hs : (if next then childSlots (actualHead D u l Y t) else oldSlots (actualHead D u l Y t)) = 2 ^ a)
      (hl : (if next then resLanes (actualHead D u l Y t) else oldLanes (actualHead D u l Y t)) = 2 ^ g)
      (ha : 2 ^ a ≤ t.length) (hg : 2 ^ g ≤ t.length) :
      panelRead (fieldAt u) next (actualHead D u l Y t) y =
        storedPanel D u (if next then l + 1 else l) y a g := by
    unfold panelRead panelShape
    rw [hs, clock, tabN_ofFn ha, List.map_ofFn]
    unfold storedPanel
    congr 1
    funext k
    simp only [Function.comp_def, slotKeys, readSlot, hl, clock, tabN_ofFn hg,
      List.map_ofFn]
    simp only [one, widthKey, formatSlots_actual, formatLanes_actual, rdOutAddr, rdOutDisp, rdOutFar,
      rdInAddr, rdInDisp, rdInFar, rdWidth]
  cases next
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases k : (D.lv l).shrink
    · exact shape _ _ (oldSlots_actual fit u Y) (by simp only [Bool.false_eq_true, ↓reduceIte,
          oldLanes_actual fit, k]) fit.slotsOld fit.lanesRefresh
    · exact shape _ _ (oldSlots_actual fit u Y) (by simp only [Bool.false_eq_true, ↓reduceIte,
          oldLanes_actual fit, k]) fit.slotsOld fit.lanesShrink
  · exact shape _ _ (childSlots_actual fit u Y) (resLanes_actual fit u Y) fit.slotsChild fit.lanesRes

theorem panelKeyList_bounds (next : Bool) (h : C10Head) (y : ℕ) {k : FieldKey}
    (hk : k ∈ panelKeyList next h y) : k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length := by
  simp only [panelKeyList, List.mem_flatten, List.mem_map] at hk
  rcases hk with ⟨_, ⟨r, hr, rfl⟩, hk⟩
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp (show r ∈
    (rangeIn h.1 (if next then childSlots h else oldSlots h)).map (slotKeys next h y) from hr)
  unfold slotKeys slotKeyList at hk
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, tabN,
    List.mem_map] at hk
  rcases hk with h' | ⟨j, _, h'⟩
  · rcases h' with h' | h' | h' | h' | h' | h'
    all_goals subst k
    all_goals exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩
  · subst k
    exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩

end P1SolC10P.SolC10prog
