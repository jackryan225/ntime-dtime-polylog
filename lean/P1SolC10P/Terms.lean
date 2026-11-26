import P1SolC10P.Panel

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.Compression
open P1Wit P1C10 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

set_option maxHeartbeats 1600000

def termsKey (h : C10Head) (y key col : ℕ) : FieldKey :=
  fieldKey false .terms h ((y * nget h 8 + key) * (nget h 9 + 1) + col)

@[fun_prop] theorem poly_termsKey {X : Type} [Codec X] {h : X → C10Head} {y key col : X → ℕ}
    (hh : Poly h) (hy : Poly y) (hk : Poly key) (hc : Poly col) :
    Poly (fun x => termsKey (h x) (y x) (key x) (col x)) := by
  unfold termsKey
  fun_prop

theorem termsKey_actual {D : Dims} {l : ℕ} {t : Tally} (fit : Fits D l t) (u : List Bool)
    (Y y key col : ℕ) :
    fieldAt u (termsKey (actualHead D u l Y t) y key col) = rdTerms D u l y key col := by
  have k : nget (actualHead D u l Y t) 8 = (D.lv l).termKeys := by
    change P1Batch.bval (Nat.bits _) = _
    rw [bval_bits]
  have a : nget (actualHead D u l Y t) 9 = (D.lv l).termArity := by
    change P1Batch.bval (Nat.bits _) = _
    rw [bval_bits]
  simp only [termsKey, k, a, fieldAt_fieldKey fit, rdTerms, Bool.false_eq_true, ↓reduceIte]

abbrev Axes (A : Type) := List (List (List A))

def shrinkTermKeys (h : C10Head) (y ln port : ℕ) : List FieldKey :=
  let key := ln * oldSlots h + port
  termsKey h y key 0 :: List.ofFn (fun c : Fin 8 => termsKey h y key (1 + c.val))

def tab2 {X A : Type} (t : X → Tally) (n m : X → ℕ) (f : (X × ℕ) × ℕ → A)
    (x : X) : List (List A) :=
  tabN (t x) (n x) (fun i => tabN (t x) (m x) (fun j => f ((x, i), j)))

theorem poly_tab2 {X A : Type} [Codec X] [Inhabited X] [Codec A]
    {t : X → Tally} {n m : X → ℕ} {f : (X × ℕ) × ℕ → A}
    (ht : Poly t) (hn : Poly n) (hm : Poly m) (hf : Poly f) : Poly (tab2 t n m f) := by
  let p : X × ℕ → X := Prod.fst
  have h : Poly p := Easy.fst.poly
  have inner := poly_tabN (h.compose ht) (h.compose hm) hf
  exact poly_tabN ht hn inner

def shrinkKeys (h : C10Head) (y : ℕ) : Axes FieldKey :=
  tab2 (fun p : C10Head × ℕ => p.1.1) (fun p => oldLanes p.1) (fun p => oldSlots p.1)
    (fun p => shrinkTermKeys p.1.1.1 p.1.1.2 p.1.2 p.2) (h, y)

theorem poly_shrinkTermKeys :
    Poly (fun p : ((C10Head × ℕ) × ℕ) × ℕ => shrinkTermKeys p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold shrinkTermKeys
  apply poly_consVal
  · fun_prop
  · apply poly_fixedTab
    intro c
    fun_prop

theorem poly_shrinkKeys : Poly (fun p : C10Head × ℕ => shrinkKeys p.1 p.2) := by
  unfold shrinkKeys
  exact poly_tab2 (X := C10Head × ℕ) (A := List FieldKey) Easy.fst.poly.fstCompose
    (Easy.fst.poly.compose poly_oldLanes) (Easy.fst.poly.compose poly_oldSlots) poly_shrinkTermKeys

def refreshTermKeys (dH : ℕ) (h : C10Head) (y ln port : ℕ) : List FieldKey :=
  List.ofFn (fun j : Fin dH => termsKey h y ln (1 + (port * dH + j.val)))

def refreshKeys (dH : ℕ) (h : C10Head) (y : ℕ) : Axes FieldKey :=
  tab2 (fun p : C10Head × ℕ => p.1.1) (fun p => resLanes p.1) (fun p => oldSlots p.1)
    (fun p => refreshTermKeys dH p.1.1.1 p.1.1.2 p.1.2 p.2) (h, y)

theorem poly_refreshTermKeys (dH : ℕ) :
    Poly (fun p : ((C10Head × ℕ) × ℕ) × ℕ => refreshTermKeys dH p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold refreshTermKeys
  apply poly_fixedTab
  intro j
  fun_prop

theorem poly_refreshKeys (dH : ℕ) : Poly (fun p : C10Head × ℕ => refreshKeys dH p.1 p.2) := by
  unfold refreshKeys
  exact poly_tab2 (X := C10Head × ℕ) (A := List FieldKey) Easy.fst.poly.fstCompose
    (Easy.fst.poly.compose poly_resLanes) (Easy.fst.poly.compose poly_oldSlots) (poly_refreshTermKeys dH)

def termShape (dH : ℕ) (h : C10Head) (y : ℕ) : Axes FieldKey :=
  if shrinking h then shrinkKeys h y else refreshKeys dH h y

@[fun_prop] theorem poly_termShape (dH : ℕ) {X : Type} [Codec X]
    {h : X → C10Head} {y : X → ℕ} (hh : Poly h) (hy : Poly y) :
    Poly (fun x => termShape dH (h x) (y x)) := by
  unfold termShape
  exact poly_if (hh.compose poly_shrinking) ((hh.pair hy).compose poly_shrinkKeys)
    ((hh.pair hy).compose (poly_refreshKeys dH))

def termKeyList (dH : ℕ) (h : C10Head) (y : ℕ) : List FieldKey :=
  (termShape dH h y).flatten.flatten

@[fun_prop] theorem poly_termKeyList (dH : ℕ) {X : Type} [Codec X]
    {h : X → C10Head} {y : X → ℕ} (hh : Poly h) (hy : Poly y) :
    Poly (fun x => termKeyList dH (h x) (y x)) :=
  poly_flatten (poly_flatten (poly_termShape dH hh hy))

def interpretTerms (f : FieldKey → ℕ) (a : Axes FieldKey) : Axes ℕ :=
  a.map (List.map (List.map f))

theorem poly_interpretTerms :
    Poly (fun p : FetchTable × Axes FieldKey => interpretTerms (tableRead p.1) p.2) :=
  poly_mapRight (poly_mapRight (poly_mapRight poly_tableRead_pair))

def normalizeTerm (r : List ℕ) : List ℕ :=
  if decide (readAt 0 r 0 = 1) then r else List.replicate 9 0

theorem poly_normalizeTerm : Poly normalizeTerm := by
  unfold normalizeTerm
  fun_prop

def termsRead (f : FieldKey → ℕ) (dH : ℕ) (h : C10Head) (y : ℕ) : Axes ℕ :=
  let r := interpretTerms f (termShape dH h y)
  if shrinking h then r.map (List.map normalizeTerm) else r

@[fun_prop] theorem poly_termsRead (dH : ℕ) {X : Type} [Codec X] {h : X → C10Head}
    {y : X → ℕ} {v : X → FetchTable} (hh : Poly h) (hy : Poly y) (hv : Poly v) :
    Poly (fun x => termsRead (tableRead (v x)) dH (h x) (y x)) := by
  unfold termsRead
  have p := (hv.pair (poly_termShape dH hh hy)).compose poly_interpretTerms
  exact poly_if (hh.compose poly_shrinking)
    (p.compose (Code.Poly.maps _ (Code.Poly.maps _ poly_normalizeTerm))) p

theorem termsRead_congr (f g : FieldKey → ℕ) (dH : ℕ) (h : C10Head) (y : ℕ)
    (he : ∀ k ∈ termKeyList dH h y, f k = g k) :
    termsRead f dH h y = termsRead g dH h y := by
  unfold termsRead
  have e : interpretTerms f (termShape dH h y) = interpretTerms g (termShape dH h y) := by
    unfold interpretTerms
    apply List.map_congr_left
    intro a ha
    apply List.map_congr_left
    intro r hr
    apply List.map_congr_left
    intro k hk
    exact he k (List.mem_flatten.mpr ⟨r, List.mem_flatten.mpr ⟨a, ha, hr⟩, hk⟩)
  rw [e]

theorem termKeyList_bounds (dH : ℕ) (h : C10Head) (y : ℕ) {k : FieldKey}
    (hk : k ∈ termKeyList dH h y) : k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length := by
  obtain ⟨r, hr, hk⟩ := List.mem_flatten.mp hk
  obtain ⟨a, ha, hr⟩ := List.mem_flatten.mp hr
  unfold termShape at ha
  split at ha
  · simp only [shrinkKeys, tab2, tabN, List.mem_map] at ha
    obtain ⟨ln, _, rfl⟩ := ha
    simp only [List.mem_map] at hr
    obtain ⟨port, _, rfl⟩ := hr
    simp only [shrinkTermKeys, List.mem_cons, List.mem_ofFn] at hk
    rcases hk with e | ⟨c, e⟩ <;> subst k <;>
      exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩
  · simp only [refreshKeys, tab2, tabN, List.mem_map] at ha
    obtain ⟨ln, _, rfl⟩ := ha
    simp only [List.mem_map] at hr
    obtain ⟨port, _, rfl⟩ := hr
    obtain ⟨j, e⟩ := List.mem_ofFn.mp hk
    subst k
    exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩

theorem ofFn_eight {A : Type} (f : ℕ → A) :
    (List.ofFn fun j : Fin 8 => f j.val) =
      (List.ofFn fun j : Fin 4 => f j.val) ++ (List.ofFn fun j : Fin 4 => f (4 + j.val)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split
    · rfl
    · congr 1
      omega

theorem normalizeTerm_cons (n : ℕ) (f : ℕ → ℕ) :
    normalizeTerm (n :: List.ofFn (fun c : Fin 8 => f c.val)) =
      if n = 1 then 1 :: ((List.ofFn fun c : Fin 4 => f c.val) ++
        (List.ofFn fun c : Fin 4 => f (4 + c.val))) else 0 :: List.replicate 8 0 := by
  have hh : readAt 0 (n :: List.ofFn (fun c : Fin 8 => f c.val)) 0 = n := rfl
  unfold normalizeTerm
  rw [hh, ofFn_eight]
  by_cases e : n = 1
  · subst n
    simp only [decide_true, ↓reduceIte]
  · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem refreshTerms_actual {D : Dims} {l : ℕ} {t : Tally} (fit : Fits D l t) (u : List Bool)
    (Y y dH : ℕ) (hr : (D.lv l).shrink = false) :
    termsRead (fieldAt u) dH (actualHead D u l Y t) y =
      List.ofFn (fun ln : Fin (2 ^ (D.lv (l + 1)).laneW) =>
        List.ofFn (fun j : Fin (2 ^ slotBits D l) =>
          List.ofFn (fun i : Fin dH => rdTerms D u l y ln (1 + (j.val * dH + i.val))))) := by
  simp only [termsRead, termShape, shrinking_actual, hr, Bool.false_eq_true, ↓reduceIte,
    interpretTerms, refreshKeys, tab2, oldSlots_actual fit, resLanes_actual fit]
  have clock : (actualHead D u l Y t).1 = t := rfl
  simp only [clock, tabN_ofFn fit.lanesRes, tabN_ofFn fit.slotsOld, List.map_ofFn,
    Function.comp_def, refreshTermKeys, termsKey_actual fit]

theorem shrinkTerms_actual {D : Dims} {l : ℕ} {t : Tally} (fit : Fits D l t) (u : List Bool)
    (Y y dH : ℕ) (hs : (D.lv l).shrink = true) :
    termsRead (fieldAt u) dH (actualHead D u l Y t) y =
      (codeShrinkDatum
        (decPanel D u l y (slotBits D l) (packingLaneBits (slotBits D l) (D.lv (l + 1)).laneW),
          ⟨0, by omega⟩, bwOf (packingTagBits (2 ^ slotBits D l)) 0,
          termsDec (a := slotBits D l) (g := (D.lv (l + 1)).laneW) D u l y)).2.2.2 := by
  have clock : (actualHead D u l Y t).1 = t := rfl
  simp only [termsRead, termShape, shrinking_actual, hs, ↓reduceIte, interpretTerms,
    shrinkKeys, tab2, oldSlots_actual fit, oldLanes_actual fit, clock, tabN_ofFn fit.slotsOld,
    tabN_ofFn fit.lanesShrink, List.map_ofFn, Function.comp_def, shrinkTermKeys,
    List.map_cons, termsKey_actual fit, codeShrinkDatum, laneList, termsDec]
  congr 1
  funext ln
  congr 1
  funext port
  let a := slotBits D l
  let g := (D.lv (l + 1)).laneW
  let w := (bitWordFinEquiv (packingLaneBits a g)).symm ln
  let z := packingFields a g w
  have hk : bwNum ((packingFields a g).symm (z.1, z.2.1, (z.2.2.1, z.2.2.2))) = ln.val := by
    change bwNum ((packingFields a g).symm (packingFields a g w)) = _
    simp only [AddEquiv.symm_apply_apply, w, bwNum, Equiv.apply_symm_apply]
  rw [hk, normalizeTerm_cons _ (fun c => rdTerms D u l y (ln.val * 2 ^ a + port.val) (1 + c))]
  by_cases h : rdTerms D u l y (ln.val * 2 ^ a + port.val) 0 = 1
  · simp only [a] at h
    simp only [a, h, ↓reduceIte, shrinkTermCode, tIdx, Bool.false_eq_true, Nat.zero_add]
  · simp only [a] at h
    simp only [h, ↓reduceIte, shrinkTermCode]

end P1SolC10P.SolC10prog
