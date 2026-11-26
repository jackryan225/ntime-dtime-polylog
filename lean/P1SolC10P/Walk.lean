import P1SolC10P.Terms

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.Compression
open P1Wit P1C10 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

set_option maxHeartbeats 1600000

/-- Header, whether a fetch has occurred, next addresses, previous addresses, and previous replies. -/
abbrev C10State := C10Head × Bool × List ℕ × List ℕ × FetchTable

def initial (h : C10Head) : C10State := (h, false, [parent h], [], [])

theorem poly_initial : Poly initial := by unfold initial; fun_prop

def childKeyList (h : C10Head) : List FieldKey :=
  fieldKey false .layout h 0 :: panelKeyList true h h.2.2.2.1

def oldKeyList (dH : ℕ) (h : C10Head) (y : ℕ) : List FieldKey :=
  fieldKey false .colour h y :: fieldKey false .offset h y ::
    (panelKeyList false h y ++ termKeyList dH h y)

@[fun_prop] theorem poly_childKeyList : Poly childKeyList := by unfold childKeyList; fun_prop

theorem poly_oldKeyList (dH : ℕ) :
    Poly (fun p : C10Head × ℕ => oldKeyList dH p.1 p.2) := by
  unfold oldKeyList
  fun_prop

def roundKeys (dH : ℕ) (s : C10State) : List FieldKey :=
  if enabled s.1 then
    childKeyList s.1 ++ (s.2.2.1.map (oldKeyList dH s.1)).flatten
  else []

@[fun_prop] theorem poly_roundKeys (dH : ℕ) : Poly (roundKeys dH) := by
  unfold roundKeys
  have child : Poly (fun s : C10State => childKeyList s.1) :=
    Easy.fst.poly.compose poly_childKeyList
  have old : Poly (fun s : C10State => s.2.2.1.map (oldKeyList dH s.1)) :=
    poly_mapWith (g := fun p : C10State × ℕ => oldKeyList dH p.1.1 p.2)
      (by fun_prop) ((Easy.fst.poly.fstCompose.pair Easy.snd.poly).compose (poly_oldKeyList dH))
  exact poly_if (Easy.fst.poly.compose poly_enabled) (child.app (poly_flatten old)) (poly_const [])

def requests (dH : ℕ) (s : C10State) : List P1Batch.Req := (roundKeys dH s).map reqOf

@[fun_prop] theorem poly_requests (dH : ℕ) : Poly (requests dH) :=
  (poly_roundKeys dH).compose (Code.Poly.maps _ poly_reqOf)

def neighbors (h : C10Head) (v : FetchTable) (y : ℕ) : List ℕ :=
  if oldValid h y then codeNbrs (panelRead (tableRead v) false h y) else []

theorem poly_neighbors : Poly (fun p : (C10Head × FetchTable) × ℕ => neighbors p.1.1 p.1.2 p.2) := by
  unfold neighbors
  fun_prop

def extendAddresses (h : C10Head) (v : FetchTable) (ys : List ℕ) : List ℕ :=
  ys ++ (ys.map (neighbors h v)).flatten

theorem poly_extendAddresses :
    Poly (fun p : (C10Head × FetchTable) × List ℕ => extendAddresses p.1.1 p.1.2 p.2) := by
  unfold extendAddresses
  exact Easy.snd.poly.app (poly_flatten (poly_mapWith
    (g := fun p : ((C10Head × FetchTable) × List ℕ) × ℕ => neighbors p.1.1.1 p.1.1.2 p.2)
    Easy.snd.poly ((Easy.fst.poly.fstCompose.pair Easy.snd.poly).compose poly_neighbors)))

def advance (dH : ℕ) (p : C10State × Words) : C10State :=
  let s := p.1
  if enabled s.1 then
    let v := makeTable (roundKeys dH s, p.2)
    let ys := s.2.2.1
    let next := if shrinking s.1 || !s.2.1 then extendAddresses s.1 v ys else ys
    (s.1, true, next, ys, v)
  else s

theorem poly_advance (dH : ℕ) : Poly (advance dH) := by
  unfold advance
  have ph : Poly (fun p : C10State × Words => p.1.1) := Easy.fst.poly.fstCompose
  have pt : Poly (fun p : C10State × Words => makeTable (roundKeys dH p.1, p.2)) :=
    ((Easy.fst.poly.compose (poly_roundKeys dH)).pair Easy.snd.poly).compose poly_makeTable
  have pys : Poly (fun p : C10State × Words => p.1.2.2.1) := by fun_prop
  have pe := ((ph.pair pt).pair pys).compose poly_extendAddresses
  have psi : Poly (fun p : C10State × Words => shrinking p.1.1 || !p.1.2.1) := by fun_prop
  exact poly_if (ph.compose poly_enabled)
    (ph.pair ((poly_const true).pair ((poly_if psi pe pys).pair (pys.pair pt)))) Easy.fst.poly

theorem advance_head (dH : ℕ) (s : C10State) (ws : Words) : (advance dH (s, ws)).1 = s.1 := by
  unfold advance
  dsimp only
  split <;> rfl

theorem childKeyList_bounds (h : C10Head) {k : FieldKey} (hk : k ∈ childKeyList h) :
    k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length := by
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩
  · exact panelKeyList_bounds _ _ _ hk

theorem oldKeyList_bounds (dH : ℕ) (h : C10Head) (y : ℕ) {k : FieldKey}
    (hk : k ∈ oldKeyList dH h y) : k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length := by
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨fieldKey_address_le _ _ _ _, fieldKey_width_le _ _ _ _⟩
  rcases List.mem_append.mp hk with hk | hk
  · exact panelKeyList_bounds _ _ _ hk
  · exact termKeyList_bounds _ _ _ hk

theorem roundKeys_bounds (dH : ℕ) (s : C10State) {k : FieldKey}
    (hk : k ∈ roundKeys dH s) : k.1 ≤ s.1.2.1 ∧ k.2 ≤ s.1.1.length := by
  unfold roundKeys at hk
  split at hk
  · rcases List.mem_append.mp hk with hk | hk
    · exact childKeyList_bounds _ hk
    · obtain ⟨ks, hs, hk⟩ := List.mem_flatten.mp hk
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hs
      exact oldKeyList_bounds _ _ _ hk
  · cases hk

theorem child_mem_roundKeys {dH : ℕ} {s : C10State} (he : enabled s.1 = true)
    {k : FieldKey} (hk : k ∈ childKeyList s.1) : k ∈ roundKeys dH s := by
  unfold roundKeys
  simp only [he, ↓reduceIte]
  exact List.mem_append_left _ hk

theorem old_mem_roundKeys {dH : ℕ} {s : C10State} (he : enabled s.1 = true)
    {y : ℕ} (hy : y ∈ s.2.2.1) {k : FieldKey} (hk : k ∈ oldKeyList dH s.1 y) :
    k ∈ roundKeys dH s := by
  unfold roundKeys
  simp only [he, ↓reduceIte]
  exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hy, hk⟩)

theorem panel_old_mem {dH : ℕ} {h : C10Head} {y : ℕ} {k : FieldKey}
    (hk : k ∈ panelKeyList false h y) : k ∈ oldKeyList dH h y :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hk))

theorem term_old_mem {dH : ℕ} {h : C10Head} {y : ℕ} {k : FieldKey}
    (hk : k ∈ termKeyList dH h y) : k ∈ oldKeyList dH h y :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hk))

abbrev readRound (dH : ℕ) (u : List Bool) (s : C10State) : FetchTable :=
  makeTable (roundKeys dH s, (requests dH s).map (P1Batch.fetch u))

theorem round_read_child {dH : ℕ} {s : C10State} (he : enabled s.1 = true) (u : List Bool) :
    ∀ k ∈ childKeyList s.1, tableRead (readRound dH u s) k = fieldAt u k :=
  fun _ hk => tableRead_fetch u (child_mem_roundKeys he hk)

theorem round_read_old {dH : ℕ} {s : C10State} (he : enabled s.1 = true) (u : List Bool)
    {y : ℕ} (hy : y ∈ s.2.2.1) :
    ∀ k ∈ oldKeyList dH s.1 y, tableRead (readRound dH u s) k = fieldAt u k :=
  fun _ hk => tableRead_fetch u (old_mem_roundKeys he hy hk)

def decodedNbrs (D : Dims) (u : List Bool) (l y : ℕ) : List ℕ :=
  if y < (D.lv l).bases then
    (List.ofFn (fun k : Fin (2 ^ slotBits D l) => rdOutAddr D u l y k)) ++
      (List.ofFn (fun k : Fin (2 ^ slotBits D l) => rdInAddr D u l y k))
  else []

theorem decodedNbrs_shrink (D : Dims) (u : List Bool) (l g : ℕ) :
    decodedNbrs D u l = nbOf shrinkNbrs (decS (slotBits D l) g D u l) := by
  funext y
  unfold decodedNbrs nbOf decS
  split <;> rfl

theorem decodedNbrs_refresh (D : Dims) (u : List Bool) (l g dH : ℕ) :
    decodedNbrs D u l = nbOf refreshNbrs (decR (slotBits D l) g dH D u l) := by
  funext y
  unfold decodedNbrs nbOf decR
  split <;> rfl

theorem neighbors_actual {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) (v : FetchTable) (y : ℕ)
    (he : ∀ k ∈ panelKeyList false (actualHead D u l Y t) y, tableRead v k = fieldAt u k) :
    neighbors (actualHead D u l Y t) v y = decodedNbrs D u l y := by
  unfold neighbors decodedNbrs
  rw [oldValid_actual, panelRead_congr _ _ _ _ _ he, panelRead_actual fit]
  simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  by_cases hv : y < (D.lv l).bases
  · simp only [hv, ↓reduceIte, codeNbrs, storedPanel, List.map_ofFn, Function.comp_def]
  · simp only [hv, ↓reduceIte]

theorem extend_actual {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) {dH : ℕ} {s : C10State}
    (hh : s.1 = actualHead D u l Y t) (he : enabled s.1 = true) :
    extendAddresses s.1 (readRound dH u s) s.2.2.1 =
      s.2.2.1 ++ s.2.2.1.flatMap (decodedNbrs D u l) := by
  unfold extendAddresses
  rw [List.flatMap_def]
  refine congrArg (fun xs => s.2.2.1 ++ xs) (congrArg List.flatten ?_)
  apply List.map_congr_left
  intro y hy
  rw [hh]
  apply neighbors_actual fit
  intro k hk
  exact round_read_old he u hy k (panel_old_mem (by rwa [hh]))

def walkDepth (sh : Bool) (r : ℕ) : ℕ := if sh then r else min r 1

theorem walkDepth_succ (sh : Bool) (r : ℕ) :
    walkDepth sh (r + 1) =
      if sh || !(decide (0 < r)) then walkDepth sh r + 1 else walkDepth sh r := by
  cases sh <;> cases r <;> simp [walkDepth]

abbrev stateAt (dH : ℕ) (u : List Bool) (h : C10Head) (r : ℕ) : C10State :=
  roundState (requests dH) (advance dH) u (initial h) r

theorem stateAt_head (dH : ℕ) (u : List Bool) (h : C10Head) (r : ℕ) :
    (stateAt dH u h r).1 = h := by
  induction r with
  | zero => rfl
  | succ r ih => exact (advance_head ..).trans ih

theorem stateAt_walk {D : Dims} {u : List Bool} {l Y : ℕ} {t : Tally}
    (fit : Fits D l t) (he : enabled (actualHead D u l Y t) = true) (dH r : ℕ) :
    let h := actualHead D u l Y t
    let s := stateAt dH u h r
    s.2.1 = decide (0 < r) ∧ s.2.2.1 =
      bfs (decodedNbrs D u l) (parent h) (walkDepth (D.lv l).shrink r) := by
  let h := actualHead D u l Y t
  change (stateAt dH u h r).2.1 = decide (0 < r) ∧ (stateAt dH u h r).2.2.1 = _
  induction r with
  | zero =>
    have hz : walkDepth (D.lv l).shrink 0 = 0 := by
      cases (D.lv l).shrink <;> rfl
    rw [hz]
    exact ⟨rfl, rfl⟩
  | succ r ih =>
    let s := stateAt dH u h r
    have hh : s.1 = h := stateAt_head ..
    have en : enabled s.1 = true := by rw [hh]; exact he
    have sk : shrinking s.1 = (D.lv l).shrink := by rw [hh, shrinking_actual]
    have ext := extend_actual (dH := dH) fit hh en
    change (advance dH (s, (requests dH s).map (P1Batch.fetch u))).2.1 = _ ∧
      (advance dH (s, (requests dH s).map (P1Batch.fetch u))).2.2.1 = _
    have seen : s.2.1 = decide (0 < r) := ih.1
    have addrs : s.2.2.1 = bfs (decodedNbrs D u l) (parent h) (walkDepth (D.lv l).shrink r) := ih.2
    constructor
    · simp only [advance, en, ↓reduceIte, Nat.zero_lt_succ, decide_true]
    · simp only [advance, en, ↓reduceIte, sk, seen, walkDepth_succ]
      split
      · change extendAddresses s.1 (readRound dH u s) s.2.2.1 = _
        rw [ext, addrs]
        rfl
      · exact addrs

theorem stateAt_data (dH : ℕ) (u : List Bool) (h : C10Head) (he : enabled h = true) (r : ℕ) :
    let s := stateAt dH u h r
    let s' := stateAt dH u h (r + 1)
    s'.2.2.2.1 = s.2.2.1 ∧ s'.2.2.2.2 = readRound dH u s := by
  let s := stateAt dH u h r
  have hh : s.1 = h := stateAt_head ..
  have en : enabled s.1 = true := by rw [hh]; exact he
  change (advance dH (s, (requests dH s).map (P1Batch.fetch u))).2.2.2.1 = _ ∧
    (advance dH (s, (requests dH s).map (P1Batch.fetch u))).2.2.2.2 = _
  simp only [advance, en, ↓reduceIte]
  exact ⟨rfl, rfl⟩

end P1SolC10P.SolC10prog
