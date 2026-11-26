import P1SolCone.Wof
import P1SolCone.FieldCache

namespace P1SolCone.SolCone

open P1Wit P1ChkFinal

abbrev ArcCode := ℕ × ℕ × ℕ
abbrev Span := ℕ × ℕ

/-- Compute the payload interval from the base prefix and the row's preceding widths. -/
def arcSpan (D : Dims) (u : List Bool) (a : ArcCode) : Span :=
  let L := D.lv D.top
  let j := a.2.1 * L.slots + a.2.2
  (D.fixedLen + rdOmega D u a.1 + pre (arcW D u a.1) j,
    rdWidth D u D.top a.1 a.2.1 a.2.2)

def arcValid (L : LevelDims) (a : ArcCode) : Bool :=
  decide (a.1 < L.bases ∧ a.2.1 < L.lanes ∧ a.2.2 < L.slots)

def spanValid (m : ℕ) (s : Span) : Bool := decide (s.1 + s.2 ≤ m)

def spanRequest (s : Span) : P1Batch.Req := (bin s.1, bin s.2)

/-- The requests for outgoing and incoming arcs of a final site, before payload bounds checks. -/
def terminalArcCodes (D : Dims) (u : List Bool) (v : ℕ) : List ArcCode × List ArcCode :=
  let L := D.lv D.top
  let p := v / L.lanes
  let lane := v % L.lanes
  let slots := List.range L.slots
  (slots.map (fun k => (p, lane, k)), slots.map fun k =>
    (rdInAddr D u D.top p k, lane ^^^ rdInDisp D u D.top p k, rdInFar D u D.top p k))

/-- Check the incoming displacement independently of the translated source lane. -/
def terminalDispValid (D : Dims) (u : List Bool) (v : ℕ) : Bool :=
  let L := D.lv D.top
  (List.range L.slots).all (fun k =>
    decide (rdInDisp D u D.top (v / L.lanes) k < L.lanes))

/-- A pure specification of the final payload batch. A failing guard gives no request list. -/
def terminalSpans (D : Dims) (u : List Bool) (cap v : ℕ) :
    Option (List Span × List Span) :=
  let L := D.lv D.top
  let arcs := terminalArcCodes D u v
  let spans := (arcs.1.map (arcSpan D u), arcs.2.map (arcSpan D u))
  if v < L.bases * L.lanes ∧ terminalDispValid D u v = true ∧
      (arcs.1 ++ arcs.2).all (arcValid L) = true ∧
      (spans.1 ++ spans.2).all (fun s => spanValid u.length s && decide (s.2 ≤ cap)) = true
    then some spans else none

private theorem option_mapM_as_map {A B : Type} (xs : List A) (f : A → B) (g : A → Option B)
    (h : ∀ a ∈ xs, g a = some (f a)) :
    (xs.mapM g) = some (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.map_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem readArc_span (D : Dims) (u : List Bool) (a : ArcCode) :
    readArc D u a.1 a.2.1 a.2.2 =
      (bif arcValid (D.lv D.top) a && spanValid u.length (arcSpan D u a) then
        some (P1Batch.fetch u (spanRequest (arcSpan D u a))) else none) := by
  rcases a with ⟨y,l,k⟩
  unfold readArc arcValid spanValid arcSpan spanRequest
  simp only [P1Batch.fetch, bval_bin]
  split <;> simp only [*, decide_true, Bool.true_and, decide_false, Bool.false_and, Bool.cond_false]
  split <;> simp [*]

theorem terminalHalfWidths (D : Dims) (u : List Bool) (v : ℕ) :
    readHalfWidths D u D.top (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes) =
      (((terminalArcCodes D u v).1.map (arcSpan D u)).map Prod.snd,
       ((terminalArcCodes D u v).2.map (arcSpan D u)).map Prod.snd) := by
  simp only [readHalfWidths, terminalArcCodes, List.map_map, Function.comp_def, arcSpan]

private theorem all_append_of_fields {A : Type} (xs ys : List A) (p : A → Bool) :
    (xs ++ ys).all p = true ↔ xs.all p = true ∧ ys.all p = true := by
  simp only [List.all_append, Bool.and_eq_true]

/-- A successful span list gives exactly the payload words at its requests in the same slot order. -/
theorem terminalSpans_sound (D : Dims) (u : List Bool) (cap v : ℕ) (s : List Span × List Span)
    (h : terminalSpans D u cap v = some s) :
    readFinalHalf D u v = some (s.1.map (P1Batch.fetch u ∘ spanRequest),
      s.2.map (P1Batch.fetch u ∘ spanRequest)) ∧
    widthsWithin cap (readHalfWidths D u D.top (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)) = true := by
  unfold terminalSpans at h
  dsimp only at h
  split at h
  next hgood =>
    obtain ⟨hv, hd, hvalid, hspan⟩ := hgood
    injection h with eq
    subst s
    let arcs := terminalArcCodes D u v
    let spans := (arcs.1.map (arcSpan D u), arcs.2.map (arcSpan D u))
    have valid (a : ArcCode) (ha : a ∈ arcs.1 ++ arcs.2) :
        (arcValid (D.lv D.top) a && spanValid u.length (arcSpan D u a)) = true := by
      have ha' : arcSpan D u a ∈ spans.1 ++ spans.2 := by
        rw [← List.map_append]
        exact List.mem_map_of_mem ha
      have hs := List.all_eq_true.mp hspan _ ha'
      simp only [Bool.and_eq_true] at hs ⊢
      exact ⟨List.all_eq_true.mp hvalid a ha, hs.1⟩
    have hread (a : ArcCode) (ha : a ∈ arcs.1 ++ arcs.2) :
        readArc D u a.1 a.2.1 a.2.2 = some (P1Batch.fetch u (spanRequest (arcSpan D u a))) := by
      rw [readArc_span, valid a ha]
      rfl
    constructor
    · have hdisp (k : ℕ) (hk : k ∈ List.range (D.lv D.top).slots) :
          rdInDisp D u D.top (v / (D.lv D.top).lanes) k < (D.lv D.top).lanes :=
        of_decide_eq_true (List.all_eq_true.mp hd k hk)
      unfold readFinalHalf
      rw [ite_eq_left hv]
      dsimp only
      have hout : (List.range (D.lv D.top).slots).mapM
          (readArc D u (v / (D.lv D.top).lanes) (v % (D.lv D.top).lanes)) =
          some (spans.1.map (P1Batch.fetch u ∘ spanRequest)) := by
        simp only [spans, arcs, terminalArcCodes, List.map_map, Function.comp_def]
        apply option_mapM_as_map
        intro k hk
        exact hread _ (List.mem_append_left _ (List.mem_map_of_mem hk))
      have hin : (List.range (D.lv D.top).slots).mapM
          (fun k => if rdInDisp D u D.top (v / (D.lv D.top).lanes) k < (D.lv D.top).lanes then
            readArc D u (rdInAddr D u D.top (v / (D.lv D.top).lanes) k)
              (v % (D.lv D.top).lanes ^^^ rdInDisp D u D.top (v / (D.lv D.top).lanes) k)
              (rdInFar D u D.top (v / (D.lv D.top).lanes) k) else none) =
          some (spans.2.map (P1Batch.fetch u ∘ spanRequest)) := by
        simp only [spans, arcs, terminalArcCodes, List.map_map, Function.comp_def]
        apply option_mapM_as_map
        intro k hk
        rw [ite_eq_left (hdisp k hk)]
        exact hread _ (List.mem_append_right _ (List.mem_map_of_mem hk))
      rw [hout, hin]
      rfl
    · rw [terminalHalfWidths]
      simp only [widthsWithin, Bool.and_eq_true, List.all_map, Function.comp_def]
      obtain ⟨ho, hi⟩ := (all_append_of_fields _ _ _).mp hspan
      constructor
      · apply List.all_eq_true.mpr
        intro z hz
        have hs := List.all_eq_true.mp ho (arcSpan D u z) (List.mem_map_of_mem hz)
        simp only [Bool.and_eq_true] at hs
        exact hs.2
      · apply List.all_eq_true.mpr
        intro z hz
        have hs := List.all_eq_true.mp hi (arcSpan D u z) (List.mem_map_of_mem hz)
        simp only [Bool.and_eq_true] at hs
        exact hs.2
  next => contradiction

theorem option_mapM_isSome {A B : Type} (xs : List A) (f : A → Option B) :
    (xs.mapM f).isSome = xs.all (fun q => (f q).isSome) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons, List.all_cons, ← ih]
    cases hf : f a <;> cases ht : as.mapM f <;> rfl

private theorem readArc_valid_of_some (D : Dims) (u : List Bool) (a : ArcCode)
    (h : (readArc D u a.1 a.2.1 a.2.2).isSome = true) :
    arcValid (D.lv D.top) a = true ∧ spanValid u.length (arcSpan D u a) = true := by
  rw [readArc_span] at h
  by_cases he : (arcValid (D.lv D.top) a && spanValid u.length (arcSpan D u a)) = true
  · simpa only [Bool.and_eq_true] using he
  · rw [Bool.eq_false_iff.mpr he] at h
    exact False.elim (Bool.false_ne_true h)

/-- Any defined terminal half below the width cap supplies precisely the requested spans. -/
theorem terminalSpans_complete (D : Dims) (u : List Bool) (cap v : ℕ)
    (hread : (readFinalHalf D u v).isSome = true)
    (hw : widthsWithin cap (readHalfWidths D u D.top
      (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)) = true) :
    (terminalSpans D u cap v).isSome = true := by
  let L := D.lv D.top
  let y := v / L.lanes
  let l := v % L.lanes
  let slots := List.range L.slots
  let fo := fun k => readArc D u y l k
  let fi := fun k => if rdInDisp D u D.top y k < L.lanes then
      readArc D u (rdInAddr D u D.top y k) (l ^^^ rdInDisp D u D.top y k) (rdInFar D u D.top y k)
    else none
  have hv : v < L.bases * L.lanes := by
    by_contra h
    unfold readFinalHalf at hread
    dsimp only at hread
    rw [ite_eq_right h] at hread
    contradiction
  have validRead : (slots.mapM fo).isSome = true ∧ (slots.mapM fi).isSome = true := by
    change ((if v < L.bases * L.lanes then
      (do let o ← slots.mapM fo; let i ← slots.mapM fi; pure (o,i)) else none) :
      Option (List (List Bool) × List (List Bool))).isSome = true at hread
    rw [ite_eq_left hv] at hread
    cases ho : slots.mapM fo <;> cases hi : slots.mapM fi
    all_goals try rw [ho] at hread
    all_goals try rw [hi] at hread
    all_goals first | exact ⟨rfl, rfl⟩ | exact False.elim (Bool.false_ne_true hread)
  simp only [option_mapM_isSome, List.all_eq_true] at validRead
  have hd (k : ℕ) (hk : k ∈ slots) : rdInDisp D u D.top y k < L.lanes := by
    have h := validRead.2 k hk
    unfold fi at h
    split at h
    · assumption
    · contradiction
  let as := terminalArcCodes D u v
  let spans := (as.1.map (arcSpan D u), as.2.map (arcSpan D u))
  have perArc (p : ArcCode) (hp : p ∈ as.1 ++ as.2) :
      arcValid L p = true ∧ spanValid u.length (arcSpan D u p) = true := by
    rcases List.mem_append.mp hp with ho | hi
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ho
      exact readArc_valid_of_some D u (y,l,k) (validRead.1 k hk)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      have hh := validRead.2 k hk
      dsimp only [fi] at hh
      rw [ite_eq_left (hd k hk)] at hh
      exact readArc_valid_of_some D u
        (rdInAddr D u D.top y k, l ^^^ rdInDisp D u D.top y k, rdInFar D u D.top y k) hh
  have disp : terminalDispValid D u v = true :=
    List.all_eq_true.mpr fun k hk => decide_eq_true (hd k hk)
  have width : ∀ s ∈ spans.1 ++ spans.2, s.2 ≤ cap := by
    rw [terminalHalfWidths] at hw
    simp only [widthsWithin, Bool.and_eq_true] at hw
    intro span hs
    rcases List.mem_append.mp hs with hs | hs
    · exact of_decide_eq_true (List.all_eq_true.mp hw.1 _ (List.mem_map_of_mem hs))
    · exact of_decide_eq_true (List.all_eq_true.mp hw.2 _ (List.mem_map_of_mem hs))
  have allSpan : (spans.1 ++ spans.2).all (fun span => spanValid u.length span && decide (span.2 ≤ cap)) = true := by
    apply List.all_eq_true.mpr
    intro span hs
    have hs' : span ∈ (as.1 ++ as.2).map (arcSpan D u) := by rw [List.map_append]; exact hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs'
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(perArc p hp).2, width _ hs⟩
  unfold terminalSpans
  change (if v < L.bases * L.lanes ∧ terminalDispValid D u v = true ∧
    (as.1 ++ as.2).all (arcValid L) = true ∧ _ then some spans else none).isSome = true
  rw [ite_eq_left ⟨hv, disp, List.all_eq_true.mpr (fun p hp => (perArc p hp).1), allSpan⟩]
  rfl

end P1SolCone.SolCone
