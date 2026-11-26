import P1SolC10P.Format

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def tabN {A : Type} (t : Tally) (n : ℕ) (f : ℕ → A) : List A :=
  (rangeIn t n).map f

@[fun_prop] theorem poly_tabN {X A : Type} [Codec X] [Inhabited X] [Codec A]
    {t : X → Tally} {n : X → ℕ} {f : X × ℕ → A}
    (ht : Poly t) (hn : Poly n) (hf : Poly f) :
    Poly (fun x => tabN (t x) (n x) (fun i => f (x, i))) :=
  poly_mapWith (poly_rangeIn ht hn) hf

theorem tabN_ofFn {A : Type} {t : Tally} {n : ℕ} (ht : n ≤ t.length) (f : ℕ → A) :
    tabN t n f = List.ofFn (fun i : Fin n => f i.val) := by
  rw [tabN, range_cap ht]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intros
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

def reqOf (k : FieldKey) : P1Batch.Req := (binary k.1, binary k.2)

@[fun_prop] theorem poly_reqOf : Poly reqOf := by unfold reqOf; fun_prop

theorem bval_fetch_reqOf (u : List Bool) (k : FieldKey) :
    P1Batch.bval (P1Batch.fetch u (reqOf k)) = fieldAt u k := by
  simp only [P1Batch.fetch, reqOf, bval_binary, fieldAt]

abbrev FetchTable := List (FieldKey × ℕ)

/-- Tabulate by the request list. For malformed batches, absent words are treated as empty. -/
def makeTable (p : List FieldKey × Words) : FetchTable :=
  List.ofFn fun i : Fin p.1.length =>
    (readAt (0, 0) p.1 i.val, P1Batch.bval (readAt [] p.2 i.val))

theorem poly_makeTable : Poly makeTable := by
  have h := poly_tabLike (l := Prod.fst)
    (f := fun z : (List FieldKey × Words) × ℕ =>
      (readAt (0, 0) z.1.1 z.2, P1Batch.bval (readAt [] z.1.2 z.2)))
    Easy.fst.poly (by fun_prop)
  exact h

theorem makeTable_fetch (ks : List FieldKey) (u : List Bool) :
    makeTable (ks, (ks.map reqOf).map (P1Batch.fetch u)) =
      ks.map (fun k => (k, fieldAt u k)) := by
  apply List.ext_getElem
  · simp only [makeTable, List.length_ofFn, List.length_map]
  · intro i hi hj
    have hk : i < ks.length := by simpa only [List.length_map] using hj
    simp only [makeTable, List.getElem_ofFn, readAt, List.getElem?_map,
      List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, List.getElem_map, bval_fetch_reqOf]

def matchesKey (q k : FieldKey) : Bool := decide (q.1 = k.1) && decide (q.2 = k.2)

theorem matchesKey_true (q k : FieldKey) : matchesKey q k = true ↔ q = k := by
  simp only [matchesKey, Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff]

@[fun_prop] theorem poly_matchesKey {X : Type} [Codec X] {f g : X → FieldKey}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => matchesKey (f x) (g x)) := by
  unfold matchesKey
  fun_prop

def fieldProbe (p : FieldKey × (FieldKey × ℕ)) : List ℕ :=
  if matchesKey p.1 p.2.1 then [p.2.2] else []

@[fun_prop] theorem poly_fieldProbe : Poly fieldProbe := by
  unfold fieldProbe
  fun_prop

def tableRead (xs : FetchTable) (k : FieldKey) : ℕ :=
  readAt 0 ((xs.map (fun p => fieldProbe (k, p))).flatten) 0

theorem poly_tableRead_pair : Poly (fun p : FetchTable × FieldKey => tableRead p.1 p.2) := by
  unfold tableRead
  have hm : Poly (fun p : FieldKey × FetchTable => p.2.map (fun v => fieldProbe (p.1, v))) :=
    Code.Poly.push (0, 0) ((0, 0), 0) poly_fieldProbe
  have hs : Poly (fun p : FetchTable × FieldKey => p.1.map (fun v => fieldProbe (p.2, v))) :=
    Easy.exchange.poly.compose hm
  exact poly_readAt 0 (poly_flatten hs) (poly_const 0)

@[fun_prop] theorem poly_tableRead {X : Type} [Codec X] {xs : X → FetchTable} {k : X → FieldKey}
    (hx : Poly xs) (hk : Poly k) : Poly (fun x => tableRead (xs x) (k x)) :=
  (hx.pair hk).compose poly_tableRead_pair

theorem tableRead_map (f : FieldKey → ℕ) {k : FieldKey} {ks : List FieldKey} (hk : k ∈ ks) :
    tableRead (ks.map (fun p => (p, f p))) k = f k := by
  induction ks with
  | nil => cases hk
  | cons a ks ih =>
    by_cases e : k = a
    · subst a
      simp only [tableRead, List.map_cons, List.flatten_cons, fieldProbe, (matchesKey_true k k).mpr rfl,
        ↓reduceIte, List.singleton_append, readAt]
      rfl
    · have hne : matchesKey k a ≠ true := fun h => e ((matchesKey_true k a).mp h)
      simp only [tableRead, List.map_cons, List.flatten_cons, fieldProbe, hne, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      simpa only [tableRead, fieldProbe] using ih ((List.mem_cons.mp hk).resolve_left e)

theorem tableRead_fetch (u : List Bool) {ks : List FieldKey} {k : FieldKey} (hk : k ∈ ks) :
    tableRead (makeTable (ks, (ks.map reqOf).map (P1Batch.fetch u))) k = fieldAt u k := by
  rw [makeTable_fetch, tableRead_map _ hk]

theorem total_map_reqOf_le (ks : List FieldKey) (w : ℕ)
    (hw : ∀ k ∈ ks, k.2 ≤ w) :
    P1Batch.total (ks.map reqOf) ≤ ks.length * w := by
  induction ks with
  | nil => simp [P1Batch.total]
  | cons k ks ih =>
    have h1 := hw k List.mem_cons_self
    have h2 := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
    simp only [P1Batch.total, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_mul, Nat.one_mul, reqOf, bval_binary] at *
    omega

theorem size_fetch_le (u : List Bool) (qs : List P1Batch.Req) :
    size (qs.map (P1Batch.fetch u)) ≤ 2 * (qs.length + P1Batch.total qs) + 1 := by
  induction qs with
  | nil => simp only [List.map_nil, size_nil, List.length_nil, P1Batch.total, List.sum_nil, Nat.add_zero, Nat.mul_zero, le_refl]
  | cons q qs ih =>
    have h : (P1Batch.fetch u q).length ≤ P1Batch.bval q.2 := by
      unfold P1Batch.fetch
      exact List.length_take_le ..
    simp only [List.map_cons, List.length_cons, P1Batch.total, List.sum_cons,
      Code.size_cons, P1ChkFinal.size_listBool] at *
    omega

theorem fieldKey_width_le (next : Bool) (m : P1Wit.Mem) (h : C10Head) (i : ℕ) :
    (fieldKey next m h i).2 ≤ h.1.length := min_le_left _ _

theorem fieldKey_address_le (next : Bool) (m : P1Wit.Mem) (h : C10Head) (i : ℕ) :
    (fieldKey next m h i).1 ≤ h.2.1 := min_le_left _ _

end P1SolC10P.SolC10prog
