import P1ChkFinal.ProgC11
import P1ChkFinal.Ball

namespace P1SolCone.SolCone

open P1Wit P1ChkFinal

/-- A P6 field is identified by its section and its offset within that section. -/
abbrev FieldKey := ℕ × ℕ

abbrev FieldCache := List (FieldKey × ℕ)

def fieldRequests (D : Dims) (fields : List FieldKey) : List P1Batch.Req :=
  fields.map fun k => fieldReq D k.1 k.2

def fieldCache (fields : List FieldKey) (replies : List (List Bool)) : FieldCache :=
  fields.zip (replies.map bitsVal)

def FieldCache.read (cache : FieldCache) (k : FieldKey) : ℕ :=
  ((cache.find? fun p => p.1 == k).map Prod.snd).getD 0

theorem fieldCache_read_on (ks : List FieldKey) (f : FieldKey → List Bool) (k : FieldKey)
    (hk : k ∈ ks) : (fieldCache ks (ks.map f)).read k = bitsVal (f k) := by
  induction ks with
  | nil => exact False.elim (List.not_mem_nil hk)
  | cons a as ih =>
    by_cases h : a = k
    · subst a
      simp only [fieldCache, List.map_cons, List.zip_cons_cons, FieldCache.read,
        List.find?_cons, beq_self_eq_true, Option.map_some, Option.getD_some]
    · have ht := List.mem_cons.mp hk |>.resolve_left (Ne.symm h)
      simp only [fieldCache, List.map_cons, List.zip_cons_cons, FieldCache.read,
        List.find?_cons, show (a == k) = false from beq_eq_false_iff_ne.mpr h]
      exact ih ht

theorem fieldCache_read_mem (D : Dims) (u : List Bool) (fields : List FieldKey) (k : FieldKey)
    (hk : k ∈ fields) :
    (fieldCache fields ((fieldRequests D fields).map (P1Batch.fetch u))).read k =
      readField D u k.1 k.2 := by
  induction fields with
  | nil => exact False.elim (List.not_mem_nil hk)
  | cons a as ih =>
    by_cases h : a = k
    · subst a
      simp only [fieldCache, fieldRequests, List.map_cons, List.zip_cons_cons, FieldCache.read,
        List.find?_cons, beq_self_eq_true, Option.map_some, Option.getD_some,
        readField_eq]
    · have ht := List.mem_cons.mp hk |>.resolve_left (Ne.symm h)
      simp only [fieldCache, fieldRequests, List.map_cons, List.zip_cons_cons, FieldCache.read,
        List.find?_cons, show (a == k) = false from beq_eq_false_iff_ne.mpr h]
      exact ih ht

/-- In the batch result each requested key is paired with its own P6 reader value. -/
theorem fieldCache_eq_map (D : Dims) (u : List Bool) (fields : List FieldKey) :
    fieldCache fields ((fieldRequests D fields).map (P1Batch.fetch u)) =
      fields.map (fun k => (k, readField D u k.1 k.2)) := by
  induction fields with
  | nil => rfl
  | cons k ks ih =>
    change (k, bitsVal (P1Batch.fetch u (fieldReq D k.1 k.2))) ::
      fieldCache ks ((fieldRequests D ks).map (P1Batch.fetch u)) = _
    rw [ih, ← readField_eq]
    rfl

/-- Every cached field equals the witness reader, even when a query is repeated. -/
def FieldCache.Agrees (cache : FieldCache) (D : Dims) (u : List Bool) : Prop :=
  ∀ p ∈ cache, p.2 = readField D u p.1.1 p.1.2

theorem fieldCache_agrees (D : Dims) (u : List Bool) (fields : List FieldKey) :
    (fieldCache fields ((fieldRequests D fields).map (P1Batch.fetch u))).Agrees D u := by
  rw [fieldCache_eq_map]
  intro p hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem FieldCache.append_agrees {D : Dims} {u : List Bool} {a b : FieldCache}
    (ha : a.Agrees D u) (hb : b.Agrees D u) : (a ++ b : FieldCache).Agrees D u := by
  intro p hp
  exact (List.mem_append.mp hp).elim (ha p) (hb p)

theorem FieldCache.read_agrees {D : Dims} {u : List Bool} {a : FieldCache} (h : a.Agrees D u)
    (key : FieldKey) (hk : key ∈ a.map Prod.fst) : a.read key = readField D u key.1 key.2 := by
  induction a with
  | nil => exact False.elim (List.not_mem_nil hk)
  | cons p ps ih =>
    by_cases hp : p.1 = key
    · have he := h p List.mem_cons_self
      simp only [FieldCache.read, List.find?_cons, hp, beq_self_eq_true,
        Option.map_some, Option.getD_some]
      simpa only [hp] using he
    · have not_eq : (p.1 == key) = false := beq_eq_false_iff_ne.mpr hp
      simp only [FieldCache.read, List.find?_cons, not_eq]
      exact ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
        ((List.mem_cons.mp hk).resolve_left (Ne.symm hp))

/-- The panel, widths, and selected-term coordinates for one base at one phase. -/
def baseFields (D : Dims) (ℓ y : ℕ) : List FieldKey :=
  let L := D.lv ℓ
  let slots := List.range L.slots
  let lanes := List.range L.lanes
  let termKeys := List.range L.termKeys
  let arity := List.range (L.termArity + 1)
  (slots.flatMap fun k =>
    ([Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar]).map fun mem =>
      (secLev ℓ mem, y * L.slots + k)) ++
  (lanes.flatMap fun l => slots.map fun k =>
    (secLev ℓ .width, (y * L.lanes + l) * L.slots + k)) ++
  [(secLev ℓ .colour, y), (secLev ℓ .offset, y)] ++
  (termKeys.flatMap fun k => arity.map fun j =>
    (secLev ℓ .terms, (y * L.termKeys + k) * (L.termArity + 1) + j))

theorem baseFields_mem_incidence (D : Dims) (ℓ y k : ℕ) (mem : Mem)
    (hk : k < (D.lv ℓ).slots)
    (hm : mem ∈ [Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar]) :
    (secLev ℓ mem, y * (D.lv ℓ).slots + k) ∈ baseFields D ℓ y := by
  have h : (secLev ℓ mem, y * (D.lv ℓ).slots + k) ∈
      (List.range (D.lv ℓ).slots).flatMap (fun j =>
        [Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar].map fun fld =>
          (secLev ℓ fld, y * (D.lv ℓ).slots + j)) :=
    List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_map.mpr ⟨mem, hm, rfl⟩⟩
  simp only [baseFields, List.mem_append]
  tauto

theorem baseFields_mem_width (D : Dims) (ℓ y l k : ℕ) (hl : l < (D.lv ℓ).lanes) (hk : k < (D.lv ℓ).slots) :
    (secLev ℓ .width, (y * (D.lv ℓ).lanes + l) * (D.lv ℓ).slots + k) ∈ baseFields D ℓ y := by
  have h : (secLev ℓ .width, (y * (D.lv ℓ).lanes + l) * (D.lv ℓ).slots + k) ∈
      (List.range (D.lv ℓ).lanes).flatMap (fun lane => (List.range (D.lv ℓ).slots).map fun slot =>
        (secLev ℓ .width, (y * (D.lv ℓ).lanes + lane) * (D.lv ℓ).slots + slot)) :=
    List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩
  simp only [baseFields, List.mem_append]
  tauto

theorem baseFields_mem_term (D : Dims) (ℓ y k j : ℕ) (hk : k < (D.lv ℓ).termKeys)
    (hj : j < (D.lv ℓ).termArity + 1) :
    (secLev ℓ .terms, (y * (D.lv ℓ).termKeys + k) * ((D.lv ℓ).termArity + 1) + j) ∈ baseFields D ℓ y := by
  unfold baseFields
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

private theorem length_flatMap_uniform {A B : Type} (l : List A) (f : A → List B) (n : ℕ)
    (h : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem baseFields_length (D : Dims) (ℓ y : ℕ) :
    (baseFields D ℓ y).length =
      (D.lv ℓ).slots * 6 + (D.lv ℓ).lanes * (D.lv ℓ).slots + 2 +
        (D.lv ℓ).termKeys * ((D.lv ℓ).termArity + 1) := by
  unfold baseFields
  simp only [List.length_append]
  repeat rw [length_flatMap_uniform _ _ _ (fun _ _ => List.length_map ..)]
  simp only [List.length_range, List.length_cons, List.length_nil]

/-- Every breadth-first expansion depends only on the neighbor lists already cached. -/
theorem bfs_congr_cached {next cached : ℕ → List ℕ} {root rounds : ℕ}
    (h : ∀ r < rounds, ∀ y ∈ bfs next root r, cached y = next y) :
    bfs cached root rounds = bfs next root rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    have eq := ih fun r hr => h r (Nat.lt_succ_of_lt hr)
    simp only [bfs, eq]
    apply congrArg (bfs next root rounds ++ ·)
    apply List.flatMap_congr
    intro y hy
    exact h rounds (Nat.lt_succ_self _) y hy

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.fieldCache_read_mem
#print axioms P1SolCone.SolCone.bfs_congr_cached
