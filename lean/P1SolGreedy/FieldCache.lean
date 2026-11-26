import P1SolGreedy.GreedyReaders

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev FieldCache := List (P1Batch.Req × NumberWord)

def cacheFields (p : List P1Batch.Req × List NumberWord) : FieldCache :=
  Code.zipFair ([], []) [] p

@[fun_prop] theorem cacheFields_poly : Poly cacheFields := (Code.easy_zip _ _).poly

/-- Attach each batch result to the request as it was before clipping. -/
theorem cacheFields_fetch (u : List Bool) (len : NumberWord) (hl : P1Batch.bval len = u.length)
    (qs : List P1Batch.Req) :
    cacheFields (qs, (clipRequests (len, qs)).map (P1Batch.fetch u)) =
      qs.map (fun q => (q, P1Batch.fetch u q)) := by
  rw [clipRequests_fetch _ _ hl]
  have h := Code.fair (id : P1Batch.Req → P1Batch.Req) (P1Batch.fetch u) qs ([], []) []
  simpa only [cacheFields, List.map_id, id_eq] using h

def matchField (p : P1Batch.Req × (P1Batch.Req × NumberWord)) : List NumberWord :=
  bif numberEq (p.1.1, p.2.1.1) then
    (bif numberEq (p.1.2, p.2.1.2) then [p.2.2] else [])
  else []

@[fun_prop] theorem matchField_poly : Poly matchField := by unfold matchField; fun_prop

theorem mem_matchField (q r : P1Batch.Req) (w v : NumberWord) :
    v ∈ matchField (q, r, w) ↔ requestNumbers q = requestNumbers r ∧ v = w := by
  have h₁ := numberEq_spec (q.1, r.1)
  have h₂ := numberEq_spec (q.2, r.2)
  unfold matchField
  dsimp only at *
  cases e₁ : numberEq (q.1, r.1) <;> cases e₂ : numberEq (q.2, r.2) <;>
    simp only [e₁, e₂, Bool.cond_false, Bool.cond_true, List.not_mem_nil, List.mem_singleton,
      requestNumbers, Prod.mk.injEq] at h₁ h₂ ⊢
  · have hn₁ : P1Batch.bval q.1 ≠ P1Batch.bval r.1 := fun x => Bool.false_ne_true (h₁.mpr x)
    simp [hn₁]
  · have hn₁ : P1Batch.bval q.1 ≠ P1Batch.bval r.1 := fun x => Bool.false_ne_true (h₁.mpr x)
    simp [hn₁]
  · have hn₂ : P1Batch.bval q.2 ≠ P1Batch.bval r.2 := fun x => Bool.false_ne_true (h₂.mpr x)
    simp [hn₂]
  · simp [h₁.mp trivial, h₂.mp trivial]

def matchingFields (p : P1Batch.Req × FieldCache) : List NumberWord :=
  (Code.polyPush matchField p).flatten

theorem matchingFields_poly : Poly matchingFields :=
  (Poly.push ([], []) (([], []), []) matchField_poly).compose Easy.flatten.poly

def cacheRead (p : FieldCache × P1Batch.Req) : NumberWord :=
  (matchingFields (p.2, p.1)).headD []

@[fun_prop] theorem cacheRead_poly : Poly cacheRead :=
  (Easy.exchange.poly.compose matchingFields_poly).compose (Code.Iter.leader []).poly

theorem mem_matchingFields (q : P1Batch.Req) (c : FieldCache) (v : NumberWord) :
    v ∈ matchingFields (q, c) ↔ ∃ r, (r, v) ∈ c ∧ requestNumbers q = requestNumbers r := by
  simp only [matchingFields, Code.polyPush, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨_, ⟨⟨r, w⟩, hr, rfl⟩, hv⟩
    obtain ⟨he, rfl⟩ := (mem_matchField q r w v).mp hv
    exact ⟨r, hr, he⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨_, ⟨(r, v), hr, rfl⟩, (mem_matchField q r v v).mpr ⟨he, rfl⟩⟩

/-- Request words with the same numeric fields select the same cache entry. -/
theorem cacheRead_congr (c : FieldCache) (q r : P1Batch.Req) (h : requestNumbers q = requestNumbers r) :
    cacheRead (c, q) = cacheRead (c, r) := by
  have h₁ : P1Batch.bval q.1 = P1Batch.bval r.1 := congrArg Prod.fst h
  have h₂ : P1Batch.bval q.2 = P1Batch.bval r.2 := congrArg Prod.snd h
  have he (a b w : NumberWord) : matchField (q, (a, b), w) = matchField (r, (a, b), w) := by
    have ha : numberEq (q.1, a) = numberEq (r.1, a) := by
      rw [Bool.eq_iff_iff, numberEq_spec, numberEq_spec]
      change (P1Batch.bval q.1 = _) ↔ (P1Batch.bval r.1 = _)
      rw [h₁]
    have hb : numberEq (q.2, b) = numberEq (r.2, b) := by
      rw [Bool.eq_iff_iff, numberEq_spec, numberEq_spec]
      change (P1Batch.bval q.2 = _) ↔ (P1Batch.bval r.2 = _)
      rw [h₂]
    change (bif numberEq (q.1, a) then (bif numberEq (q.2, b) then [w] else []) else []) =
      (bif numberEq (r.1, a) then (bif numberEq (r.2, b) then [w] else []) else [])
    rw [ha, hb]
  have hm : c.map (fun x => matchField (q, x)) = c.map (fun x => matchField (r, x)) := by
    apply List.map_congr_left
    rintro ⟨⟨a, b⟩, w⟩ _
    exact he a b w
  unfold cacheRead matchingFields Code.polyPush
  rw [hm]

theorem cacheRead_fetch (u : List Bool) (qs : List P1Batch.Req) (q : P1Batch.Req)
    (hq : ∃ r ∈ qs, requestNumbers q = requestNumbers r) :
    cacheRead (qs.map (fun r => (r, P1Batch.fetch u r)), q) = P1Batch.fetch u q := by
  let c := qs.map (fun r => (r, P1Batch.fetch u r))
  have hm (v : NumberWord) (hv : v ∈ matchingFields (q, c)) : v = P1Batch.fetch u q := by
    obtain ⟨r, hr, he⟩ := (mem_matchingFields q c v).mp hv
    obtain ⟨s, _, hp⟩ := List.mem_map.mp hr
    have hsr : s = r := congrArg Prod.fst hp
    subst s
    have hv' : P1Batch.fetch u r = v := congrArg Prod.snd hp
    exact hv'.symm.trans (fetch_of_requestNumbers u he.symm)
  obtain ⟨r, hr, he⟩ := hq
  have hmem : P1Batch.fetch u r ∈ matchingFields (q, c) :=
    (mem_matchingFields _ _ _).mpr ⟨r, List.mem_map_of_mem hr, he⟩
  change (matchingFields (q, c)).headD [] = _
  cases hs : matchingFields (q, c) with
  | nil =>
    rw [hs] at hmem
    exact (List.not_mem_nil hmem).elim
  | cons v vs =>
    exact hm v (hs.symm ▸ List.mem_cons_self)

theorem cacheRead_field (D : Dims) (u : List Bool) (ℓ : ℕ) (k : Mem)
    (qs : List P1Batch.Req) (i : NumberWord) (hq : fieldWords (rowSection k (levelRow D ℓ), i) ∈ qs) :
    P1Batch.bval (cacheRead (qs.map (fun q => (q, P1Batch.fetch u q)),
      fieldWords (rowSection k (levelRow D ℓ), i))) =
      readField D u (secLev ℓ k) (P1Batch.bval i) := by
  rw [cacheRead_fetch _ _ _ ⟨_, hq, rfl⟩, fetch_of_requestNumbers _ (requestNumbers_rowField D ℓ k i),
    bval_bitsVal, ← readField_eq]

/-- Cartesian products with a polynomial construction on encoded lists. -/
@[fun_prop] theorem product_poly {A B : Type} [Codec A] [Codec B] (a : A) (b : B) :
    Poly (fun p : List A × List B => p.1.product p.2) := by
  let row (p : List B × A) := Code.polyPush (id : A × B → A × B) (p.2, p.1)
  have hr : Poly row := by
    exact Easy.exchange.poly.compose (Poly.push a b Poly.identity)
  have h := ((Easy.exchange (X := List A) (Y := List B)).poly.compose
    (Poly.push ([] : List B) a hr)).compose Easy.flatten.poly
  change Poly (fun p : List A × List B => p.1.flatMap (fun x => p.2.map (fun y => (x,y))))
  simpa only [row, Code.polyPush, List.flatMap_def, id_eq, Prod.swap] using h

end P1SolGreedy.SolDemand
