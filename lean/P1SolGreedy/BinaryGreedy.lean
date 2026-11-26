import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Carry.Accum
import OAI.Computability.IntegerMultiplication.Code.Iter

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code

namespace P1SolGreedy.SolDemand

abbrev NumberWord := List Bool

theorem value_bval (x : NumberWord) : Bits.value x = P1Batch.bval x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp only [Bits.value_cons, Bits.digit, P1Batch.bval, ih, Bool.toNat_false, Bool.toNat_true]

@[fun_prop] theorem poly_not : Poly Bool.not := Code.Iter.negate.poly

/-- Numeric comparison permits redundant high zeroes in either word. -/
theorem less_spec (x y : NumberWord) :
    Carry.lt_ (x, y) = decide (P1Batch.bval x < P1Batch.bval y) := by
  rw [Carry.lt_r, value_bval, value_bval]

def numberEq (p : NumberWord × NumberWord) : Bool :=
  bif Carry.lt_ p then false else !Carry.lt_ (p.2, p.1)

@[fun_prop] theorem numberEq_poly : Poly numberEq := by unfold numberEq; fun_prop

theorem numberEq_spec (p : NumberWord × NumberWord) :
    numberEq p = true ↔ P1Batch.bval p.1 = P1Batch.bval p.2 := by
  obtain ⟨x, y⟩ := p
  unfold numberEq
  rw [less_spec, less_spec]
  rcases lt_trichotomy (P1Batch.bval x) (P1Batch.bval y) with h | h | h
  · simp [h, h.ne]
  · simp [h]
  · simp [h, h.ne', h.not_gt]

def minNumber (p : NumberWord × NumberWord) : NumberWord :=
  bif Carry.lt_ p then p.1 else p.2

@[fun_prop] theorem minNumber_poly : Poly minNumber := by unfold minNumber; fun_prop

theorem minNumber_value (x y : NumberWord) :
    P1Batch.bval (minNumber (x, y)) = min (P1Batch.bval x) (P1Batch.bval y) := by
  unfold minNumber
  rw [less_spec]
  by_cases h : P1Batch.bval x < P1Batch.bval y
  · simp only [h, decide_true, Bool.cond_true, min_eq_left h.le]
  · simp only [h, decide_false, Bool.cond_false, min_eq_right (Nat.le_of_not_gt h)]

/-- A binary section offset and width give a field request at a binary index. -/
def fieldWords (p : (NumberWord × NumberWord) × NumberWord) : P1Batch.Req :=
  (Bits.add (p.1.1, Carry.times0 (p.2, p.1.2)), p.1.2)

@[fun_prop] theorem fieldWords_poly : Poly fieldWords := by unfold fieldWords; fun_prop

theorem fieldWords_start (o w i : NumberWord) :
    P1Batch.bval (fieldWords ((o, w), i)).1 =
      P1Batch.bval o + P1Batch.bval i * P1Batch.bval w := by
  change P1Batch.bval (Bits.add (o, Carry.times0 (i, w))) = _
  rw [← value_bval, Bits.add_val, Carry.tm_value, value_bval, value_bval, value_bval]

def hasTrue (l : List Bool) : Bool :=
  Code.Iter.small (([] : List Bool), l.filter id)

@[fun_prop] theorem hasTrue_poly : Poly hasTrue := by
  unfold hasTrue
  have h : Poly (Code.Iter.small (X := Bool) (Y := Bool)) := Code.Iter.small_easy.poly
  exact (by fun_prop : Poly (fun l : List Bool => (([] : List Bool), l.filter id))).compose h

theorem hasTrue_spec (l : List Bool) : hasTrue l = true ↔ true ∈ l := by
  unfold hasTrue Code.Iter.small
  simp only [List.length_nil, decide_eq_true_eq]
  cases h : l.filter id with
  | nil =>
    have hn : true ∉ l := fun hm => by
      have hh : true ∈ l.filter id := List.mem_filter.mpr ⟨hm, rfl⟩
      rw [h] at hh
      exact List.not_mem_nil hh
    simp [hn]
  | cons b bs =>
    have hb : b ∈ l.filter id := by rw [h]; exact List.mem_cons_self
    obtain ⟨hm, ht⟩ := List.mem_filter.mp hb
    have he : b = true := ht
    subst b
    simp [hm]

def hasNumber (p : NumberWord × List NumberWord) : Bool :=
  hasTrue (Code.polyPush numberEq p)

@[fun_prop] theorem hasNumber_poly : Poly hasNumber :=
  (Poly.push ([] : NumberWord) ([] : NumberWord) numberEq_poly).compose hasTrue_poly

theorem hasNumber_spec (w : NumberWord) (l : List NumberWord) :
    hasNumber (w, l) = true ↔ P1Batch.bval w ∈ l.map P1Batch.bval := by
  simp only [hasNumber, hasTrue_spec, Code.polyPush, List.mem_map, numberEq_spec]
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, he.symm⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, he.symm⟩

/-- Check lowest absent number using the public list of candidates. -/
def leastMissingWords (p : NumberWord × (NumberWord × (List NumberWord × List NumberWord))) : Bool :=
  let v := p.1
  let cap := p.2.1
  let forbidden := p.2.2.1
  let candidates := p.2.2.2
  bif Carry.lt_ (v, cap) then
    (bif hasNumber (v, forbidden) then false
      else !hasTrue (Code.polyPush (fun q : (NumberWord × List NumberWord) × NumberWord =>
        bif Carry.lt_ (q.2, q.1.1) then !hasNumber (q.2, q.1.2) else false) ((v, forbidden), candidates)))
  else false

theorem leastMissingWords_poly : Poly leastMissingWords := by
  let misses (q : (NumberWord × List NumberWord) × NumberWord) :=
    bif Carry.lt_ (q.2, q.1.1) then !hasNumber (q.2, q.1.2) else false
  have h : Poly misses := by unfold misses; fun_prop
  have hm : Poly (Code.polyPush misses) := Poly.push ([], []) [] h
  unfold leastMissingWords
  change Poly (fun p : NumberWord × (NumberWord × (List NumberWord × List NumberWord)) =>
    bif Carry.lt_ (p.1, p.2.1) then
      (bif hasNumber (p.1, p.2.2.1) then false
        else !hasTrue (Code.polyPush misses ((p.1, p.2.2.1), p.2.2.2)))
    else false)
  fun_prop

theorem leastMissingWords_spec (v cap : NumberWord) (forbidden candidates : List NumberWord)
    (hc : ∀ k < P1Batch.bval cap, k ∈ candidates.map P1Batch.bval) :
    leastMissingWords (v, cap, forbidden, candidates) = true ↔
      P1Batch.bval v < P1Batch.bval cap ∧
        P1Batch.bval v ∉ forbidden.map P1Batch.bval ∧
        ∀ k < P1Batch.bval v, k ∈ forbidden.map P1Batch.bval := by
  let misses (q : (NumberWord × List NumberWord) × NumberWord) :=
    bif Carry.lt_ (q.2, q.1.1) then !hasNumber (q.2, q.1.2) else false
  have hmiss (w : NumberWord) : misses ((v, forbidden), w) = true ↔
      P1Batch.bval w < P1Batch.bval v ∧ P1Batch.bval w ∉ forbidden.map P1Batch.bval := by
    unfold misses
    dsimp only
    rw [less_spec]
    by_cases h : P1Batch.bval w < P1Batch.bval v
    · simp only [h, decide_true, Bool.cond_true, true_and, Bool.not_eq_true', Bool.eq_false_iff]
      exact not_congr (hasNumber_spec w forbidden)
    · simp [h]
  have hf : hasTrue (Code.polyPush misses ((v, forbidden), candidates)) = false ↔
      ∀ w ∈ candidates, P1Batch.bval w < P1Batch.bval v → P1Batch.bval w ∈ forbidden.map P1Batch.bval := by
    rw [Bool.eq_false_iff]
    change (¬ hasTrue (Code.polyPush misses ((v, forbidden), candidates)) = true) ↔ _
    rw [hasTrue_spec]
    change (true ∉ candidates.map (fun w => misses ((v, forbidden), w))) ↔ _
    constructor
    · intro h w hw hk
      by_contra hn
      exact h (List.mem_map.mpr ⟨w, hw, (hmiss w).mpr ⟨hk, hn⟩⟩)
    · intro h ht
      obtain ⟨w, hw, hm⟩ := List.mem_map.mp ht
      obtain ⟨hk, hn⟩ := (hmiss w).mp hm
      exact hn (h w hw hk)
  unfold leastMissingWords
  change ((bif Carry.lt_ (v, cap) then
    (bif hasNumber (v, forbidden) then false else !hasTrue (Code.polyPush misses ((v, forbidden), candidates)))
    else false) = true) ↔ _
  rw [less_spec]
  by_cases hv : P1Batch.bval v < P1Batch.bval cap
  · by_cases hd : P1Batch.bval v ∈ forbidden.map P1Batch.bval
    · simp only [hv, decide_true, Bool.cond_true, (hasNumber_spec v forbidden).mpr hd,
        Bool.false_eq_true, hd, not_true_eq_false, false_and, true_and]
    · have hd' : hasNumber (v, forbidden) = false :=
        Bool.eq_false_iff.mpr (fun h => hd ((hasNumber_spec v forbidden).mp h))
      simp only [hv, decide_true, Bool.cond_true, hd', Bool.cond_false, Bool.not_eq_true',
        hf, hd, not_false_eq_true, true_and]
      constructor
      · intro h k hk
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (hc k (hk.trans hv))
        exact h w hw hk
      · exact fun h w _ hk => h (P1Batch.bval w) hk
  · simp [hv]

end P1SolGreedy.SolDemand
