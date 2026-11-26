import P1SolF0R.Find
import P1SolF0R.LocalBeta
import P1ChkFinal.C10RcPoly
import P1SolC10P.Primitives

namespace P1SolF0R.SolReader

open P1Net P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open scoped P1ChkFinal.AstraC10

abbrev AccessItem := ℕ × ℕ

/-- The block coordinate of a port or a window, relative to the first owned block. -/
def accessBlock (centers : List ℕ) (x : AccessItem) : ℕ :=
  if x.1 < 3 then x.1 * centers.length + x.2
  else readAt 0 centers x.2 - 1 + (x.1 - 3)

/-- A port scans the whole interval. A window scans the lanes strictly after its own. -/
def accessTest (p : (List ℕ × (Bool × ℕ × ℕ)) × ℕ) : Bool :=
  let c := readAt 0 p.1.1 p.2
  let z := p.1.2.2.2
  (p.1.2.1 || decide (p.1.2.2.1 < p.2)) && (decide (c ≤ z + 1) && decide (z ≤ c + 1))

def accessFind (centers : List ℕ) (port : Bool) (j z : ℕ) : Option ℕ :=
  firstMatch accessTest ((centers, port, j, z), List.range centers.length)

/-- A row of the content access permutation in network lane coordinates. -/
def accessRow (p : List ℕ × AccessItem) : AccessItem :=
  let t := p.2.1
  let j := p.2.2
  let z := accessBlock p.1 p.2
  if t < 6 then
    match accessFind p.1 (decide (t < 3)) j z with
    | some l => (3 + (z + 1 - readAt 0 p.1 l), l)
    | none => if t < 3 then p.2 else (z / p.1.length, z % p.1.length)
  else p.2

private theorem find_range_spec {N : ℕ} (test : ℕ → Bool) (x : Option (Fin N))
    (hs : ∀ i, x = some i → test i.val = true ∧ ∀ j < i.val, test j = false)
    (hn : x = none → ∀ j < N, test j = false) :
    (List.range N).find? test = x.map Fin.val := by
  cases hx : x with
  | none =>
    simp only [Option.map_none, List.find?_eq_none, List.mem_range]
    intro j hj
    simp only [hn hx j hj, Bool.false_eq_true, not_false_eq_true]
  | some i =>
    obtain ⟨h, hm⟩ := hs i hx
    exact range_find_eq_some.mpr ⟨i.isLt, h, hm⟩

section Correct

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

private def origin : ℤ := (bigQ I σ k ι - 1) * (2 ^ h : ℕ)

/-- The centers reconstructed from the genuine start and move records. -/
def trueCenters : List ℕ :=
  List.ofFn fun j : Fin (2 ^ h) =>
    center (2 ^ h) ((betaOf σ k (ι.val * 2 ^ h)) % (2 ^ h : ℕ)).toNat
      (intervalMoves σ ι k) j.val

theorem length_trueCenters : (trueCenters σ ι k).length = 2 ^ h := List.length_ofFn

private theorem readTrueCenter (j : Fin (2 ^ h)) :
    ((readAt 0 (trueCenters σ ι k) j.val : ℕ) : ℤ) =
      laneBeta I σ ι k j.val - origin σ ι k := by
  simp only [trueCenters, readAt_ofFn, origin, center_eq]

private theorem readTrueCenter_pos (j : Fin (2 ^ h)) : 0 < readAt 0 (trueCenters σ ι k) j.val := by
  simp only [trueCenters, readAt_ofFn, center]
  have hj := j.isLt
  omega

private theorem accessBlock_eq (t : Fin 8) (j : Fin (2 ^ h)) :
    (accessBlock (trueCenters σ ι k) (t.val, j.val) : ℤ) =
      itemBlock I σ ι k t j - origin σ ι k := by
  by_cases ht : t.val < 3
  · simp only [accessBlock, ht, ite_true, length_trueCenters, itemBlock, portBlock, origin]
    push_cast
    ring
  · simp only [accessBlock, ht, ite_false, itemBlock]
    have hc := readTrueCenter_pos σ ι k j
    rw [Nat.cast_add, Int.ofNat_sub (show 1 ≤ _ from hc), readTrueCenter]
    ring

private theorem accessTest_eq (z : ℕ) (Z : ℤ) (hz : (z : ℤ) = Z - origin σ ι k)
    (port : Bool) (j l : Fin (2 ^ h)) :
    accessTest ((trueCenters σ ι k, port, j.val, z), l.val) = true ↔
      (port = true ∨ j < l) ∧ P1Net.Acc I σ ι k l Z := by
  have hl := readTrueCenter σ ι k l
  simp only [accessTest, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Fin.lt_def,
    P1Net.Acc, InWindow]
  constructor
  · rintro ⟨hp, hlow, hhigh⟩
    exact ⟨hp, by omega, by omega⟩
  · rintro ⟨hp, hlow, hhigh⟩
    exact ⟨hp, by omega, by omega⟩

private theorem accessFind_port (z : ℕ) (Z : ℤ) (hz : (z : ℤ) = Z - origin σ ι k)
    (j : Fin (2 ^ h)) :
    accessFind (trueCenters σ ι k) true j.val z = (firstAcc I σ ι k Z).map Fin.val := by
  unfold accessFind firstMatch
  simp only [length_trueCenters]
  apply find_range_spec
  · intro l hl
    obtain ⟨ha, hm⟩ := firstAcc_spec hl
    refine ⟨(accessTest_eq σ ι k z Z hz true j l).2 ⟨Or.inl rfl, ha⟩, ?_⟩
    intro u hu
    have hlt : u < 2 ^ h := hu.trans l.isLt
    let v : Fin (2 ^ h) := ⟨u, hlt⟩
    apply Bool.eq_false_iff.mpr
    intro hv
    have hv' := ((accessTest_eq σ ι k z Z hz true j v).1 hv).2
    exact (Nat.not_le_of_lt hu) (hm v hv')
  · intro hx u hu
    apply Bool.eq_false_iff.mpr
    intro hv
    exact firstAcc_none hx ⟨u, hu⟩ ((accessTest_eq σ ι k z Z hz true j ⟨u, hu⟩).1 hv).2

private theorem accessFind_window (z : ℕ) (Z : ℤ) (hz : (z : ℤ) = Z - origin σ ι k)
    (j : Fin (2 ^ h)) :
    accessFind (trueCenters σ ι k) false j.val z = (nextAcc I σ ι k Z j).map Fin.val := by
  unfold accessFind firstMatch
  simp only [length_trueCenters]
  apply find_range_spec
  · intro l hl
    obtain ⟨hj, ha, hm⟩ := nextAcc_spec hl
    refine ⟨(accessTest_eq σ ι k z Z hz false j l).2 ⟨Or.inr hj, ha⟩, ?_⟩
    intro u hu
    let v : Fin (2 ^ h) := ⟨u, hu.trans l.isLt⟩
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨hv', hv''⟩ := (accessTest_eq σ ι k z Z hz false j v).1 hv
    exact (Nat.not_le_of_lt hu) (hm v (hv'.resolve_left Bool.false_ne_true) hv'')
  · intro hx u hu
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨hv', hv''⟩ := (accessTest_eq σ ι k z Z hz false j ⟨u, hu⟩).1 hv
    exact nextAcc_none hx ⟨u, hu⟩ (hv'.resolve_left Bool.false_ne_true) hv''

private theorem accessDst_window (z : ℕ) (Z : ℤ) (hz : (z : ℤ) = Z - origin σ ι k)
    (l : Fin (2 ^ h)) (ha : P1Net.Acc I σ ι k l Z) :
    3 + (z + 1 - readAt 0 (trueCenters σ ι k) l.val) = (typ (3 + slotAt I σ ι k l Z)).val := by
  have hs := slotAt_lt I σ ι k ha
  rw [typ_val (by omega)]
  congr 1
  have hc := readTrueCenter σ ι k l
  have hl := ha.1
  change laneBeta I σ ι k l - 1 ≤ Z at hl
  unfold slotAt
  omega

private theorem accessDst_port (z : ℕ) (Z : ℤ) (hz : (z : ℤ) = Z - origin σ ι k)
    (j : Fin (2 ^ h)) (ha : P1Net.Acc I σ ι k j Z) :
    (z / 2 ^ h, z % 2 ^ h) = ((typ (portType I σ ι k Z)).val, (portLane h Z).val) := by
  obtain ⟨hl, hr⟩ := window_in_owned I σ ι k j ha
  obtain ⟨ht, hb⟩ := portBlock_of_owned I σ ι k hl hr
  have hcast : (z : ℤ) = ((portType I σ ι k Z * 2 ^ h + (portLane h Z).val : ℕ) : ℤ) := by
    simp only [portBlock] at hb
    unfold origin at hz
    push_cast at hz ⊢
    linarith
  have he : z = portType I σ ι k Z * 2 ^ h + (portLane h Z).val := by exact_mod_cast hcast
  rw [typ_val (by omega), he, Nat.mul_comm (portType I σ ι k Z) (2 ^ h),
    Nat.add_comm _ (portLane h Z).val, Nat.add_mul_div_left _ _ (Nat.two_pow_pos h), Nat.div_eq_of_lt (portLane h Z).isLt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (portLane h Z).isLt]

theorem accessRow_eq (x : Fin 8 × Fin (2 ^ h)) :
    accessRow (trueCenters σ ι k, (x.1.val, x.2.val)) =
      ((accNext I σ ι k x).1.val, (accNext I σ ι k x).2.val) := by
  obtain ⟨t, j⟩ := x
  let z := accessBlock (trueCenters σ ι k) (t.val, j.val)
  let Z := itemBlock I σ ι k t j
  have hz : (z : ℤ) = Z - origin σ ι k := accessBlock_eq σ ι k t j
  change (if t.val < 6 then
      match accessFind (trueCenters σ ι k) (decide (t.val < 3)) j.val z with
      | some l => (3 + (z + 1 - readAt 0 (trueCenters σ ι k) l), l)
      | none => if t.val < 3 then (t.val, j.val) else
          (z / (trueCenters σ ι k).length, z % (trueCenters σ ι k).length)
    else (t.val, j.val)) = _
  by_cases h3 : t.val < 3
  · have h6 : t.val < 6 := by omega
    rw [if_pos h6, decide_eq_true h3, accessFind_port σ ι k z Z hz j]
    cases hf : firstAcc I σ ι k Z with
    | none => simp only [Option.map_none, h3, ite_true, accNext, ← show Z = itemBlock I σ ι k t j from rfl, hf]
    | some l =>
      simp only [Option.map_some, h3, ite_true, accNext, ← show Z = itemBlock I σ ι k t j from rfl, hf]
      exact Prod.ext (accessDst_window σ ι k z Z hz l (firstAcc_spec hf).1) rfl
  · by_cases h6 : t.val < 6
    · rw [if_pos h6, decide_eq_false h3, accessFind_window σ ι k z Z hz j]
      cases hf : nextAcc I σ ι k Z j with
      | none =>
        simp only [Option.map_none, h3, ite_false, length_trueCenters, accNext, h6, ite_true,
          ← show Z = itemBlock I σ ι k t j from rfl, hf]
        have ha : P1Net.Acc I σ ι k j Z := by
          unfold Z itemBlock
          rw [if_neg h3]
          exact acc_slot I σ ι k j _ (by omega)
        exact accessDst_port σ ι k z Z hz j ha
      | some l =>
        simp only [Option.map_some, h3, h6, ite_false, ite_true, accNext,
          ← show Z = itemBlock I σ ι k t j from rfl, hf]
        exact Prod.ext (accessDst_window σ ι k z Z hz l (nextAcc_spec hf).2.1) rfl
    · simp only [h6, ite_false, h3, accNext]

end Correct

section Program

variable {X : Type} [Codec X]

theorem range_length_poly {A : Type} [Codec A] :
    Poly (fun l : List A => List.range l.length) := by
  have hp := poly_tabLike (l := (id : List A → List A))
    (f := fun p : List A × ℕ => p.2) Poly.identity Easy.snd.poly
  convert hp using 1
  funext l
  apply List.ext_getElem
  · simp only [List.length_range, tabLike, id_eq, List.length_ofFn]
  · intros
    simp only [List.getElem_range, tabLike, List.getElem_ofFn]

@[local fun_prop] theorem poly_nat_le {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun p => decide (f p ≤ g p)) := by
  simpa only [Nat.lt_succ_iff] using
    poly_lt hf (poly_addNat hg (poly_const 1))

theorem accessTest_poly : Poly accessTest := by
  unfold accessTest
  fun_prop

abbrev AccessSearch := List ℕ × (Bool × ℕ × ℕ)

theorem accessFind_poly :
    Poly (fun p : AccessSearch => accessFind p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Poly (fun p : AccessSearch => List.range p.1.length) :=
    Easy.fst.poly.compose range_length_poly
  exact (Poly.identity.pair hr).compose
    (firstMatch_poly (default : AccessSearch) (0 : ℕ) accessTest_poly)

theorem accessBlock_poly :
    Poly (fun p : List ℕ × AccessItem => accessBlock p.1 p.2) := by
  have ht : Poly (fun p : List ℕ × AccessItem => decide (p.2.1 < 3)) := by fun_prop
  have hp : Poly (fun p : List ℕ × AccessItem => p.2.1 * p.1.length + p.2.2) := by fun_prop
  have hw : Poly (fun p : List ℕ × AccessItem => readAt 0 p.1 p.2.2 - 1 + (p.2.1 - 3)) := by
    fun_prop
  simpa only [accessBlock, Bool.cond_eq_ite, decide_eq_true_eq] using ht.choose hp hw

@[local fun_prop] theorem poly_succ : Poly Nat.succ :=
  poly_addNat Poly.identity (poly_const 1)

abbrev AccessAnswer := (List ℕ × AccessItem × ℕ) × Option ℕ

theorem accessRow_poly : Poly accessRow := by
  let z (p : List ℕ × AccessItem) := accessBlock p.1 p.2
  have hz : Poly z := accessBlock_poly
  have hfind : Poly (fun p : List ℕ × AccessItem => accessFind p.1 (decide (p.2.1 < 3)) p.2.2 (z p)) :=
    (show Poly (fun p : List ℕ × AccessItem => (p.1, decide (p.2.1 < 3), p.2.2, z p)) from
      by fun_prop).compose accessFind_poly
  let data (p : List ℕ × AccessItem) := ((p.1, p.2, z p), accessFind p.1 (decide (p.2.1 < 3)) p.2.2 (z p))
  have hd : Poly data := (show Poly (fun p : List ℕ × AccessItem => (p.1, p.2, z p)) from
    by fun_prop).pair hfind
  let finishRow (p : AccessAnswer) :=
    let l := p.2.elim 0 id
    bif decide (p.1.2.1.1 < 6) then
      bif p.2.isSome then (3 + (p.1.2.2 + 1 - readAt 0 p.1.1 l), l)
      else bif decide (p.1.2.1.1 < 3) then p.1.2.1
      else (p.1.2.2 / p.1.1.length, p.1.2.2 % p.1.1.length)
    else p.1.2.1
  have hf : Poly finishRow := by
    have hs : Poly (fun p : AccessAnswer => p.2.isSome) := by
      have he : Easy (fun o : Option ℕ => o.elim false (fun _ => true)) :=
        OAI.Computability.NearSquareRoot.PhaseTable.easyOption false _ (Easy.const true)
      have hb : Poly (fun o : Option ℕ => o.isSome) := by
        convert he.poly using 1
        funext o
        cases o <;> rfl
      exact Easy.snd.poly.compose hb
    have hc : Poly (fun p : AccessAnswer => p.1.1) := by fun_prop
    have hi : Poly (fun p : AccessAnswer => p.1.2.1) := by fun_prop
    have ht : Poly (fun p : AccessAnswer => p.1.2.1.1) := by fun_prop
    have hz' : Poly (fun p : AccessAnswer => p.1.2.2) := by fun_prop
    have hl : Poly (fun p : AccessAnswer => p.2.elim 0 id) :=
      poly_defaultOption 0 Easy.snd.poly
    have ha := poly_readAt 0 hc hl
    have h0 := poly_addNat (poly_const 3) (poly_subNat (poly_addNat hz' (poly_const 1)) ha)
    have h1 := (poly_divNat hz' (poly_lengthNat hc)).pair (poly_modNat hz' (poly_lengthNat hc))
    exact (poly_lt ht (poly_const 6)).choose
      (hs.choose (h0.pair hl) ((poly_lt ht (poly_const 3)).choose hi h1)) hi
  convert hd.compose hf using 1
  funext p
  unfold finishRow data accessRow
  dsimp only [z]
  by_cases h6 : p.2.1 < 6
  · by_cases h3 : p.2.1 < 3 <;>
      cases accessFind p.1 (decide (p.2.1 < 3)) p.2.2 (accessBlock p.1 p.2) <;>
      simp only [h6, h3, decide_true, decide_false, Bool.cond_true, Bool.cond_false,
        ite_true, ite_false, Option.isSome_some, Option.isSome_none, Option.elim_some, id_eq]
  · simp only [h6, decide_false, Bool.cond_false, ite_false]

end Program

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.accessRow_eq
