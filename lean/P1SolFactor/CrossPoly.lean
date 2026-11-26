import P1SolFactor.OwnerTargets
import P1SolFactor.CrossTablesPoly

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code

namespace P1SolFactor.SolCross

open P1SolFactor.SolPolyWords
open P1Benes.Tab

abbrev Query := Tally × (Tables × (Tally × Tally))

def encodeQuery (n : ℕ) (P Q : List ℕ) (k a : ℕ) : Query :=
  (tally n, (encodeTables P Q, (tally k, tally a)))

def inner (p : Query) : Bool :=
  !(eqT (p.1, [])) && !(eqT (p.2.2.1, [])) && lessT (p.2.2.1, doubleT p.1)

private theorem andB_poly : Poly (fun p : Bool × Bool => p.1 && p.2) := (Easy.finite _).poly
attribute [local fun_prop] andB_poly
private theorem notB_poly : Poly (fun p : Bool => !p) := Iter.negate.poly
attribute [local fun_prop] notB_poly

@[fun_prop] theorem inner_poly : Poly inner := by unfold inner; fun_prop

def descend (p : Query) : Query :=
  (decT p.1, (child (p.2.1, oddT p.2.2.2), (decT p.2.2.1, halfT p.2.2.2)))

@[fun_prop] theorem descend_poly : Poly descend := by unfold descend; fun_prop

def crossStep (p : Query) : Query := bif inner p then descend p else p

private theorem crossStep_poly : Poly crossStep := by unfold crossStep; fun_prop

def finish (p : Query) : Bool :=
  let k := p.2.2.1
  let a := halfT p.2.2.2
  let tables := p.2.1
  bif eqT (p.1, []) then eqT (k, []) && oddT (Iter.pick [] (tables.1, []))
  else bif eqT (k, []) then first (tables, a)
  else bif eqT (k, doubleT p.1) then last (tables, a)
  else false

private theorem finish_poly : Poly finish := by unfold finish; fun_prop

private def tableWithin (M : ℕ) (t : List Tally) : Prop :=
  t.length ≤ M ∧ ∀ x ∈ t, size x ≤ M

private def queryWithin (M : ℕ) (p : Query) : Prop :=
  size p.1 ≤ M ∧ tableWithin M p.2.1.1 ∧ tableWithin M p.2.1.2 ∧
    size p.2.2.1 ≤ M ∧ size p.2.2.2 ≤ M

private theorem tableWithin_of_size (M : ℕ) (t : List Tally) (h : size t ≤ M) :
    tableWithin M t := ⟨(duration t).le.trans h, fun _ hx => (size_bel hx).le.trans h⟩

private theorem queryWithin_self (p : Query) : queryWithin (size p) p := by
  unfold queryWithin
  refine ⟨?_, tableWithin_of_size _ _ ?_, tableWithin_of_size _ _ ?_, ?_, ?_⟩
  all_goals simp only [size_prod]; omega

private theorem tableWithin_size (M : ℕ) (t : List Tally) (h : tableWithin M t) :
    size t ≤ 1 + M * (M + 1) := by
  suffices hb : size t ≤ 1 + t.length * (M + 1) from
    hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.1) _)
  induction t with
  | nil => simp only [size_nil, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons x t ih =>
    have hx := h.2 x List.mem_cons_self
    have ht : tableWithin M t := ⟨(Nat.le_succ _).trans h.1,
      fun y hy => h.2 y (List.mem_cons_of_mem _ hy)⟩
    have hb := ih ht
    simp only [size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem queryWithin_size (M : ℕ) (p : Query) (h : queryWithin M p) :
    size p ≤ 6 * (M + 1) ^ 2 := by
  obtain ⟨hn, hp, hq, hk, ha⟩ := h
  have hp' := tableWithin_size M p.2.1.1 hp
  have hq' := tableWithin_size M p.2.1.2 hq
  simp only [size_prod]
  nlinarith

private theorem half_size (x : Tally) : size (halfT x) ≤ size x := by
  rw [size_tally, size_tally]
  simp only [halfT, Carry.half_v, tally_length]
  have h := Nat.div_le_self x.length 2
  omega

private theorem dec_size (x : Tally) : size (decT x) ≤ size x := by
  rw [size_tally, size_tally]
  simp [decT, cutLists]

private theorem size_pick_of_within (M : ℕ) (t : List Tally) (j : Tally)
    (ht : tableWithin M t) (hm : 1 ≤ M) :
    size (Iter.pick [] (t, j)) ≤ M := by
  rw [← recover_tally j, pick_getD]
  rw [List.getD_eq_getElem?_getD]
  cases hj : t[j.length]? with
  | none => simpa only [Option.getD_none, size_nil] using hm
  | some x =>
    exact ht.2 x (List.mem_of_getElem? hj)

private theorem childTable_within (M : ℕ) (t : Tables) (dir b : Bool)
    (h : tableWithin M t.1) (h' : tableWithin M t.2) (hm : 1 ≤ M) :
    tableWithin M (childTable (t, (dir, b))) := by
  constructor
  · simp only [childTable, polyPush, List.length_map, Iter.sizeup, halfT, Carry.half_v,
      tally_length, ruler_length]
    exact (Nat.div_le_self _ _).trans h.1
  · intro x hx
    simp only [childTable, polyPush, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    apply (half_size _).trans
    apply size_pick_of_within M _ _ _ hm
    cases dir <;> assumption

private theorem crossStep_within (M : ℕ) (p : Query) (h : queryWithin M p) :
    queryWithin M (crossStep p) := by
  unfold crossStep
  cases e : inner p
  · exact h
  obtain ⟨hn, hp, hq, hk, ha⟩ := h
  have hm := (size_pos p.1).trans_le hn
  exact ⟨(dec_size _).trans hn, childTable_within _ _ _ _ hp hq hm,
    childTable_within _ _ _ _ hp hq hm, (dec_size _).trans hk, (half_size _).trans ha⟩

private theorem rideWithin (l : Tally) (p : Query) (M : ℕ) (hs : queryWithin M p) :
    queryWithin M (ride crossStep (l, p)) := by
  induction l generalizing p with
  | nil => exact hs
  | cons _ l ih => exact ih (crossStep p) (crossStep_within M p hs)

private theorem ride_cross_poly : Poly (ride crossStep) := by
  apply Code.Poly.fold_left (f := fun p : Query × Unit => crossStep p.1)
    (Easy.fst.poly.compose crossStep_poly) 6 2
  rintro ⟨fuel, p⟩ l _
  change size (ride crossStep (l, p)) ≤ 6 * (size (fuel, p) + 1)^2
  apply (queryWithin_size _ _ (rideWithin l p (size p) (queryWithin_self p))).trans
  have hs : size p ≤ size (fuel, p) := by
    change size p ≤ size fuel + size p + 1
    omega
  gcongr

def queryBit (p : Query) : Bool := finish (ride crossStep (p.1, p))

theorem queryBit_poly : Poly queryBit :=
  ((Easy.fst.poly.pair Code.Poly.identity).compose ride_cross_poly).compose finish_poly

private theorem inner_encode (n : ℕ) (P Q : List ℕ) (k a : ℕ) :
    inner (encodeQuery (n + 1) P Q k a) = (!decide (k = 0) && decide (k ≤ 2 * n + 1)) := by
  unfold inner encodeQuery
  change (!(eqT (tally (n + 1), tally 0)) && !(eqT (tally k, tally 0)) &&
    lessT (tally k, doubleT (tally (n + 1)))) = _
  have h : k < 2 * (n + 1) ↔ k ≤ 2 * n + 1 := by omega
  simp only [eqT_tally, doubleT_tally, lessT_tally, Nat.succ_ne_zero, decide_false,
    Bool.not_false, Bool.true_and, h]

private theorem descend_encode (n : ℕ) (P Q : List ℕ) (k a : ℕ) :
    descend (encodeQuery (n + 1) P Q k a) =
      encodeQuery n (subT P Q (decide (a % 2 = 1))) (subInvT P Q (decide (a % 2 = 1)))
        (k - 1) (a / 2) := by
  simp only [descend, encodeQuery, decT_tally, Nat.add_sub_cancel, oddT_tally,
    halfT_tally, child_encode]

private theorem finish_leaf (P Q : List ℕ) (k a : ℕ) :
    finish (encodeQuery 0 P Q k a) = crossT 0 P Q k a := by
  unfold finish encodeQuery crossT
  simp only [eqT, tally_length, List.length_nil, decide_true, Bool.cond_true]
  change (decide (k = 0) && oddT (Iter.pick [] (P.map tally, tally 0))) = _
  rw [pick_tally, oddT_tally]

private theorem finish_node (n : ℕ) (P Q : List ℕ) (k a : ℕ) :
    finish (encodeQuery (n + 1) P Q k a) =
      if k = 0 then firstT P Q (a / 2)
      else if k = 2 * n + 2 then lastT P Q (a / 2) else false := by
  unfold finish encodeQuery
  change (bif eqT (tally (n + 1), tally 0) then _ else
    bif eqT (tally k, tally 0) then _ else
    bif eqT (tally k, doubleT (tally (n + 1))) then _ else false) = _
  rw [show 2 * n + 2 = 2 * (n + 1) by omega]
  simp only [eqT_tally, Nat.succ_ne_zero, decide_false, Bool.cond_false,
    doubleT_tally, halfT_tally, first_encode, last_encode, Bool.cond_decide]

private theorem iterate_fixed (p : Query) (h : inner p = false) (n : ℕ) :
    crossStep^[n] p = p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, crossStep, h, Bool.cond_false, ih]

private theorem cross_iterate (n : ℕ) (P Q : List ℕ) (k a : ℕ) :
    finish (crossStep^[n] (encodeQuery n P Q k a)) = crossT n P Q k a := by
  induction n generalizing P Q k a with
  | zero => exact finish_leaf P Q k a
  | succ n ih =>
    rw [crossT]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, iterate_fixed _ (by simp only [inner_encode, hk, decide_true, Bool.not_true,
        Bool.false_and]), finish_node, ite_eq_left hk]
    rw [ite_eq_right hk]
    by_cases hi : k ≤ 2 * n + 1
    · rw [ite_eq_left hi, Function.iterate_succ_apply]
      rw [show crossStep (encodeQuery (n + 1) P Q k a) = descend (encodeQuery (n + 1) P Q k a) by
        simp only [crossStep, inner_encode, hk, hi, decide_false, decide_true, Bool.not_false,
          Bool.true_and, Bool.cond_true]]
      rw [descend_encode]
      exact ih _ _ _ _
    · rw [ite_eq_right hi, iterate_fixed _ (by simp only [inner_encode, hi, decide_false,
        Bool.and_false]), finish_node, ite_eq_right hk]

theorem queryBit_encode (n : ℕ) (P Q : List ℕ) (k a : ℕ) :
    queryBit (encodeQuery n P Q k a) = crossT n P Q k a := by
  unfold queryBit
  rw [ride_t]
  simpa only [encodeQuery, tally_length] using cross_iterate n P Q k a

end P1SolFactor.SolCross

theorem P1SolFactor.crossPoly : P1SolFactor.Owner.CrossPoly := by
  let rearrange (p : (Tally × P1SolFactor.SolCross.Tables) × (Tally × Tally)) :
      P1SolFactor.SolCross.Query := (p.1.1, (p.1.2, p.2))
  have h : Poly rearrange := by unfold rearrange; fun_prop
  exact ⟨fun p => P1SolFactor.SolCross.queryBit (rearrange p),
    h.compose P1SolFactor.SolCross.queryBit_poly,
    fun n π κ a => P1SolFactor.SolCross.queryBit_encode n
      (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a⟩

#print axioms P1SolFactor.crossPoly
