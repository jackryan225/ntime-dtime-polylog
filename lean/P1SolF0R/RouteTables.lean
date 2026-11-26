import P1SolF0R.AccessRows
import P1SolF0R.LaneOrder
import P1Benes.Tab
import P1P5.KWRefresh

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

/-- Widths of the type and lane fields, and the number of lanes. -/
abbrev RouteShape := Tally × Tally × ℕ

def encodeLabel (p : RouteShape × AccessItem) : ℕ :=
  reverseNum (p.1.2.1, p.2.2) + p.1.2.2 * reverseNum (p.1.1, p.2.1)

def decodeLabel (p : RouteShape × ℕ) : AccessItem :=
  (reverseNum (p.1.1, p.2 / p.1.2.2), reverseNum (p.1.2.1, p.2 % p.1.2.2))

attribute [local fun_prop] reverseNum_poly

theorem encodeLabel_poly : Poly encodeLabel := by
  unfold encodeLabel
  fun_prop

theorem decodeLabel_poly : Poly decodeLabel := by
  unfold decodeLabel
  fun_prop

/-- The change of coordinates from typed items to numeric Beneš labels. -/
def itemLabel (t h : ℕ) : (Fin (2 ^ t) × Fin (2 ^ h)) ≃ Fin (2 ^ (t + h)) :=
  (((laneEquiv t).symm.prodCongr (laneEquiv h).symm).trans (addrEquiv t h)).trans
    (bitWordFinEquiv (t + h))

theorem encodeLabel_eq {t h : ℕ} (x : Fin (2 ^ t) × Fin (2 ^ h)) :
    encodeLabel ((tally t, tally h, 2 ^ h), (x.1.val, x.2.val)) = (itemLabel t h x).val := by
  have hty := reverseNum_lane ((laneEquiv t).symm x.1)
  have hla := reverseNum_lane ((laneEquiv h).symm x.2)
  simp only [Equiv.apply_symm_apply] at hty hla
  simp only [encodeLabel, itemLabel, Equiv.trans_apply, Equiv.prodCongr_apply, addrEquiv,
    Equiv.coe_fn_mk, addressNumber, hty, hla, Prod.map]

theorem decodeLabel_eq {t h : ℕ} (x : Fin (2 ^ t) × Fin (2 ^ h)) :
    decodeLabel ((tally t, tally h, 2 ^ h), (itemLabel t h x).val) = (x.1.val, x.2.val) := by
  let u := (laneEquiv t).symm x.1
  let l := (laneEquiv h).symm x.2
  let U := (bitWordFinEquiv t u).val
  let L := (bitWordFinEquiv h l).val
  have hh : L < 2 ^ h := (bitWordFinEquiv h l).isLt
  have hn : (itemLabel t h x).val = L + 2 ^ h * U := addressNumber u l
  have hu : reverseNum (tally t, U) = x.1.val := by
    simpa only [U, u, P1ChkFinal.bwNum, Equiv.apply_symm_apply] using reverseNum_request u
  have hl : reverseNum (tally h, L) = x.2.val := by
    simpa only [L, l, P1ChkFinal.bwNum, Equiv.apply_symm_apply] using reverseNum_request l
  unfold decodeLabel
  simp only [Prod.fst, Prod.snd, hn, Nat.add_mul_div_left _ _ (Nat.two_pow_pos h),
    Nat.div_eq_of_lt hh, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh, hu, hl]

abbrev ContentInput := (Tally × List ℕ) × ℕ

private def contentShape (p : ContentInput) : RouteShape :=
  (tally 3, p.1.1, p.1.2.length)

private theorem contentShape_poly : Poly contentShape := by
  unfold contentShape
  fun_prop

private def contentInputItem (p : ContentInput) : AccessItem :=
  decodeLabel (contentShape p, p.2)

private theorem contentInputItem_poly : Poly contentInputItem :=
  (contentShape_poly.pair Easy.snd.poly).compose decodeLabel_poly

private def contentOutputItem (p : ContentInput) : AccessItem :=
  accessRow (p.1.2, contentInputItem p)

private theorem contentOutputItem_poly : Poly contentOutputItem :=
  ((show Poly (fun p : ContentInput => p.1.2) from by fun_prop).pair
    contentInputItem_poly).compose accessRow_poly

/-- Compute one content row in label order from the lane bit width and the locally read centers. -/
def contentAt (p : ContentInput) : ℕ :=
  encodeLabel (contentShape p, contentOutputItem p)

theorem contentAt_poly : Poly contentAt :=
  (contentShape_poly.pair contentOutputItem_poly).compose encodeLabel_poly

theorem contentAt_def (p : ContentInput) :
    contentAt p =
      let s : RouteShape := (tally 3, p.1.1, p.1.2.length)
      encodeLabel (s, accessRow (p.1.2, decodeLabel (s, p.2))) :=
  rfl

/-- The row function for the state path in network lane coordinates. -/
def stateRow (p : ℕ × AccessItem) : AccessItem :=
  bif decide (p.2.1 = 0) then
    bif decide (p.2.2 = 0) then (1, p.2.2) else p.2
  else bif decide (p.2.2 + 1 < p.1) then (1, p.2.2 + 1) else (0, 0)

theorem stateRow_poly : Poly stateRow := by
  unfold stateRow
  fun_prop

theorem stateRow_eq {h : ℕ} (x : Fin 2 × Fin (2 ^ h)) :
    stateRow (2 ^ h, (x.1.val, x.2.val)) = ((stNext x).1.val, (stNext x).2.val) := by
  rcases x with ⟨t, l⟩
  have ht : t = 0 ↔ t.val = 0 := Fin.ext_iff
  by_cases h0 : t.val = 0
  · by_cases hl : l.val = 0 <;> simp [stateRow, stNext, h0, ht, hl]
  · by_cases hl : l.val + 1 < 2 ^ h <;> simp [stateRow, stNext, h0, ht, hl]

def stateAt (p : (Tally × Tally) × ℕ) : ℕ :=
  let s : RouteShape := (tally 1, p.1.1, p.1.2.length)
  encodeLabel (s, stateRow (p.1.2.length, decodeLabel (s, p.2)))

theorem stateAt_poly : Poly stateAt := by
  have hlen : Poly (fun p : (Tally × Tally) × ℕ => p.1.2.length) := by fun_prop
  have hshape : Poly (fun p : (Tally × Tally) × ℕ => (tally 1, p.1.1, p.1.2.length)) := by fun_prop
  have hdec := (hshape.pair Easy.snd.poly).compose decodeLabel_poly
  exact (hshape.pair ((hlen.pair hdec).compose stateRow_poly)).compose encodeLabel_poly

/-- Use a unary clock to specify the number of rows. -/
def forwardRows {A : Type} (row : A × ℕ → ℕ) (p : A × Tally) : List ℕ :=
  (List.range p.2.length).map fun j => row (p.1, j)

theorem forwardRows_poly {A : Type} [Codec A] (a : A) {row : A × ℕ → ℕ}
    (h : Poly row) : Poly (forwardRows row) :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose range_length_poly)).compose (Poly.push a 0 h)

theorem forwardRows_eq {A : Type} (row : A × ℕ → ℕ) (a : A) (clock : Tally) {N : ℕ}
    (hN : clock.length = N) (π : Equiv.Perm (Fin N))
    (h : ∀ j : Fin N, row (a, j.val) = (π j).val) :
    forwardRows row (a, clock) = P1Benes.Tab.tabOf π := by
  apply List.ext_getElem
  · simp only [forwardRows, List.length_map, List.length_range, hN, P1Benes.Tab.tabOf_length]
  · intro i hi hj
    simp only [forwardRows, List.getElem_map, List.getElem_range, P1Benes.Tab.tabOf, List.getElem_ofFn]
    exact h ⟨i, by simpa only [P1Benes.Tab.tabOf_length] using hj⟩

def inverseAt (p : List ℕ × ℕ) : ℕ :=
  (firstMatch (fun z : (List ℕ × ℕ) × ℕ => decide (readAt 0 z.1.1 z.2 = z.1.2))
    (p, List.range p.1.length)).elim 0 id

theorem inverseAt_poly : Poly inverseAt := by
  have ht : Poly (fun z : (List ℕ × ℕ) × ℕ => decide (readAt 0 z.1.1 z.2 = z.1.2)) := by fun_prop
  have hr := (show Poly (fun p : List ℕ × ℕ => p.1) from by fun_prop).compose range_length_poly
  exact poly_defaultOption 0 ((Poly.identity.pair hr).compose (firstMatch_poly ([], 0) 0 ht))

theorem inverseAt_eq {N : ℕ} (π : Equiv.Perm (Fin N)) (l : Fin N) :
    inverseAt (P1Benes.Tab.tabOf π, l.val) = (π.symm l).val := by
  unfold inverseAt firstMatch
  simp only [P1Benes.Tab.tabOf_length]
  have ha (i : Fin N) : readAt 0 (P1Benes.Tab.tabOf π) i.val = (π i).val :=
    readAt_ofFn _ _ _
  have hf : (List.range N).find? (fun j => decide (readAt 0 (P1Benes.Tab.tabOf π) j = l.val)) =
      some (π.symm l).val := by
    apply range_find_eq_some.mpr
    refine ⟨(π.symm l).isLt, ?_, ?_⟩
    · rw [ha, Equiv.apply_symm_apply]
      exact decide_eq_true rfl
    · intro j hj
      let i : Fin N := ⟨j, hj.trans (π.symm l).isLt⟩
      change decide (readAt 0 (P1Benes.Tab.tabOf π) i.val = l.val) = false
      rw [ha]
      apply decide_eq_false
      intro he
      have h' : π i = l := Fin.ext he
      have h'' : i = π.symm l := by rw [← h', Equiv.symm_apply_apply]
      exact (Nat.ne_of_lt hj) (congrArg Fin.val h'')
  rw [hf]
  rfl

def inverseRows (xs : List ℕ) : List ℕ :=
  (List.range xs.length).map fun j => inverseAt (xs, j)

theorem inverseRows_poly : Poly inverseRows := poly_mapWith range_length_poly inverseAt_poly

theorem inverseRows_eq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    inverseRows (P1Benes.Tab.tabOf π) = P1Benes.Tab.tabOf π.symm := by
  apply List.ext_getElem
  · simp only [inverseRows, List.length_map, List.length_range, P1Benes.Tab.tabOf_length]
  · intro i hi hj
    simp only [inverseRows, List.getElem_map, List.getElem_range, P1Benes.Tab.tabOf, List.getElem_ofFn]
    exact inverseAt_eq π ⟨i, by simpa only [P1Benes.Tab.tabOf_length] using hj⟩

/-- Bound the unary row encoding by the number of rows even on arbitrary lists. -/
def tallyRows (xs : List ℕ) : List Tally := xs.map fun i => tally (min i xs.length)

theorem tallyRows_poly : Poly tallyRows := by
  have h : Poly (fun p : List ℕ × ℕ => tally (min p.2 p.1.length)) :=
    P1ProgEng.SolKWR.poly_tallyMin Easy.snd.poly (poly_lengthNat Easy.fst.poly)
      ((Dom.base _).mono fun p => by
        have h := duration p.1
        simp only [size_prod]
        omega)
  exact poly_mapWith Poly.identity h

theorem tallyRows_eq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    tallyRows (P1Benes.Tab.tabOf π) = (P1Benes.Tab.tabOf π).map tally := by
  unfold tallyRows
  apply List.map_congr_left
  intro i hi
  rw [P1Benes.Tab.tabOf_length]
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hi
  rw [min_eq_left (π l).isLt.le]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.decodeLabel_eq
#print axioms P1SolF0R.SolReader.inverseRows_eq
