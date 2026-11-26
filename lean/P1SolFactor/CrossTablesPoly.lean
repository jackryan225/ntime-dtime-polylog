import P1SolFactor.PolyWords
import P1Benes.Tab

namespace P1SolFactor.SolCross

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1SolFactor.SolPolyWords
open P1Benes.Tab

abbrev Tables := List Tally × List Tally

def encodeTables (P Q : List ℕ) : Tables := (P.map tally, Q.map tally)

@[simp] theorem flipLow_tally (n : ℕ) : flipLow (tally n) = tally (flipT n) := by
  unfold flipLow flipT
  rw [oddT_tally]
  by_cases h : n % 2 = 1 <;> simp [h]

def rho (p : Tables × Tally) : Tally :=
  Iter.pick [] (p.1.2, flipLow (Iter.pick [] (p.1.1, flipLow p.2)))

@[fun_prop] theorem rho_poly : Poly rho := by unfold rho; fun_prop

@[simp] theorem rho_encode (P Q : List ℕ) (x : ℕ) :
    rho (encodeTables P Q, tally x) = tally (rhoT P Q x) := by
  simp only [rho, encodeTables, rhoT, flipLow_tally, pick_tally]

def orbitStep (p : Tables × (Tally × Tally)) : Tables × (Tally × Tally) :=
  let next := rho (p.1, p.2.1)
  (p.1, (next, minT (p.2.2, next)))

private theorem orbitStep_poly : Poly orbitStep := by unfold orbitStep; fun_prop

private theorem orbitStep_size (p : Tables × (Tally × Tally)) :
    size (orbitStep p) ≤ size p + size p.1 + 1 := by
  have hn := Iter.search_size p.1.2 ([] : Tally) (flipLow (Iter.pick [] (p.1.1, flipLow p.2.1)))
  change size (rho (p.1, p.2.1)) ≤ size p.1.2 + 1 at hn
  have hm (x y : Tally) : size (minT (x, y)) ≤ size x := by
    rw [size_tally, size_tally]
    unfold minT lessT Iter.small
    by_cases h : x.length < y.length <;> simp [h]
    all_goals omega
  have h := hm p.2.2 (rho (p.1, p.2.1))
  simp only [orbitStep, size_prod] at h ⊢
  omega

def orbitMin (p : Tables × Tally) : Tally :=
  (ride orbitStep (ruler p.1.1, (p.1, (p.2, p.2)))).2.2

private theorem fold_orbit_bound (l : Tally) (P : Tables) (x m : Tally) :
    size (ride orbitStep (l, (P, (x, m)))) ≤
      size (P, (x, m)) + l.length * (size P + 1) := by
  induction l generalizing x m with
  | nil => simp [ride]
  | cons _ l ih =>
    change size (ride orbitStep (l, (P, (rho (P, x), minT (m, rho (P, x)))))) ≤ _
    have h := ih (rho (P, x)) (minT (m, rho (P, x)))
    have hs := orbitStep_size (P, (x, m))
    change size (P, (rho (P, x), minT (m, rho (P, x)))) ≤ _ at hs
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    dsimp only at hs
    omega

private theorem orbitRide_poly : Poly (ride orbitStep) := by
  apply Code.Poly.fold_left (f := fun p : (Tables × (Tally × Tally)) × Unit => orbitStep p.1)
    (Easy.fst.poly.compose orbitStep_poly) 2 2
  rintro ⟨s, P, x, m⟩ l hl
  have hn : l.length ≤ s.length := hl.length_le
  have hd := duration s
  have h := fold_orbit_bound l P x m
  let B := size s + size (P, (x, m)) + 2
  change size (ride orbitStep (l, (P, (x, m)))) ≤ 2 * B ^ 2
  apply h.trans
  have hp : size P ≤ size (P, (x, m)) := by
    change size P ≤ size P + size (x, m) + 1
    omega
  have hb : l.length * (size P + 1) ≤ B ^ 2 := by
    have h1 : l.length ≤ B := by unfold B; omega
    have h2 : size P + 1 ≤ B := by unfold B; omega
    rw [pow_two]
    exact Nat.mul_le_mul h1 h2
  have hb' : size (P, (x, m)) ≤ B ^ 2 := by
    have h1 : size (P, (x, m)) ≤ B := by unfold B; omega
    have h2 : 1 ≤ B := by unfold B; omega
    rw [pow_two]
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  omega

@[fun_prop] theorem orbitMin_poly : Poly orbitMin := by
  unfold orbitMin
  have h : Poly (fun p : Tables × Tally => (ruler p.1.1, (p.1, (p.2, p.2)))) := by fun_prop
  exact (h.compose orbitRide_poly).sndCompose.sndCompose

private theorem orbit_iterate (P Q : List ℕ) (steps x m : ℕ) (hm : m ≤ x) :
    ((orbitStep^[steps]) (encodeTables P Q, (tally x, tally m))).2.2 =
      tally (min m (iterMin (rhoT P Q) steps x)) := by
  induction steps generalizing x m with
  | zero => simp only [Function.iterate_zero_apply, iterMin, min_eq_left hm]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [orbitStep, rho_encode, minT_tally]
    rw [ih _ _ (min_le_right _ _)]
    have ht : iterMin (rhoT P Q) k (rhoT P Q x) ≤ rhoT P Q x :=
      iterMin_le _ _ _ 0 (Nat.zero_le _)
    simp only [iterMin]
    congr 1
    calc
      min (min m (rhoT P Q x)) (iterMin (rhoT P Q) k (rhoT P Q x)) =
          min m (iterMin (rhoT P Q) k (rhoT P Q x)) := by
        rw [min_assoc, min_eq_right ht]
      _ = min m (min x (iterMin (rhoT P Q) k (rhoT P Q x))) := by
        rw [← min_assoc, min_eq_left hm]

@[simp] theorem orbitMin_encode (P Q : List ℕ) (x : ℕ) :
    orbitMin (encodeTables P Q, tally x) = tally (iterMin (rhoT P Q) P.length x) := by
  unfold orbitMin
  rw [ride_t]
  simp only [encodeTables, ruler_length, List.length_map]
  change ((orbitStep^[P.length]) (encodeTables P Q, (tally x, tally x))).2.2 = _
  rw [orbit_iterate P Q P.length x x le_rfl]
  congr 1
  exact min_eq_right (iterMin_le _ _ _ 0 (Nat.zero_le _))

def colour (p : Tables × Tally) : Bool :=
  lessT (orbitMin (p.1, flipLow p.2), orbitMin p)

def first (p : Tables × Tally) : Bool := colour (p.1, doubleT p.2)

def last (p : Tables × Tally) : Bool :=
  colour (p.1, Iter.pick [] (p.1.2, doubleT p.2))

@[fun_prop] theorem colour_poly : Poly colour := by unfold colour; fun_prop
@[fun_prop] theorem first_poly : Poly first := by unfold first; fun_prop
@[fun_prop] theorem last_poly : Poly last := by unfold last; fun_prop

@[simp] theorem colour_encode (P Q : List ℕ) (x : ℕ) :
    colour (encodeTables P Q, tally x) = colT P Q x := by
  simp only [colour, flipLow_tally, orbitMin_encode, lessT_tally, colT]

@[simp] theorem first_encode (P Q : List ℕ) (x : ℕ) :
    first (encodeTables P Q, tally x) = firstT P Q x := by
  simp only [first, doubleT_tally, colour_encode, firstT]

@[simp] theorem last_encode (P Q : List ℕ) (x : ℕ) :
    last (encodeTables P Q, tally x) = lastT P Q x := by
  simp only [last, doubleT_tally, show (encodeTables P Q).2 = Q.map tally from rfl,
    pick_tally, colour_encode, lastT]

def xorB (p : Bool × Bool) : Bool := xor p.1 p.2

@[fun_prop] theorem xorB_poly : Poly xorB := (Easy.finite _).poly

def directionTable (p : Tables × Bool) : List Tally :=
  bif p.2 then p.1.2 else p.1.1

@[fun_prop] theorem directionTable_poly : Poly directionTable := by
  unfold directionTable
  fun_prop

def childRow (p : (Tables × (Bool × Bool)) × Tally) : Tally :=
  let tbl := directionTable (p.1.1, p.1.2.1)
  let boundary := bif p.1.2.1 then last (p.1.1, p.2) else first (p.1.1, p.2)
  let base := doubleT p.2
  let j := bif xorB (boundary, p.1.2.2) then () :: base else base
  halfT (Iter.pick [] (tbl, j))

@[fun_prop] theorem childRow_poly : Poly childRow := by unfold childRow; fun_prop

def childTable (p : Tables × (Bool × Bool)) : List Tally :=
  polyPush childRow (p, Iter.lineup (halfT (ruler p.1.1)))

@[fun_prop] theorem childTable_poly : Poly childTable := by
  unfold childTable
  exact ((by fun_prop : Poly (fun p : Tables × (Bool × Bool) =>
    (p, Iter.lineup (halfT (ruler p.1.1)))))).compose
      (Code.Poly.push (([], []), (false, false)) [] childRow_poly)

def child (p : Tables × Bool) : Tables :=
  (childTable (p.1, (false, p.2)), childTable (p.1, (true, p.2)))

@[fun_prop] theorem child_poly : Poly child := by unfold child; fun_prop

private theorem childRow_encode (P Q : List ℕ) (dir b : Bool) (l : ℕ) :
    childRow ((encodeTables P Q, (dir, b)), tally l) =
      tally (if dir then Q.getD (2 * l + (if xor (lastT P Q l) b then 1 else 0)) 0 / 2
        else P.getD (2 * l + (if xor (firstT P Q l) b then 1 else 0)) 0 / 2) := by
  have idx (d : Bool) :
      (bif d then () :: tally (2 * l) else tally (2 * l)) =
        tally (2 * l + if d then 1 else 0) := by
    cases d <;> simp
  have f : directionTable (encodeTables P Q, false) = P.map tally := rfl
  have g : directionTable (encodeTables P Q, true) = Q.map tally := rfl
  cases dir
  · simp only [childRow, Bool.cond_false, first_encode, doubleT_tally, f, xorB, idx,
      pick_tally, halfT_tally]
    rfl
  · simp only [childRow, Bool.cond_true, last_encode, doubleT_tally, g, xorB, idx,
      pick_tally, halfT_tally]
    rfl

@[simp] theorem child_encode (P Q : List ℕ) (b : Bool) :
    child (encodeTables P Q, b) = encodeTables (subT P Q b) (subInvT P Q b) := by
  have hlen :
      halfT (ruler (encodeTables P Q).1) = tally (P.length / 2) := by
    rw [← recover_tally (ruler (encodeTables P Q).1), halfT_tally]
    simp only [encodeTables, List.length_map, ruler_length]
  have ofFn_range (f : ℕ → Tally) (n : ℕ) :
      List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  change (childTable (encodeTables P Q, (false, b)), childTable (encodeTables P Q, (true, b))) =
    ((subT P Q b).map tally, (subInvT P Q b).map tally)
  simp only [childTable, hlen, Iter.lined, polyPush, Function.comp_def,
    childRow_encode, Bool.false_eq_true, ↓reduceIte, ofFn_range, subT, subInvT,
    List.map_map]

end P1SolFactor.SolCross
