import OAI.Computability.IntegerMultiplication.Carry.Shrink

namespace P1SolFactor.SolPolyWords

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code

@[fun_prop] theorem pick_poly {X : Type} [Codec X] (d : X) : Poly (Iter.pick d) :=
  (Iter.facile d).poly

theorem pick_getD {X : Type} (d : X) (xs : List X) (n : ℕ) :
    Iter.pick d (xs, tally n) = xs.getD n d := by
  simp only [Iter.pick, tally_length, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD]

@[simp] theorem pick_tally (xs : List ℕ) (n : ℕ) :
    Iter.pick ([] : Tally) (xs.map tally, tally n) = tally (xs.getD n 0) := by
  rw [pick_getD]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[n]? <;> rfl

def decT (x : Tally) : Tally := (cutLists (tally 1, x)).2

def halfT (x : Tally) : Tally := (Carry.half x).1

def oddT (x : Tally) : Bool := (Carry.half x).2

def eqT (p : Tally × Tally) : Bool := decide (p.1.length = p.2.length)

def lessT (p : Tally × Tally) : Bool := Iter.small p

def doubleT (x : Tally) : Tally := x ++ x

def flipLow (x : Tally) : Tally := bif oddT x then decT x else () :: x

def minT (p : Tally × Tally) : Tally := bif lessT p then p.1 else p.2

@[fun_prop] theorem cut_poly {X : Type} [Codec X] : Poly (cutLists (X := X)) :=
  (easy_cut Easy.identity).poly

@[fun_prop] theorem ruler_poly {X : Type} [Codec X] : Poly (ruler (X := X)) :=
  (Easy.ruler Easy.identity).poly

@[fun_prop] theorem decT_poly : Poly decT := ((Code.Poly.const (X := Tally) (tally 1)).pair Code.Poly.identity).compose cut_poly.sndCompose
@[fun_prop] theorem halfT_poly : Poly halfT := Carry.halfCost.poly.fstCompose
@[fun_prop] theorem oddT_poly : Poly oddT := Carry.halfCost.poly.sndCompose
@[fun_prop] theorem eqT_poly : Poly eqT := Iter.linked.poly
@[fun_prop] theorem lessT_poly : Poly lessT := Iter.small_easy.poly
@[fun_prop] theorem doubleT_poly : Poly doubleT := by unfold doubleT; fun_prop
@[fun_prop] theorem flipLow_poly : Poly flipLow := by unfold flipLow; fun_prop
@[fun_prop] theorem minT_poly : Poly minT := by unfold minT; fun_prop

@[simp] theorem decT_tally (n : ℕ) : decT (tally n) = tally (n - 1) := by
  rw [← recover_tally (decT (tally n))]
  simp [decT, cutLists]

@[simp] theorem halfT_tally (n : ℕ) : halfT (tally n) = tally (n / 2) := by
  simp [halfT, Carry.half_v]

@[simp] theorem oddT_tally (n : ℕ) : oddT (tally n) = decide (n % 2 = 1) := by
  simp [oddT, Carry.half_v, Carry.parity]

@[simp] theorem eqT_tally (m n : ℕ) : eqT (tally m, tally n) = decide (m = n) := by
  simp [eqT]

@[simp] theorem lessT_tally (m n : ℕ) : lessT (tally m, tally n) = decide (m < n) := by
  simp [lessT, Iter.small]

@[simp] theorem doubleT_tally (n : ℕ) : doubleT (tally n) = tally (2 * n) := by
  rw [← recover_tally (doubleT (tally n))]
  simp [doubleT, two_mul]

@[simp] theorem minT_tally (m n : ℕ) : minT (tally m, tally n) = tally (min m n) := by
  unfold minT
  rw [lessT_tally]
  by_cases h : m < n
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (Nat.le_of_not_gt h)]

end P1SolFactor.SolPolyWords
