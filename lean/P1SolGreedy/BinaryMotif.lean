import P1SolGreedy.GreedyFormat
import OAI.Computability.IntegerMultiplication.Carry.Square
import OAI.Computability.VPVNP.MotifAdmission

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP

namespace P1SolGreedy.SolDemand

def bitXorPair (p : Bool × Bool) : Bool := Bool.xor p.1 p.2

def xorWords (p : NumberWord × NumberWord) : NumberWord :=
  (Code.zipSafe false false p).map bitXorPair

@[fun_prop] theorem xorWords_poly : Poly xorWords :=
  (Easy.zipSafe false false).poly.compose (Easy.finite bitXorPair).mapping.poly

theorem value_cons_bit (b : Bool) (w : NumberWord) :
    Bits.value (b :: w) = Nat.bit b (Bits.value w) := by
  cases b <;> simp [Nat.bit_val, Nat.add_comm]

theorem value_xorPairs (ps : List (Bool × Bool)) :
    Bits.value (ps.map bitXorPair) = Bits.value (ps.map Prod.fst) ^^^ Bits.value (ps.map Prod.snd) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, value_cons_bit, Nat.xor_bit, bitXorPair, ih]

theorem value_xorWords (x y : NumberWord) :
    Bits.value (xorWords (x, y)) = Bits.value x ^^^ Bits.value y := by
  unfold xorWords
  rw [value_xorPairs]
  unfold Code.zipSafe
  rw [List.map_fst_zip, List.map_snd_zip]
  · simp [Bits.value_append]
  all_goals simp [Nat.add_comm]

theorem bval_xorWords (x y : NumberWord) :
    P1Batch.bval (xorWords (x, y)) = P1Batch.bval x ^^^ P1Batch.bval y := by
  rw [← value_bval, value_xorWords, value_bval, value_bval]

def sumStep (p : Unit × NumberWord × NumberWord) : NumberWord :=
  Bits.add (p.2.1, p.2.2)

def sumWords (xs : List NumberWord) : NumberWord :=
  Carry.trek sumStep (xs, (), [])

@[fun_prop] theorem sumWords_poly : Poly sumWords := by
  have hStep : Poly sumStep := by unfold sumStep; fun_prop
  have hCount := Carry.polyTrek sumStep hStep 3 (by
    intro z acc w
    simp only [sumStep, P1ChkFinal.size_listBool, Bits.add_length]
    omega)
  exact (show Poly (fun xs : List NumberWord => (xs, (), ([] : NumberWord))) from by fun_prop).compose hCount

theorem bval_sumWords (xs : List NumberWord) :
    P1Batch.bval (sumWords xs) = (xs.map P1Batch.bval).sum := by
  have H (ys : List NumberWord) (acc : NumberWord) :
      Bits.value (Carry.trek sumStep (ys, (), acc)) =
        Bits.value acc + (ys.map Bits.value).sum := by
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      change Bits.value (Carry.trek sumStep (ys, (), Bits.add (acc, y))) =
        Bits.value acc + ((y :: ys).map Bits.value).sum
      rw [ih, Bits.add_val, List.map_cons, List.sum_cons, Nat.add_assoc]
  unfold sumWords
  rw [← value_bval, H]
  simp only [show Bits.value = P1Batch.bval from funext value_bval, P1Batch.bval, Nat.zero_add]

/-- Compute the same ceiling as the integer motif admission rule using binary division and square root. -/
def ceilRootWords (p : NumberWord × NumberWord) : NumberWord :=
  bif numberEq (p.1, []) then []
  else Bits.add (Carry.rescue (Carry.nat_div (Carry.sub0 (p.1, [true]), p.2)).1, [true])

@[fun_prop] theorem ceilRootWords_poly : Poly ceilRootWords := by
  unfold ceilRootWords
  fun_prop

theorem bval_ceilRootWords (n d : NumberWord) :
    P1Batch.bval (ceilRootWords (n, d)) =
      MotifAdmission.ceilRoot (P1Batch.bval n) (P1Batch.bval d) := by
  have h1 : P1Batch.bval (Carry.sub0 (n, [true])) = P1Batch.bval n - 1 := by
    rw [← value_bval, Carry.sub0_v, value_bval]
    rfl
  have hdiv := (bval_divide (Carry.sub0 (n, [true])) d).1
  rw [h1] at hdiv
  unfold ceilRootWords MotifAdmission.ceilRoot
  dsimp only
  by_cases h : P1Batch.bval n = 0
  · have hb : numberEq (n, []) = true := (numberEq_spec _).mpr h
    rw [hb, Bool.cond_true, ite_eq_left h]
    rfl
  · have hb : numberEq (n, []) = false := Bool.eq_false_iff.mpr (fun ht => h ((numberEq_spec _).mp ht))
    rw [hb, Bool.cond_false, ite_eq_right h, MotifAdmission.floorRoot_eq,
      ← value_bval, Bits.add_val, Carry.rescued, value_bval, hdiv]
    rfl

#print axioms bval_xorWords
#print axioms bval_ceilRootWords

end P1SolGreedy.SolDemand
