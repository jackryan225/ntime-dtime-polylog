import P1SolGreedy.BinaryMotif
import P1ChkGreedy.LocalC6
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

private def highDigits : List (ZMod 2) → ℕ
  | [] => 0
  | b :: bs => b.val * 2 ^ bs.length + highDigits bs

private theorem highDigits_append (xs ys : List (ZMod 2)) :
    highDigits (xs ++ ys) = highDigits xs * 2 ^ ys.length + highDigits ys := by
  induction xs with
  | nil => simp [highDigits]
  | cons b bs ih =>
    simp only [List.cons_append, highDigits, List.length_append, pow_add, ih]
    ring

private theorem highDigits_ofFn {n : ℕ} (x : BitWord n) :
    highDigits (List.ofFn x) = (bitWordFinEquiv n x).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, highDigits, List.length_ofFn, bitWordFinEquiv_val, ← ih (Fin.tail x)]
    change _ * _ + highDigits (List.ofFn (Fin.tail x)) = _
    rw [Nat.mul_comm, Nat.add_comm]

/-- Numeric high/low split for the bit-word numbering used in the packing code. -/
theorem splitBitWord_number (high low : ℕ) (x : BitWord (high + low)) :
    (bitWordFinEquiv (high + low) x).val =
      (bitWordFinEquiv high (splitBitWord high low x).1).val * 2 ^ low +
        (bitWordFinEquiv low (splitBitWord high low x).2).val := by
  rw [← highDigits_ofFn, List.ofFn_add, highDigits_append, List.length_ofFn,
    highDigits_ofFn, highDigits_ofFn]
  rfl

theorem packingFields_number {a g : ℕ} (x : BitWord (packingLaneBits a g)) :
    (bitWordFinEquiv _ x).val =
      ((bitWordFinEquiv _ (packingFields a g x).1).val * 2 ^ a +
        (bitWordFinEquiv _ (packingFields a g x).2.1).val) * 2 ^ (packingTagBits (2 ^ a) + g) +
      ((bitWordFinEquiv _ (packingFields a g x).2.2.1).val * 2 ^ g +
        (bitWordFinEquiv _ (packingFields a g x).2.2.2).val) := by
  let c := 2 * 2 ^ a + 1
  let j := packingTagBits (2 ^ a)
  let y := (splitBitWord c (a + (j + g)) x).2
  let z := (splitBitWord a (j + g) y).2
  rw [splitBitWord_number c (a + (j + g)) x,
    show (splitBitWord c (a + (j + g)) x).2 = y from rfl, splitBitWord_number a (j + g) y,
    show (splitBitWord a (j + g) y).2 = z from rfl, splitBitWord_number j g z]
  change _ =
    ((bitWordFinEquiv c (splitBitWord c _ x).1).val * 2 ^ a +
      (bitWordFinEquiv a (splitBitWord a _ y).1).val) * 2 ^ (j + g) +
      ((bitWordFinEquiv j (splitBitWord j g z).1).val * 2 ^ g +
        (bitWordFinEquiv g (splitBitWord j g z).2).val)
  rw [pow_add 2 a]
  ring

theorem packedTagNumber {a g : ℕ} (x : BitWord (packingLaneBits a g)) :
    (bitWordFinEquiv _ x).val / 2 ^ g % 2 ^ packingTagBits (2 ^ a) =
      (bitWordFinEquiv _ (packingFields a g x).2.2.1).val := by
  rw [packingFields_number]
  let j := packingTagBits (2 ^ a)
  let h := (bitWordFinEquiv _ (packingFields a g x).1).val * 2 ^ a +
    (bitWordFinEquiv _ (packingFields a g x).2.1).val
  let t := bitWordFinEquiv j (packingFields a g x).2.2.1
  let l := bitWordFinEquiv g (packingFields a g x).2.2.2
  change (h * 2 ^ (j + g) + (t.val * 2 ^ g + l.val)) / 2 ^ g % 2 ^ j = t.val
  rw [show h * 2 ^ (j + g) + (t.val * 2 ^ g + l.val) =
    2 ^ g * (h * 2 ^ j + t.val) + l.val by rw [pow_add]; ring,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt l.isLt, Nat.add_zero]
  exact Nat.mul_add_mod_of_lt t.isLt

/-- Decode an in-range number with the same zero fallback as the stored bit-word readers. -/
def boundWord (p : NumberWord × NumberWord) : NumberWord :=
  bif Carry.lt_ (p.2, p.1) then p.2 else []

@[fun_prop] theorem boundWord_poly : Poly boundWord := by unfold boundWord; fun_prop

theorem bval_boundWord (n : ℕ) [NeZero n] (v : NumberWord) :
    P1Batch.bval (boundWord (bin n, v)) = (finOr0 n (P1Batch.bval v) : ℕ) := by
  unfold boundWord
  dsimp only
  rw [less_spec, bval_bin]
  unfold finOr0
  by_cases h : P1Batch.bval v < n
  · rw [decide_eq_true h, Bool.cond_true, dite_eq_left h]
  · rw [decide_eq_false h, Bool.cond_false, dite_eq_right h]
    rfl

/-- Extract the tag after removing the residual lane digits of the displacement. -/
def tagOfDispWords (p : NumberWord × NumberWord × NumberWord × NumberWord) : NumberWord :=
  let w := boundWord (p.1, p.2.2.2)
  let higher := (Carry.nat_div (w, p.2.1)).1
  (Carry.nat_div (higher, p.2.2.1)).2

@[fun_prop] theorem tagOfDispWords_poly : Poly tagOfDispWords := by
  unfold tagOfDispWords
  dsimp only
  fun_prop

theorem bval_tagOfDispWords (a g : ℕ) (v : NumberWord) :
    P1Batch.bval (tagOfDispWords
      (bin (2 ^ packingLaneBits a g), bin (2 ^ g), bin (2 ^ packingTagBits (2 ^ a)), v)) =
      (bitWordFinEquiv _ (tagOfDisp a g (P1Batch.bval v)) : ℕ) := by
  let w := boundWord (bin (2 ^ packingLaneBits a g), v)
  let x := (bitWordFinEquiv (packingLaneBits a g)).symm
    (finOr0 (2 ^ packingLaneBits a g) (P1Batch.bval v))
  have hx : (bitWordFinEquiv (packingLaneBits a g) x : ℕ) = P1Batch.bval w := by
    rw [bval_boundWord]
    exact congrArg Fin.val ((bitWordFinEquiv (packingLaneBits a g)).apply_symm_apply _)
  have H := packedTagNumber x
  rw [hx] at H
  change P1Batch.bval (Carry.nat_div
      ((Carry.nat_div (w, bin (2 ^ g))).1, bin (2 ^ packingTagBits (2 ^ a)))).2 = _
  rw [(bval_divide _ _).2, (bval_divide _ _).1, bval_bin, bval_bin]
  exact H

#print axioms bval_tagOfDispWords

end P1SolGreedy.SolDemand
