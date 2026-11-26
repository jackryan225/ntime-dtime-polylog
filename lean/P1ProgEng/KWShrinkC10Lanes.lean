import P1P7.ShrinkIds
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.CharP.Two

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.VPVNP.Compression

/-- Number a coordinate word in the same order as the C10 panel codec. -/
abbrev wordNum {n : ℕ} (w : BitWord n) : ℕ := (bitWordFinEquiv n w).val

theorem wordNum_lt {n : ℕ} (w : BitWord n) : wordNum w < 2 ^ n :=
  (bitWordFinEquiv n w).isLt

theorem wordNum_cast {n m : ℕ} (h : m = n) (w : BitWord n) :
    wordNum (w ∘ Fin.cast h) = wordNum w := by
  subst n
  rfl

theorem wordNum_cons {n : ℕ} (b : ZMod 2) (w : BitWord n) :
    wordNum (Fin.cons b w) = wordNum w + 2 ^ n * b.val := by
  exact bitWordFinEquiv_val n (Fin.cons b w)

theorem wordNum_append {m n : ℕ} (u : BitWord m) (v : BitWord n) :
    wordNum (Fin.append u v) = 2 ^ n * wordNum u + wordNum v := by
  induction m with
  | zero =>
      rw [Fin.append_left_nil u v rfl, wordNum_cast]
      change wordNum v = 2 ^ n * 0 + wordNum v
      simp only [Nat.mul_zero, Nat.zero_add]
  | succ m ih =>
      let c := u 0
      let w := Fin.tail u
      have h : u = Fin.cons c w := (Fin.cons_self_tail u).symm
      rw [h, Fin.append_cons, wordNum_cast, wordNum_cons, wordNum_cons, ih]
      rw [pow_add]
      ring

theorem wordNum_split {m n : ℕ} (w : BitWord (m + n)) :
    wordNum w = 2 ^ n * wordNum (splitBitWord m n w).1 + wordNum (splitBitWord m n w).2 := by
  change wordNum w =
    2 ^ n * wordNum (fun i => w (Fin.castAdd n i)) + wordNum (fun i => w (Fin.natAdd m i))
  rw [← wordNum_append, Fin.append_castAdd_natAdd]

theorem wordNum_bit {n : ℕ} (w : BitWord n) (i : Fin n) :
    (wordNum w).testBit (n - 1 - i.val) = decide ((w i).val = 1) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      have h : wordNum w = 2 ^ n * (w 0).val + wordNum (Fin.tail w) :=
        (bitWordFinEquiv_val n w).trans (Nat.add_comm _ _)
      rw [h, Nat.testBit_two_pow_mul_add _ (wordNum_lt (n := n) (Fin.tail w))]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, lt_irrefl, ite_false, Nat.sub_self,
          Nat.testBit_zero, Nat.mod_eq_of_lt (ZMod.val_lt (w 0))]
      · have hj : n + 1 - 1 - j.succ.val = n - 1 - j.val := by
          simp only [Fin.val_succ]
          omega
        have hlt : n - 1 - j.val < n := by omega
        rw [hj, ite_eq_left hlt]
        exact ih (Fin.tail w) j

theorem xor_radix {n a b x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    (2 ^ n * a + x) ^^^ (2 ^ n * b + y) = 2 ^ n * (a ^^^ b) + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hy)]
  split <;> rw [Nat.testBit_xor]

theorem zmodTwo_val_add (a b : ZMod 2) : (a + b).val = a.val ^^^ b.val := by
  have ha : a.val < 2 := ZMod.val_lt a
  have hb : b.val < 2 := ZMod.val_lt b
  rw [ZMod.val_add]
  have ca : a.val = 0 ∨ a.val = 1 := by omega
  have cb : b.val = 0 ∨ b.val = 1 := by omega
  rcases ca with ha | ha <;> rcases cb with hb | hb <;> rw [ha, hb] <;> decide

theorem wordNum_add {n : ℕ} (u v : BitWord n) : wordNum (u + v) = wordNum u ^^^ wordNum v := by
  induction n with
  | zero => change 0 = (0 ^^^ 0); decide
  | succ n ih =>
      have ht : Fin.tail (u + v) = Fin.tail u + Fin.tail v := rfl
      change (bitWordFinEquiv (n + 1) (u + v)).val =
        (bitWordFinEquiv (n + 1) u).val ^^^ (bitWordFinEquiv (n + 1) v).val
      simp only [bitWordFinEquiv_val, ht, Pi.add_apply, zmodTwo_val_add]
      change wordNum (Fin.tail u + Fin.tail v) + 2 ^ n * ((u 0).val ^^^ (v 0).val) =
        (wordNum (Fin.tail u) + 2 ^ n * (u 0).val) ^^^ (wordNum (Fin.tail v) + 2 ^ n * (v 0).val)
      rw [ih]
      rw [Nat.add_comm (wordNum (Fin.tail u)), Nat.add_comm (wordNum (Fin.tail v)),
        xor_radix (wordNum_lt _) (wordNum_lt _), Nat.add_comm]

@[simp] theorem wordNum_zero (n : ℕ) : wordNum (0 : BitWord n) = 0 := by
  simpa only [zero_add, Nat.xor_self] using wordNum_add (0 : BitWord n) 0

theorem wordNum_sub {n : ℕ} (u v : BitWord n) : wordNum (u - v) = wordNum u ^^^ wordNum v := by
  rw [sub_eq_add_neg, show -v = v from funext fun i => CharTwo.neg_eq (v i), wordNum_add]

/-- The old lane consists of colour, slot label, tag and residual lane in descending place value. -/
theorem packingNum {a g : ℕ} (w : BitWord (packingLaneBits a g)) :
    let q := packingFields a g w
    wordNum w =
      (((wordNum q.1 * 2 ^ a + wordNum q.2.1) * 2 ^ packingTagBits (2 ^ a) +
        wordNum q.2.2.1) * 2 ^ g + wordNum q.2.2.2) := by
  let cl := splitBitWord (2 * 2 ^ a + 1) (a + (packingTagBits (2 ^ a) + g)) w
  let sl := splitBitWord a (packingTagBits (2 ^ a) + g) cl.2
  let tl := splitBitWord (packingTagBits (2 ^ a)) g sl.2
  change wordNum w =
      (((wordNum cl.1 * 2 ^ a + wordNum sl.1) * 2 ^ packingTagBits (2 ^ a) +
        wordNum tl.1) * 2 ^ g + wordNum tl.2)
  have h₁ : wordNum w = 2 ^ (a + (packingTagBits (2 ^ a) + g)) * wordNum cl.1 +
      wordNum cl.2 := wordNum_split w
  have h₂ : wordNum cl.2 = 2 ^ (packingTagBits (2 ^ a) + g) * wordNum sl.1 +
      wordNum sl.2 := wordNum_split cl.2
  have h₃ : wordNum sl.2 = 2 ^ g * wordNum tl.1 + wordNum tl.2 := wordNum_split sl.2
  rw [h₁, h₂, h₃]
  simp only [pow_add]
  ring

abbrev LaneFields := ℕ × ℕ × ℕ × ℕ

/-- The code of the old lane with the four fields supplied separately. -/
def joinLane (d j l : ℕ) (f : LaneFields) : ℕ :=
  ((f.1 * d + f.2.1) * j + f.2.2.1) * l + f.2.2.2

/-- The size of the residual field is obtained from a stored lane table. -/
def splitLane (d j l w : ℕ) : LaneFields :=
  let wt := w / l
  let wh := wt / j
  (wh / d, wh % d, wt % j, w % l)

theorem div_radix {r q p : ℕ} (h : r < p) : (q * p + r) / p = q := by
  rw [Nat.mul_comm q p, Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt h, Nat.add_zero]

theorem mod_radix {r q p : ℕ} (h : r < p) : (q * p + r) % p = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem splitLane_join {d j l : ℕ} (f : LaneFields)
    (hh : f.2.1 < d) (ht : f.2.2.1 < j) (hl : f.2.2.2 < l) :
    splitLane d j l (joinLane d j l f) = f := by
  rcases f with ⟨c, h, t, r⟩
  simp only [splitLane, joinLane, div_radix hl, div_radix ht, div_radix hh,
    mod_radix hl, mod_radix ht, mod_radix hh]

theorem splitLane_packing {a g : ℕ} (w : BitWord (packingLaneBits a g)) :
    splitLane (2 ^ a) (2 ^ packingTagBits (2 ^ a)) (2 ^ g) (wordNum w) =
      let f := packingFields a g w
      (wordNum f.1, wordNum f.2.1, wordNum f.2.2.1, wordNum f.2.2.2) := by
  let f := packingFields a g w
  let code : LaneFields := (wordNum f.1, wordNum f.2.1, wordNum f.2.2.1, wordNum f.2.2.2)
  have hw : wordNum w = joinLane (2 ^ a) (2 ^ packingTagBits (2 ^ a)) (2 ^ g) code :=
    packingNum w
  have hh : code.2.1 < 2 ^ a := wordNum_lt (n := a) f.2.1
  have ht : code.2.2.1 < 2 ^ packingTagBits (2 ^ a) :=
    wordNum_lt (n := packingTagBits (2 ^ a)) f.2.2.1
  have hl : code.2.2.2 < 2 ^ g := wordNum_lt (n := g) f.2.2.2
  exact (congrArg (splitLane (2 ^ a) (2 ^ packingTagBits (2 ^ a)) (2 ^ g)) hw).trans
    (splitLane_join code hh ht hl)

theorem joinLane_packing {a g : ℕ} (w : BitWord (packingLaneBits a g)) :
    joinLane (2 ^ a) (2 ^ packingTagBits (2 ^ a)) (2 ^ g)
      (let f := packingFields a g w
       (wordNum f.1, wordNum f.2.1, wordNum f.2.2.1, wordNum f.2.2.2)) = wordNum w :=
  (packingNum w).symm

end P1ProgEng.SolKWS.C10
