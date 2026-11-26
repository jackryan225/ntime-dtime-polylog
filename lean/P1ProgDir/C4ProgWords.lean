import P1ProgDir.C4ProgLogic
import P1ProgDir.C4ProgNumerics

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Net P1Wit P1ChkDir

theorem bval_eq_value (l : Word) : P1Batch.bval l = value l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp only [P1Batch.bval, value_cons, ih] <;> rfl

def wordLT (p : Word × Word) : Bool := more p.swap

@[fun_prop] theorem poly_wordLT : Poly wordLT :=
  (easy_more Easy.exchange).poly

theorem wordLT_true (x y : Word) : wordLT (x, y) = true ↔ value x < value y :=
  more_lt y x

def wordEq (p : Word × Word) : Bool := !(wordLT p || wordLT p.swap)

@[fun_prop] theorem poly_wordEq : Poly wordEq :=
  (poly_wordLT.pair (Easy.exchange.poly.compose poly_wordLT)).compose
    (Easy.finite (fun q : Bool × Bool => !(q.1 || q.2))).poly

theorem wordEq_true (x y : Word) : wordEq (x, y) = true ↔ value x = value y := by
  have h₁ : wordLT (x, y) = false ↔ ¬value x < value y := by
    rw [← Bool.not_eq_true, wordLT_true]
  have h₂ : wordLT (y, x) = false ↔ ¬value y < value x := by
    rw [← Bool.not_eq_true, wordLT_true]
  change (!(wordLT (x, y) || wordLT (y, x))) = true ↔ _
  rw [Bool.not_eq_true', Bool.or_eq_false_iff, h₁, h₂]
  omega

def wordMin (p : Word × Word) : Word := bif wordLT p then p.1 else p.2

@[fun_prop] theorem poly_wordMin : Poly wordMin := by unfold wordMin; fun_prop

theorem value_wordMin (x y : Word) : value (wordMin (x, y)) = min (value x) (value y) := by
  unfold wordMin
  cases e : wordLT (x, y)
  · rw [Bool.cond_false, min_eq_right]
    exact Nat.le_of_not_gt fun h => by rw [(wordLT_true x y).mpr h] at e; contradiction
  · rw [Bool.cond_true, min_eq_left ((wordLT_true x y).mp e).le]

def wordSub (p : Word × Word) : Word := bif (sub p).2 then [] else (sub p).1

@[fun_prop] theorem poly_wordSub : Poly wordSub := by unfold wordSub; fun_prop

theorem value_wordSub (x y : Word) : value (wordSub (x, y)) = value x - value y := by
  unfold wordSub
  cases hb : (sub (x, y)).2
  · rw [Bool.cond_false, sub_val_le]
    exact Nat.le_of_not_gt fun h => by rw [(sub_borrow x y).mpr h] at hb; contradiction
  · rw [Bool.cond_true, value_nil, Nat.sub_eq_zero_of_le ((sub_borrow x y).mp hb).le]

def wordHead (w : Word) : Bool := w.headD false

def wordTail (w : Word) : Word := w.tail

@[fun_prop] theorem easy_wordHead : Easy wordHead := Iter.leader false

@[fun_prop] theorem easy_wordTail : Easy wordTail := by
  have e : wordTail = (fun w : Word => List.casesOn w [] (fun _ t => t)) := by
    funext w
    cases w <;> rfl
  rw [e]
  exact Easy.listCase [] Easy.snd

@[fun_prop] theorem poly_wordHead : Poly wordHead := easy_wordHead.poly

@[fun_prop] theorem poly_wordTail : Poly wordTail := easy_wordTail.poly

theorem value_wordHead (w : Word) : (wordHead w).toNat = value w % 2 := by
  cases w with
  | nil => rfl
  | cons b w => cases b <;> simp only [wordHead, List.headD_cons, value_odd, d0, d1] <;> rfl

theorem value_wordTail (w : Word) : value (wordTail w) = value w / 2 := by
  cases w with
  | nil => rfl
  | cons b w => exact (value_half b w).symm

def wordQR (p : Word × Word) : Word × Word := Binary.nat_div p

@[fun_prop] theorem poly_wordQR : Poly wordQR := Binary.polyND

/-- Offset and width of one witness section. -/
abbrev SectionWord := Word × Word

def wordFieldReq (p : Word × SectionWord × Word) : P1Batch.Req :=
  let off := add (p.2.1.1, Binary.school (p.2.1.2, p.2.2))
  (wordMin (off, p.1), p.2.1.2)

@[fun_prop] theorem poly_wordFieldReq : Poly wordFieldReq := by unfold wordFieldReq; fun_prop

theorem bval_wordFieldReq (m : Word) (s : SectionWord) (j : Word) :
    P1Batch.bval (wordFieldReq (m, s, j)).1 =
      min (value m) (value s.1 + value s.2 * value j) ∧
    P1Batch.bval (wordFieldReq (m, s, j)).2 = value s.2 := by
  simp only [wordFieldReq, bval_eq_value, value_wordMin, add_val, Binary.school_exact, min_comm, and_self]

theorem wordFieldReq_address (m : Word) (s : SectionWord) (j : Word) :
    P1Batch.bval (wordFieldReq (m, s, j)).1 ≤ value m := by
  rw [(bval_wordFieldReq m s j).1]
  exact Nat.min_le_left _ _

theorem wordFieldReq_fetch (u : Word) (D : Dims) (s : ℕ) (m : Word) (w : SectionWord) (j : Word)
    (hm : value m = u.length) (ho : value w.1 = D.off s) (hw : value w.2 = D.width s) :
    P1Batch.bval (P1Batch.fetch u (wordFieldReq (m, w, j))) = readField D u s (value j) := by
  rw [← fieldReq_value]
  unfold P1Batch.fetch
  rw [(bval_wordFieldReq m w j).1, (bval_wordFieldReq m w j).2, hm, ho, hw]
  simp only [fieldReq, bval_canonical, Nat.mul_comm (D.width s) (value j)]

def wordPos (p : Signed.S) : Word := bif p.1 then [] else p.2

@[fun_prop] theorem poly_wordPos : Poly wordPos := by unfold wordPos; fun_prop

theorem value_wordPos (p : Signed.S) : value (wordPos p) = (Signed.whole p).toNat := by
  rcases p with ⟨sgn, w⟩
  cases sgn <;> simp [wordPos, Signed.whole, Signed.tag]

theorem value_drop (w : Word) (h : ℕ) : value (w.drop h) = value w / 2 ^ h := by
  induction h generalizing w with
  | zero => simp
  | succ h ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [List.drop_succ_cons, ih, pow_succ', ← Nat.div_div_eq_div_mul, value_half]

def bigQuot (p : Tally × Word) : Signed.S :=
  let sign := wordHead p.2
  let q := (cutLists (p.1, wordTail p.2)).2
  (sign, bif sign then add (q, [true]) else q)

@[fun_prop] theorem poly_bigQuot : Poly bigQuot := by
  have cut : Easy (fun p : Tally × Word => cutLists (p.1, wordTail p.2)) :=
    easy_cut (Easy.fst.pair (Easy.snd.compose easy_wordTail))
  have pre := (Easy.snd.compose easy_wordHead).pair cut.sndCompose
  have post : Poly (fun p : Bool × Word => (p.1, bif p.1 then add (p.2, [true]) else p.2)) := by
    fun_prop
  exact pre.poly.compose post

theorem ediv_negSucc_ofNat (n : ℕ) {d : ℕ} (hd : 0 < d) :
    (Int.negSucc n) / (d : ℤ) = -((n / d : ℕ) : ℤ) - 1 := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hrem : (↑(n % d) : ℤ) < d := by exact_mod_cast Nat.mod_lt n hd
  have hnon : (0 : ℤ) ≤ ↑(n % d) := Int.natCast_nonneg _
  have hsum : ((n / d : ℕ) : ℤ) * d + ↑(n % d) = (n : ℤ) := by
    rw [mul_comm]
    exact_mod_cast (Nat.div_add_mod n d)
  apply ediv_eq_of_bounds hd'
  · rw [Int.negSucc_eq, sub_mul, neg_mul, one_mul]
    omega
  · rw [Int.negSucc_eq, sub_mul, neg_mul, one_mul]
    omega

theorem whole_bigQuot (w : Word) (h : ℕ) :
    Signed.whole (bigQuot (tally h, w)) = bigOf (2 ^ h) (unzigzag (value w)) := by
  cases w with
  | nil =>
    simp [bigQuot, wordHead, wordTail, Signed.whole, Signed.tag, cutLists, unzigzag, bigOf]
  | cons b w =>
    have e : (cutLists (tally h, w)).2 = w.drop h := by simp [cutLists, tally_length]
    cases b
    · simp only [bigQuot, wordHead, wordTail, List.headD_cons, List.tail_cons, Bool.cond_false, e, Signed.whole, Signed.tag,
        one_mul, value_drop, value_odd, d0, unzigzag, ↓reduceIte, value_half, bigOf]
      exact Int.natCast_ediv ..
    · have e' : unzigzag (value (true :: w)) = Int.negSucc (value w) := by
        simp only [unzigzag, value_odd, d1, Nat.one_ne_zero, ↓reduceIte, value_half]
      have eqBig : bigOf (2 ^ h) (unzigzag (value (true :: w))) =
          -((value w / 2 ^ h : ℕ) : ℤ) - 1 := by
        unfold bigOf
        rw [e', ediv_negSucc_ofNat _ (Nat.two_pow_pos _)]
      rw [eqBig]
      simp only [bigQuot, wordHead, wordTail, List.headD_cons, List.tail_cons, Bool.cond_true, e, Signed.whole, Signed.tag,
        neg_one_mul, add_val, value_cons, d1, value_nil, Nat.mul_zero, Nat.add_zero, value_drop]
      push_cast
      omega

/-- Destination port type for any stored zigzag block numbers, including a pair
whose quotient difference falls outside the three physical port types. -/
def wordPortSlot (p : Tally × Word × Word × Word) : Word :=
  let big₀ := bigQuot (p.1, p.2.1)
  let big₁ := bigQuot (p.1, p.2.2.1)
  let gap := Signed.plus (Signed.plus (big₀, (false, p.2.2.2)), Signed.neg big₁)
  (Binary.nat_div (wordPos gap, [true, true])).2

@[fun_prop] theorem poly_wordPortSlot : Poly wordPortSlot := by
  have hPlus := Signed.easy_plus.poly
  have hNeg := Signed.easy_neg.poly
  unfold wordPortSlot
  fun_prop

theorem value_wordPortSlot (h : ℕ) (x y δ : Word) :
    value (wordPortSlot (tally h, x, y, δ)) =
      (bigOf (2 ^ h) (unzigzag (value x)) + ↑(value δ) - bigOf (2 ^ h) (unzigzag (value y))).toNat % 3 := by
  unfold wordPortSlot
  rw [(Binary.division_rules _ _).2, value_wordPos, Signed.plus_v, Signed.plus_v,
    whole_bigQuot, Signed.neg_r, whole_bigQuot]
  have hd : Signed.whole (false, δ) = ↑(value δ) := by simp only [Signed.whole, Signed.tag, Bool.cond_false, one_mul]
  rw [hd, sub_eq_add_neg]
  rfl

end P1ProgDir.SolC4
