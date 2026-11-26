import P1Wit.Layout
import OAI.Computability.IntegerMultiplication.Bits.Small
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace P1ProgDir.SolSigned

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits P1Wit

def sign (w : Word) : Bool := w.headD false
def magnitude (w : Word) : Word := w.tail
def signedValue (w : Word) : ℤ := unzigzag (value w)

theorem easy_sign : Easy sign := Iter.leader false

theorem easy_magnitude : Easy magnitude := by
  change Easy (fun w : Word => w.tail)
  have h := Easy.listCase ([] : Word) (Easy.snd (X := Bool) (Y := Word))
  convert h using 1
  funext w
  cases w <;> rfl

theorem signedValue_eq (w : Word) :
    signedValue w = bif sign w then Int.negSucc (value (magnitude w))
      else (value (magnitude w) : ℤ) := by
  cases w with
  | nil => rfl
  | cons b w =>
    have hm₀ : (0 + 2 * value w) % 2 = 0 := by omega
    have hm₁ : (1 + 2 * value w) % 2 ≠ 0 := by omega
    have hd₀ : (0 + 2 * value w) / 2 = value w := by omega
    have hd₁ : (1 + 2 * value w) / 2 = value w := by omega
    cases b <;>
      simp only [signedValue, sign, magnitude, value_cons, d0, d1, List.headD_cons,
        List.tail_cons, Bool.cond_true, Bool.cond_false, unzigzag, hm₀, hm₁, hd₀, hd₁,
        ite_true, ite_false]
    rfl

def quotient (p : Tally × Word) : Word :=
  sign p.2 :: (cutLists (p.1, magnitude p.2)).2

theorem easy_quotient : Easy quotient := by
  have hs : Easy (fun p : Tally × Word => sign p.2) := Easy.snd.compose easy_sign
  have hm : Easy (fun p : Tally × Word => magnitude p.2) := Easy.snd.compose easy_magnitude
  exact (hs.pair (easy_cut (Easy.fst.pair hm)).sndCompose).compose Easy.cons

theorem signedValue_cons (b : Bool) (w : Word) :
    signedValue (b :: w) = bif b then Int.negSucc (value w) else (value w : ℤ) := by
  rw [signedValue_eq]
  rfl

theorem value_drop (w : Word) (i : ℕ) : value (w.drop i) = value w / 2 ^ i := by
  induction i generalizing w with
  | zero => simp
  | succ i ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [List.drop_succ_cons, ih, pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      rw [value_cons]
      have hd := digit_le b
      omega

theorem quotient_value (s : Tally) (w : Word) :
    signedValue (quotient (s, w)) = signedValue w / (2 : ℕ) ^ s.length := by
  let N := (2 : ℕ) ^ s.length
  have hn : 0 < N := Nat.pow_pos (by decide)
  have hz : 0 < (N : ℤ) := by exact_mod_cast hn
  change signedValue (quotient (s, w)) = signedValue w / (N : ℤ)
  rw [quotient, signedValue_cons, signedValue_eq w]
  change (bif sign w then Int.negSucc (value ((magnitude w).drop s.length))
    else (value ((magnitude w).drop s.length) : ℤ)) = _
  rw [value_drop]
  cases h : sign w
  · simp only [Bool.cond_false]
    exact (Int.natCast_ediv _ _).symm
  · simp only [Bool.cond_true]
    have hs (n : ℕ) : Int.negSucc n = -(n : ℤ) - 1 := by omega
    rw [hs, hs]
    symm
    rw [Int.ediv_eq_iff_of_pos hz]
    have hm := Nat.mod_lt (value (magnitude w)) hn
    have hd := Nat.div_add_mod (value (magnitude w)) N
    have hm' : ((value (magnitude w) % N : ℕ) : ℤ) < N := by exact_mod_cast hm
    have hd' : (N : ℤ) * ((value (magnitude w) / N : ℕ) : ℤ) +
        ((value (magnitude w) % N : ℕ) : ℤ) = value (magnitude w) := by exact_mod_cast hd
    constructor <;> nlinarith

def ltSigned (p : Word × Word) : Bool :=
  let s := sign p.1
  let t := sign p.2
  let m := magnitude p.1
  let n := magnitude p.2
  bif s then (bif t then more (m, n) else true) else
    (bif t then false else more (n, m))

theorem easy_ltSigned : Easy ltSigned := by
  let s := (Easy.fst (X := Word) (Y := Word)).compose easy_sign
  let t := (Easy.snd (X := Word) (Y := Word)).compose easy_sign
  let m := (Easy.fst (X := Word) (Y := Word)).compose easy_magnitude
  let n := (Easy.snd (X := Word) (Y := Word)).compose easy_magnitude
  have hif {f g : Word × Word → Bool} (h : Easy f) (k : Easy g) :
      Easy (fun p => bif sign p.2 then g p else f p) :=
    (t.pair Easy.identity).compose (Easy.ifst h k)
  exact (s.pair Easy.identity).compose (Easy.ifst
    (hif (easy_more (n.pair m)) (Easy.const false))
    (hif (Easy.const true) (easy_more (m.pair n))))

theorem ltSigned_eq (x y : Word) :
    ltSigned (x, y) = true ↔ signedValue x < signedValue y := by
  rw [signedValue_eq, signedValue_eq]
  unfold ltSigned
  change (bif sign x then (bif sign y then more (magnitude x, magnitude y) else true)
    else (bif sign y then false else more (magnitude y, magnitude x))) = true ↔ _
  cases sign x <;> cases sign y <;>
    simp only [Bool.cond_true, Bool.cond_false, more_lt, Bool.false_eq_true, true_iff, false_iff] <;> omega

def incMagnitude (w : Word) : Word := add (w, [true])
def decMagnitude (w : Word) : Word := (sub (w, [true])).1

theorem easy_incMagnitude : Easy incMagnitude :=
  easy_add (Easy.identity.pair (Easy.const [true]))

theorem easy_decMagnitude : Easy decMagnitude :=
  (easy_sub (Easy.identity.pair (Easy.const [true]))).fstCompose

theorem incMagnitude_value (w : Word) : value (incMagnitude w) = value w + 1 := by
  rw [incMagnitude, add_val]
  rfl

theorem decMagnitude_value (w : Word) (h : 0 < value w) :
    value (decMagnitude w) + 1 = value w := by
  unfold decMagnitude
  rw [sub_val_le w [true] h]
  change value w - 1 + 1 = value w
  omega

/-- Add one to a signed number without canonicalizing any high zero bits. -/
def inc (w : Word) : Word :=
  let m := magnitude w
  bif sign w then
    (bif more (m, []) then true :: decMagnitude m else [])
  else false :: incMagnitude m

/-- Subtract one from a signed number. -/
def dec (w : Word) : Word :=
  let m := magnitude w
  bif sign w then true :: incMagnitude m else
    (bif more (m, []) then false :: decMagnitude m else [true])

theorem easy_inc : Easy inc := by
  have hm := easy_magnitude
  have hp := easy_more (hm.pair (Easy.const ([] : Word)))
  have hl := ((Easy.const true).pair (hm.compose easy_decMagnitude)).compose Easy.cons
  have hr := ((Easy.const false).pair (hm.compose easy_incMagnitude)).compose Easy.cons
  exact (easy_sign.pair Easy.identity).compose
    (Easy.ifst hr ((hp.pair Easy.identity).compose (Easy.ifst (Easy.const []) hl)))

theorem easy_dec : Easy dec := by
  have hm := easy_magnitude
  have hp := easy_more (hm.pair (Easy.const ([] : Word)))
  have hl := ((Easy.const false).pair (hm.compose easy_decMagnitude)).compose Easy.cons
  have hr := ((Easy.const true).pair (hm.compose easy_incMagnitude)).compose Easy.cons
  exact (easy_sign.pair Easy.identity).compose
    (Easy.ifst ((hp.pair Easy.identity).compose (Easy.ifst (Easy.const [true]) hl)) hr)

theorem inc_value (w : Word) : signedValue (inc w) = signedValue w + 1 := by
  rw [signedValue_eq w]
  unfold inc
  cases h : sign w
  · simp only [Bool.cond_false, signedValue_cons, incMagnitude_value]
    omega
  · simp only [Bool.cond_true]
    cases hm : more (magnitude w, [])
    · have hn : ¬ 0 < value (magnitude w) := by
        intro hp
        have he := (more_lt (magnitude w) []).mpr hp
        rw [hm] at he
        contradiction
      simp only [Bool.cond_false]
      change 0 = Int.negSucc (value (magnitude w)) + 1
      omega
    · have hp : 0 < value (magnitude w) := (more_lt (magnitude w) []).mp hm
      have hd := decMagnitude_value _ hp
      simp only [Bool.cond_true, signedValue_cons]
      omega

theorem dec_value (w : Word) : signedValue (dec w) = signedValue w - 1 := by
  rw [signedValue_eq w]
  unfold dec
  cases h : sign w
  · simp only [Bool.cond_false]
    cases hm : more (magnitude w, [])
    · have hn : ¬ 0 < value (magnitude w) := by
        intro hp
        have he := (more_lt (magnitude w) []).mpr hp
        rw [hm] at he
        contradiction
      simp only [Bool.cond_false]
      change -1 = (value (magnitude w) : ℤ) - 1
      omega
    · have hp : 0 < value (magnitude w) := (more_lt (magnitude w) []).mp hm
      have hd := decMagnitude_value _ hp
      simp only [Bool.cond_true, Bool.cond_false, signedValue_cons]
      omega
  · simp only [Bool.cond_true, signedValue_cons, incMagnitude_value]
    omega

end P1ProgDir.SolSigned
