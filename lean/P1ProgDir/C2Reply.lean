import P1ProgDir.Readbacks
import P1ProgDir.Signed

namespace P1ProgDir.SolC2Reply

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolSigned P1ProgDir.SolReadbacks

def eqWord (p : Word × Word) : Bool := !(more p) && !(more p.swap)

theorem easy_eqWord : Easy eqWord :=
  ((easy_more Easy.identity).pair (easy_more Easy.exchange)).compose
    (Easy.finite (fun p : Bool × Bool => !p.1 && !p.2))

theorem eqWord_eq (p : Word × Word) : eqWord p = true ↔ value p.1 = value p.2 := by
  rcases p with ⟨x, y⟩
  have h (b : Bool) : (!b) = true ↔ ¬ b = true := by cases b <;> decide
  simp only [eqWord, Bool.and_eq_true, h, Prod.swap, more_lt]
  omega

def positive (w : Word) : Word := bif sign w then [] else magnitude w
def negative (w : Word) : Word := bif sign w then incMagnitude (magnitude w) else []

theorem easy_positive : Easy positive :=
  (easy_sign.pair Easy.identity).compose (Easy.ifst easy_magnitude (Easy.const []))

theorem easy_negative : Easy negative :=
  (easy_sign.pair Easy.identity).compose
    (Easy.ifst (Easy.const []) (easy_magnitude.compose easy_incMagnitude))

theorem signed_by_parts (w : Word) :
    signedValue w = (value (positive w) : ℤ) - (value (negative w) : ℤ) := by
  rw [signedValue_eq]
  unfold positive negative
  cases sign w <;> simp only [Bool.cond_true, Bool.cond_false, value_nil, incMagnitude_value] <;> omega

/-- Compare signed difference against the trit sum using two natural totals.
The four inputs are the current and previous start fields, and the positive and
negative trit counts. -/
def checkSum (p : Word × Word × Word × Word) : Bool :=
  eqWord (add (add (positive p.1, negative p.2.1), p.2.2.2),
    add (add (negative p.1, positive p.2.1), p.2.2.1))

theorem easy_checkSum : Easy checkSum := by
  let P := Word × Word × Word × Word
  have hc : Easy (fun p : P => p.1) := Easy.fst
  have hp : Easy (fun p : P => p.2.1) := Easy.snd.compose Easy.fst
  have hplus : Easy (fun p : P => p.2.2.1) := Easy.snd.compose (Easy.snd.compose Easy.fst)
  have hminus : Easy (fun p : P => p.2.2.2) := Easy.snd.compose (Easy.snd.compose Easy.snd)
  have hl := easy_add ((hc.compose easy_positive).pair (hp.compose easy_negative))
  have hr := easy_add ((hc.compose easy_negative).pair (hp.compose easy_positive))
  exact ((easy_add (hl.pair hminus)).pair (easy_add (hr.pair hplus))).compose easy_eqWord

theorem checkSum_eq (cur prev plus minus : Word) :
    checkSum (cur, prev, plus, minus) = true ↔
      signedValue cur = signedValue prev + (value plus : ℤ) - (value minus : ℤ) := by
  simp only [checkSum, eqWord_eq, add_val, signed_by_parts]
  omega

theorem trit_count_eq (l : List ℕ) :
    (l.map tritDelta).sum =
      ((l.filter (· == 2)).length : ℤ) - ((l.filter (· == 0)).length : ℤ) := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    by_cases h0 : u = 0
    · subst u
      simp [tritDelta, ih]
      omega
    · by_cases h2 : u = 2
      · subst u
        simp [tritDelta, ih]
        omega
      · have hz : tritDelta u = 0 := by unfold tritDelta; split_ifs <;> omega
        simpa [hz, h0, h2] using ih

end P1ProgDir.SolC2Reply
