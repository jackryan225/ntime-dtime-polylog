import P1ProgDir.Signed

namespace P1ProgDir.SolC14Reply

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolSigned

def eqSigned (p : Word × Word) : Bool :=
  !(ltSigned p) && !(ltSigned p.swap)

theorem easy_eqSigned : Easy eqSigned := by
  have h := easy_ltSigned.pair (Easy.exchange.compose easy_ltSigned)
  exact h.compose (Easy.finite (fun p : Bool × Bool => !p.1 && !p.2))

theorem eqSigned_eq (p : Word × Word) :
    eqSigned p = true ↔ signedValue p.1 = signedValue p.2 := by
  rcases p with ⟨x, y⟩
  have h (b : Bool) : (!b) = true ↔ ¬ b = true := by cases b <;> decide
  simp only [eqSigned, Bool.and_eq_true, h, Prod.swap, ltSigned_eq]
  omega

def zeroWord (w : Word) : Bool := !more (w, [])

theorem easy_zeroWord : Easy zeroWord :=
  (easy_more (Easy.identity.pair (Easy.const ([] : Word)))).compose
    (Easy.finite (fun b : Bool => !b))

theorem zeroWord_eq (w : Word) : zeroWord w = true ↔ value w = 0 := by
  have h (b : Bool) : (!b) = true ↔ ¬ b = true := by cases b <;> decide
  simp only [zeroWord, h, more_lt, value_nil]
  omega

/-- Test the three possible predecessor fields for a range-checked guess owner.
The two inputs to the decision are the guess block and its owner's big block. -/
def windowTest (p : Word × Word × Word × Word × Word) : Bool :=
  (eqSigned (p.1, dec p.2.1) && zeroWord p.2.2.1) ||
    (eqSigned (p.1, p.2.1) && zeroWord p.2.2.2.1) ||
    (eqSigned (p.1, inc p.2.1) && zeroWord p.2.2.2.2)

theorem easy_windowTest : Easy windowTest := by
  let P := Word × Word × Word × Word × Word
  have hQ : Easy (fun p : P => p.1) := Easy.fst
  have hb : Easy (fun p : P => p.2.1) := Easy.snd.compose Easy.fst
  have h0 : Easy (fun p : P => p.2.2.1) := Easy.snd.compose (Easy.snd.compose Easy.fst)
  have h1 : Easy (fun p : P => p.2.2.2.1) := Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
  have h2 : Easy (fun p : P => p.2.2.2.2) := Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd))
  have test {q z : P → Word} (hq : Easy q) (hz : Easy z) :
      Easy (fun p => eqSigned (p.1, q p) && zeroWord (z p)) :=
    (((hQ.pair hq).compose easy_eqSigned).pair (hz.compose easy_zeroWord)).compose
      (Easy.finite (fun b : Bool × Bool => b.1 && b.2))
  exact (((test (hb.compose easy_dec) h0).pair (test hb h1)).pair
    (test (hb.compose easy_inc) h2)).compose
      (Easy.finite (fun p : (Bool × Bool) × Bool => p.1.1 || p.1.2 || p.2))

theorem windowTest_eq (Q b p₀ p₁ p₂ : Word) :
    windowTest (Q, b, p₀, p₁, p₂) = true ↔
      ∃ δ : Fin 3, signedValue Q = signedValue b - 1 + (δ : ℤ) ∧
        value (if δ.val = 0 then p₀ else if δ.val = 1 then p₁ else p₂) = 0 := by
  simp only [windowTest, Bool.or_eq_true, Bool.and_eq_true, eqSigned_eq, zeroWord_eq,
    dec_value, inc_value]
  constructor
  · rintro ((⟨hb, hp⟩ | ⟨hb, hp⟩) | ⟨hb, hp⟩)
    · exact ⟨0, by simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hb, hp⟩
    · exact ⟨1, by change signedValue Q = signedValue b - 1 + 1; omega, hp⟩
    · exact ⟨2, by change signedValue Q = signedValue b - 1 + 2; omega, hp⟩
  · rintro ⟨δ, h, hp⟩
    fin_cases δ
    · exact Or.inl (Or.inl ⟨by change signedValue Q = signedValue b - 1 + 0 at h; omega, hp⟩)
    · exact Or.inl (Or.inr ⟨by change signedValue Q = signedValue b - 1 + 1 at h; omega, hp⟩)
    · exact Or.inr ⟨by change signedValue Q = signedValue b - 1 + 2 at h; omega, hp⟩

end P1ProgDir.SolC14Reply
