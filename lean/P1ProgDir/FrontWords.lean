import P1ProgDir.Geometry
import P1ProgDir.Signed

namespace P1ProgDir.SolFrontWords

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Int P1ProgDir.SolGeometry

/-- Width of the directory fields, chosen from fixed constants and the clock length. -/
def widthTally (a b w₀ w₁ : ℕ) (n : Word) : Tally :=
  tally w₀ ++ timesTally w₁ (lambdaTally a b n)

theorem widthTally_length (a b w₀ w₁ : ℕ) (n : Word) :
    (widthTally a b w₀ w₁ n).length = w₀ + w₁ * lpK2 a b (value n) := by
  simp only [widthTally, List.length_append, tally_length, timesTally_length, lambdaTally_length]

theorem poly_widthTally (a b w₀ w₁ : ℕ) : Poly (widthTally a b w₀ w₁) :=
  (Code.Poly.const (tally w₀)).app ((poly_lambdaTally a b).compose (easy_timesTally w₁).poly)

def guessCellsWord (a : ℕ) (n : Word) : Word :=
  scale a (add (product (n, n), [true]))

theorem guessCellsWord_value (a : ℕ) (n : Word) :
    value (guessCellsWord a n) = a * (value n ^ 2 + 1) := by
  simp only [guessCellsWord, scale_exact, add_val, exact_prod, pow_two]
  rfl

theorem poly_guessCellsWord (a : ℕ) : Poly (guessCellsWord a) := by
  have h2 : Poly (fun n : Word => product (n, n)) :=
    (Poly.identity.pair Poly.identity).compose Poly.product_base
  exact ((h2.pair (Code.Poly.const ([true] : Word))).compose (easy_add Easy.identity).poly).compose
    (easy_scale a Easy.identity).poly

/-- Number of big blocks containing a guess cell in the concrete input tape. -/
def guessCountWord (a b : ℕ) (n : Word) : Word :=
  if a = 0 then [] else
    SolSigned.incMagnitude
      ((cutLists (bTally a b n, SolSigned.decMagnitude (false :: guessCellsWord a n))).2)

theorem guessCountWord_value (a b : ℕ) (n : Word) :
    value (guessCountWord a b n) =
      if a = 0 then 0 else
        (2 * (a * (value n ^ 2 + 1)) - 1) /
          (2 ^ (lpP2 a b (value n) / 2) * laneCount a b (value n)) + 1 := by
  unfold guessCountWord
  split_ifs with ha
  · rfl
  · have h : 0 < value (false :: guessCellsWord a n) := by
      rw [value_cons, d0, zero_add, guessCellsWord_value]
      positivity
    have he := SolSigned.decMagnitude_value _ h
    have he' : value (SolSigned.decMagnitude (false :: guessCellsWord a n)) =
        2 * (a * (value n ^ 2 + 1)) - 1 := by
      rw [value_cons, d0, zero_add, guessCellsWord_value] at he
      omega
    simp only [SolSigned.incMagnitude_value, cutLists, value_drop, he', bTally_length, pow_add, laneCount]

theorem poly_guessCountWord (a b : ℕ) : Poly (guessCountWord a b) := by
  unfold guessCountWord
  split_ifs
  · exact Code.Poly.const []
  · have hg := ((Code.Poly.const false).pair (poly_guessCellsWord a)).compose Poly.cons
    exact (((poly_bTally a b).pair (hg.compose SolSigned.easy_decMagnitude.poly)).compose
      (easy_cut Easy.identity).sndCompose.poly).compose SolSigned.easy_incMagnitude.poly

end P1ProgDir.SolFrontWords
