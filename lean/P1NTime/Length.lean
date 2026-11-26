import C1Challenge.NonVacuity
import P1Wrap.ParamTask
import P1Hier.UTSplit

namespace P1NTime.AstraNTime

open C1Challenge
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Wrap.W3.PT

/-- The guess always fits in one bit per input cell. -/
theorem guessLen_le (n : ℕ) : guessLen n ≤ n := by
  have growth (k : ℕ) : (k + 3) ^ 2 < 2 ^ (k + 4) := by
    induction k with
    | zero => decide
    | succ k ih =>
      calc
        (k + 1 + 3) ^ 2 ≤ 2 * (k + 3) ^ 2 := by
          rw [show 2 * (k + 3) ^ 2 = (k + 1 + 3) ^ 2 + (k ^ 2 + 4 * k + 2) by ring]
          exact Nat.le_add_right _ _
        _ < 2 * 2 ^ (k + 4) := Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ = 2 ^ (k + 1 + 4) := by
          exact (Nat.mul_comm 2 _).trans (pow_succ (2 : ℕ) (k + 4)).symm
  rcases n with _ | _ | _ | k
  · decide
  · decide
  · decide
  · change Nat.log 2 ((k + 3) ^ 2) ≤ k + 3
    by_contra! high
    have lower : (2 : ℕ) ^ (k + 4) ≤ 2 ^ Nat.log 2 ((k + 3) ^ 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (not_le_of_gt (growth k))
      (lower.trans (Nat.pow_log_le_self 2 (by positivity)))

/-- The floor logarithm of the square as a tally, from a binary argument. -/
def squareLogT (w : Word) : Tally :=
  (cutLists (tally 1, light (add (sqW w, [true])))).2

theorem squareLogT_length (w : Word) :
    (squareLogT w).length = guessLen (value w) := by
  simp only [squareLogT, cutLists, List.length_drop, light_v, tally_length,
    add_val, sqW, exact_prod, value_one, clog_succ_sub_one, guessLen, pow_two]

theorem poly_squareLogT : Poly squareLogT := by
  unfold squareLogT
  exact poly_drop (Code.Poly.const (tally 1))
    (poly_light (poly_add (poly_sq Code.Poly.identity) (Code.Poly.const [true])))

def guessTally (s : Tally) : Tally := squareLogT (born s.length)

theorem guessTally_length (s : Tally) : (guessTally s).length = guessLen s.length := by
  rw [guessTally, squareLogT_length, birthValue]

/-- Polynomial cost on the binary length is linear in the original tally length. -/
theorem easy_guessTally : Easy guessTally := by
  obtain ⟨t, ⟨k, C, ht⟩, hT⟩ := poly_squareLogT
  obtain ⟨D, hD⟩ := absorb1 k C
  have run : Task (fun s : Tally => size s + t (born s.length)) send
      (fun s => send (guessTally s)) :=
    Task.compose easy_chart (Task.on hT (fun s : Tally => born s.length))
  refine Task.bound run (D + 2) (fun s => ?_)
  have cost : t (born s.length) ≤ D * (s.length + 1) :=
    (ht (born s.length)).trans (hD s.length)
  have hs : s.length + 1 ≤ size s + 1 := by rw [size_tally]; omega
  have hmul := Nat.mul_le_mul_left D hs
  rw [Nat.add_mul]
  omega

/-- The test uses the parser shared with the hierarchy checker. -/
def checkLength (z : List Bool) : Bool :=
  decide ((P1Hier.UM.unGuess z).1.length =
    (guessTally (ruler (P1Hier.UM.unGuess z).2)).length)

theorem easy_checkLength : Easy checkLength := by
  have hw : Easy (fun z => (P1Hier.UM.unGuess z).1) := P1Hier.UM.easy_unGuess.fstCompose
  have hx : Easy (fun z => (P1Hier.UM.unGuess z).2) := P1Hier.UM.easy_unGuess.sndCompose
  exact (hw.pair ((Easy.ruler hx).compose easy_guessTally)).compose Code.Iter.linked

theorem checkLength_withGuess (u x : List Bool) :
    checkLength (withGuess u x) = decide (u.length = guessLen x.length) := by
  simp only [checkLength, P1Hier.UM.unGuess_withGuess, guessTally_length, ruler_length]

theorem machine_of_easy (f : List Bool → Bool) (hf : Easy f) :
    ∃ (D : Machine) (K : ℕ), ∀ z : List Bool,
      HaltsWithin D z (f z) (K * (z.length + 1)) := by
  obtain ⟨M, K, hM⟩ := P1Hier.compile_task size (fun z : List Bool => z) f hf
  refine ⟨P1Hier.ofOAI M, 3 * K, fun z => ?_⟩
  have h := P1Hier.haltsWithin_ofOAI M z (f z) _ (hM z)
  refine h.mono ?_
  rw [size_word]
  calc
    K * (z.length + (2 * z.length + 1) + 1) ≤ K * (3 * (z.length + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 3 * K * (z.length + 1) := by ring

/-- A single linear-time deterministic checker works for every candidate. -/
theorem lengthMachine :
    ∃ (D : Machine) (K : ℕ), ∀ u x : List Bool,
      HaltsWithin D (withGuess u x) (decide (u.length = guessLen x.length))
        (K * ((withGuess u x).length + 1)) := by
  obtain ⟨D, K, hD⟩ := machine_of_easy checkLength easy_checkLength
  exact ⟨D, K, fun u x => (checkLength_withGuess u x) ▸ hD (withGuess u x)⟩

end P1NTime.AstraNTime

#print axioms P1NTime.AstraNTime.guessLen_le
#print axioms P1NTime.AstraNTime.lengthMachine
