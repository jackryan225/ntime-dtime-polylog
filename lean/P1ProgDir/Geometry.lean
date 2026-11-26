import P1Int.LemmaP
import OAI.Computability.IntegerMultiplication.Bits.Multiply
import OAI.Computability.IntegerMultiplication.Carry.Small
import OAI.Computability.IntegerMultiplication.Bits.Small

namespace P1ProgDir.SolGeometry

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Int

set_option maxHeartbeats 1000000

/-- Read the length of the ordinary input as a binary word. -/
theorem easy_lengthWord {A : Type*} [Codec A] :
    Easy (fun w : List A => born w.length) := by
  simpa only [ruler_length, id_eq] using (Easy.ruler Easy.identity).compose easy_chart

def lengthHeader (p : List Bool × List Bool × List Bool) :
    (Word × Word) × List Bool := ((born p.1.length, p.2.2), p.2.1)

theorem easy_lengthHeader : Easy lengthHeader := by
  have hx : Easy (fun p : List Bool × List Bool × List Bool => born p.1.length) :=
    Easy.fst.compose easy_lengthWord
  have hρ : Easy (fun p : List Bool × List Bool × List Bool => p.2.2) :=
    Easy.snd.compose Easy.snd
  have hu : Easy (fun p : List Bool × List Bool × List Bool => p.2.1) :=
    Easy.snd.compose Easy.fst
  exact (hx.pair hρ).pair hu

/-- Compute the D7 clock from the binary input length. -/
def clockWord (a b : ℕ) (n : Word) : Word :=
  add (add (scale (b + 2 * a) (add (product (n, n), [true])), n), [true])

theorem clockWord_value (a b : ℕ) (n : Word) : value (clockWord a b n) = lpTime a b (value n) := by
  simp only [clockWord, add_val, scale_exact, exact_prod, lpTime, pow_two]
  change (b + 2 * a) * (value n * value n + 1) + value n + 1 = _
  ring

theorem poly_clockWord (a b : ℕ) : Poly (clockWord a b) := by
  have hs : Poly (fun n : Word => product (n, n)) :=
    (Poly.identity.pair Poly.identity).compose Poly.product_base
  have hadd : ∀ {X : Type} [Codec X] {f g : X → Word}, Poly f → Poly g →
      Poly (fun w => add (f w, g w)) := fun h k =>
    (h.pair k).compose (easy_add Easy.identity).poly
  have hp : Poly (fun w : Word => scale (b + 2 * a) (add (product (w, w), [true]))) :=
    (hadd hs (Code.Poly.const ([true] : Word))).compose (easy_scale _ Easy.identity).poly
  exact hadd (hadd hp Poly.identity) (Code.Poly.const ([true] : Word))

def lambdaTally (a b : ℕ) (n : Word) : Tally := light (clockWord a b n)

theorem lambdaTally_length (a b : ℕ) (n : Word) :
    (lambdaTally a b n).length = lpK2 a b (value n) := by
  rw [lambdaTally, light_v, tally_length, clockWord_value, lpK2, lpLam2]

theorem poly_lambdaTally (a b : ℕ) : Poly (lambdaTally a b) :=
  (poly_clockWord a b).compose lightPoly

def pTally (a b : ℕ) (n : Word) : Tally :=
  (cutLists (tally 1, light (add (born (lambdaTally a b n).length, [true])))).2

theorem pTally_length (a b : ℕ) (n : Word) :
    (pTally a b n).length = lpP2 a b (value n) := by
  have hlog (x : ℕ) : Nat.clog 2 (x + 1) - 1 = Nat.log 2 x := by
    cases x with
    | zero => decide
    | succ x =>
      have hlo := Nat.pow_log_le_self 2 (show x + 1 ≠ 0 by omega)
      have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (x + 1)
      have h₁ := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
        (show 2 ^ Nat.log 2 (x + 1) < (x + 1) + 1 by omega)
      have h₂ := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
        (show (x + 1) + 1 ≤ 2 ^ (Nat.log 2 (x + 1) + 1) by omega)
      omega
  simp only [pTally, cutLists, light_v, List.length_drop, tally_length, add_val, birthValue]
  change Nat.clog 2 ((lambdaTally a b n).length + 1) - 1 = _
  rw [hlog, lambdaTally_length, lpK2, lpP2]

theorem poly_pTally (a b : ℕ) : Poly (pTally a b) := by
  have hlen := (poly_lambdaTally a b).compose easy_chart.poly
  have hs := (hlen.pair (Code.Poly.const ([true] : Word))).compose (easy_add Easy.identity).poly
  have ht := hs.compose lightPoly
  have he : Easy (fun p : Tally × Tally => (cutLists p).2) :=
    (easy_cut Easy.identity).sndCompose
  exact ((Code.Poly.const (tally 1)).pair ht).compose he.poly

def timesTally (c : ℕ) (u : Tally) : Tally :=
  match c with
  | 0 => []
  | k + 1 => u ++ timesTally k u

theorem easy_timesTally (c : ℕ) : Easy (timesTally c) := by
  induction c with
  | zero => exact Easy.const []
  | succ k hk =>
    exact (Easy.identity.pair hk).compose Easy.append

theorem timesTally_length (c : ℕ) (u : Tally) :
    (timesTally c u).length = c * u.length := by
  induction c with
  | zero => simp [timesTally]
  | succ k hk => simp only [timesTally, List.length_append, hk, Nat.succ_mul, Nat.add_comm]

def hTally (a b : ℕ) (n : Word) : Tally := (half (timesTally 19 (pTally a b n))).1

def bTally (a b : ℕ) (n : Word) : Tally := (half (pTally a b n)).1 ++ hTally a b n

theorem hTally_length (a b : ℕ) (n : Word) :
    (hTally a b n).length = 19 * lpP2 a b (value n) / 2 := by
  simp only [hTally, half_v, timesTally_length, pTally_length, tally_length]

theorem bTally_length (a b : ℕ) (n : Word) :
    (bTally a b n).length = lpP2 a b (value n) / 2 + 19 * lpP2 a b (value n) / 2 := by
  simp only [bTally, List.length_append, half_v, pTally_length, hTally_length, tally_length]

theorem poly_halfFst : Poly (fun t : Tally => (half t).1) := halfCost.fstCompose.poly

theorem poly_hTally (a b : ℕ) : Poly (hTally a b) := by
  apply Code.Poly.compose (f := fun n : Word => timesTally 19 (pTally a b n))
    (g := fun t : Tally => (half t).1)
  · exact Code.Poly.compose (f := pTally a b) (g := timesTally 19)
      (poly_pTally a b) (Easy.poly (easy_timesTally 19))
  · exact poly_halfFst

theorem poly_bTally (a b : ℕ) : Poly (bTally a b) := by
  apply Code.Poly.app (f := fun n : Word => (half (pTally a b n)).1) (g := hTally a b)
  · exact Code.Poly.compose (f := pTally a b) (g := fun t : Tally => (half t).1)
      (poly_pTally a b) poly_halfFst
  · exact poly_hTally a b

def powWord (s : Tally) : Word := shift (s, [true])

theorem powWord_value (s : Tally) : value (powWord s) = 2 ^ s.length := by
  simp [powWord, shift_value, value_cons, d1]

theorem easy_powWord : Easy powWord :=
  easy_shift (Easy.identity.pair (Easy.const [true]))

theorem value_ones (s : Tally) : value (fill true s) + 1 = 2 ^ s.length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change (1 + 2 * value (fill true s)) + 1 = 2 ^ (s.length + 1)
    rw [pow_succ]
    omega

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

def bigCount (a b aM n : ℕ) : ℕ :=
  let p := lpP2 a b n
  let B := 2 ^ (p / 2) * 2 ^ (19 * p / 2)
  (aM * 2 ^ lpK2 a b n + B - 1) / B

def laneCount (a b n : ℕ) : ℕ := 2 ^ (19 * lpP2 a b n / 2)

def iWord (a b aM : ℕ) (n : Word) : Word :=
  let s := bTally a b n
  let t := scale aM (powWord (lambdaTally a b n))
  (cutLists (s, add (t, fill true s))).2

theorem iWord_value (a b aM : ℕ) (n : Word) :
    value (iWord a b aM n) = bigCount a b aM (value n) := by
  have h := value_ones (bTally a b n)
  have he : value (fill true (bTally a b n)) = 2 ^ (bTally a b n).length - 1 := by omega
  simp only [iWord, cutLists, value_drop, add_val, scale_exact, powWord_value,
    lambdaTally_length, he, bTally_length, pow_add, bigCount]
  have hh : 0 < 2 ^ (lpP2 a b (value n) / 2) * 2 ^ (19 * lpP2 a b (value n) / 2) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  congr 1
  omega

theorem poly_iWord (a b aM : ℕ) : Poly (iWord a b aM) := by
  let l := lambdaTally a b
  let s := bTally a b
  let t (n : Word) := scale aM (powWord (l n))
  have he : Easy (fun p : Tally × Word => (cutLists p).2) :=
    (easy_cut Easy.identity).sndCompose
  have hf : Easy (fun t : Tally => fill true t) := easy_fill true Easy.identity
  have hg : Easy (fun w : Word => scale aM w) := easy_scale aM Easy.identity
  have ha : Easy add := easy_add Easy.identity
  have ht : Poly t := Code.Poly.compose (f := fun n => powWord (l n)) (g := scale aM)
    (Code.Poly.compose (f := l) (g := powWord) (poly_lambdaTally a b) easy_powWord.poly) hg.poly
  have h1 : Poly (fun n => fill true (s n)) :=
    Code.Poly.compose (f := s) (g := fill true) (poly_bTally a b) hf.poly
  have h2 : Poly (fun n => add (t n, fill true (s n))) :=
    Code.Poly.compose (f := fun n => (t n, fill true (s n))) (g := add) (ht.pair h1) ha.poly
  exact Code.Poly.compose (f := fun n => (s n, add (t n, fill true (s n))))
    (g := fun p => (cutLists p).2) ((poly_bTally a b).pair h2) he.poly

def tritCountWord (a b aM r : ℕ) (n : Word) : Word :=
  shift (hTally a b n, scale r (iWord a b aM n))

theorem tritCountWord_value (a b aM r : ℕ) (n : Word) :
    value (tritCountWord a b aM r n) = bigCount a b aM (value n) * laneCount a b (value n) * r := by
  simp only [tritCountWord, shift_value, scale_exact, hTally_length, iWord_value, laneCount]
  ring

theorem poly_tritCountWord (a b aM r : ℕ) : Poly (tritCountWord a b aM r) := by
  have hs : Easy (scale r) := easy_scale r Easy.identity
  have hh : Easy shift := easy_shift Easy.identity
  have hf : Poly (fun n => scale r (iWord a b aM n)) :=
    Code.Poly.compose (f := iWord a b aM) (g := scale r) (poly_iWord a b aM) hs.poly
  exact Code.Poly.compose (f := fun n => (hTally a b n, scale r (iWord a b aM n)))
    (g := shift) ((poly_hTally a b).pair hf) hh.poly

end P1ProgDir.SolGeometry
