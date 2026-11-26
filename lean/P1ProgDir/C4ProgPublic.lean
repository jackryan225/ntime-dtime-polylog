import P1ProgDir.C4ProgNat
import P1ProgDir.C4ProgPrepare

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ChkDir P1Wit
open NatCode

abbrev PublicData := List ℕ × List Tally

def publicData (P : C4Dims) : PublicData := (fmtBig P, (fmtSmall P).map tally)

/-- The supplied format program may leave high zeroes in its binary words.
This conversion gives binary naturals and retains the unary work limits. -/
theorem publicData_of_fmt (dims : ℕ → C4Dims) (h : FmtHyp4 dims) :
    Poly (fun w : Word => publicData (dims (value w))) := by
  obtain ⟨f, hf, hs⟩ := h
  have hp : Poly (fun p : List Word × List Tally => (p.1.map value, p.2)) := by
    exact (Easy.fst.poly.compose (Poly.maps _ poly_value)).pair Easy.snd.poly
  have he : (fun w : Word => ((f w).1.map value, (f w).2)) =
      (fun w => publicData (dims (value w))) := by
    funext w
    have vb : P1Batch.bval = value := funext bval_eq_value
    obtain ⟨hbig, hsmall⟩ := hs w
    rw [vb] at hbig hsmall
    have e := congrArg (List.map tally) hsmall
    simp only [List.map_map, Function.comp_def, recover_tally] at e
    change List.map id (f w).2 = _ at e
    rw [List.map_id] at e
    exact Prod.ext hbig e
  rw [← he]
  exact hf.compose hp

def big (p : PublicData) (i : ℕ) : ℕ := p.1.getD i 0

def small (p : PublicData) (i : ℕ) : Tally := p.2.getD i []

@[fun_prop] theorem poly_big (i : ℕ) : Poly (fun p : PublicData => big p i) := by
  exact Easy.fst.poly.compose (poly_getD 0 i)

@[fun_prop] theorem poly_small (i : ℕ) : Poly (fun p : PublicData => small p i) := by
  exact Easy.snd.poly.compose (poly_getD [] i)

def readCap (p : ℕ × ℕ) : ℕ := bif ltb p.1 p.2 then p.1 else p.2

@[fun_prop] theorem poly_readCap : Poly readCap := by unfold readCap; fun_prop

theorem readCap_eq (x y : ℕ) : readCap (x, y) = min x y := by
  unfold readCap
  by_cases h : x < y
  · rw [ltb_iff.mpr h, Bool.cond_true, Nat.min_eq_left h.le]
  · rw [ltb_false_iff.mpr (Nat.le_of_not_lt h), Bool.cond_false, Nat.min_eq_right (Nat.le_of_not_lt h)]

/-- Build one addressed field from public size data and the field index. -/
def numericRequest (p : ℕ × ℕ × ℕ × ℕ) : P1Batch.Req :=
  (Length.born (readCap (p.1, p.2.1 + p.2.2.2 * p.2.2.1)), Length.born p.2.2.1)

@[fun_prop] theorem poly_numericRequest : Poly numericRequest := by
  unfold numericRequest
  fun_prop

theorem numericRequest_eq (D : Dims) (m s i : ℕ) :
    numericRequest (m, D.off s, D.width s, i) = fieldReq m D s i := by
  unfold numericRequest fieldReq
  dsimp only
  rw [readCap_eq, Nat.mul_comm i (D.width s)]

theorem range_of_tally (t : Tally) : (Iter.lineup t).map List.length = List.range t.length := by
  unfold Iter.lineup
  rw [List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_range]
  · intros
    simp only [List.getElem_ofFn, Function.comp_def, tally_length, List.getElem_range]

@[fun_prop] theorem poly_range_of_tally : Poly (fun t : Tally => List.range t.length) := by
  have h := Iter.poly_line.compose (Poly.maps (fun t : Tally => t.length) poly_length)
  rwa [show (fun t : Tally => (Iter.lineup t).map List.length) =
    (fun t : Tally => List.range t.length) from funext range_of_tally] at h

end P1ProgDir.SolC4
