import P1SolFactor.PaddedCompare
import P1SolFactor.WordViews

namespace P1SolFactor.SolHalf

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open SolRows

/-- Decode a bit letter of a packed query. Symbols outside the bit encoding read as false. -/
def decodeInputBit {R : Type} : P1P5.EvalSym R → Bool
  | .inl _ => false
  | .inr tok => decide (tok = P1P5.Tok.one)

@[simp] theorem decodeInputBit_inputBit {R : Type} (b : Bool) :
    decodeInputBit (inputBit (R := R) b) = b := by cases b <;> rfl

@[simp] theorem map_decodeInputBit_inputBit {R : Type} (word : List Bool) :
    (word.map (inputBit (R := R))).map decodeInputBit = word := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [List.map_cons, decodeInputBit_inputBit, ih]

theorem paddedAgree_iff_wordAtWidth {A : Type} (bit : A → Bool) (width : ℕ) (xs ys : List A)
    (hx : xs.length ≤ width) (hy : ys.length ≤ width) :
    paddedAgree bit xs ys ↔ wordAtWidth width (xs.map bit) = wordAtWidth width (ys.map bit) := by
  constructor
  · intro h
    unfold wordAtWidth
    congr 1
    funext i
    exact h i.val
  · intro h i
    by_cases hi : i < width
    · have hread := congrArg (fun word : List Bool => word.getD i false) h
      simp only [wordAtWidth, getD_ofFn, dite_eq_left hi] at hread
      exact hread
    · have hx' : (xs.map bit).length ≤ i := by rw [List.length_map]; omega
      have hy' : (ys.map bit).length ≤ i := by rw [List.length_map]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hx', List.getElem?_eq_none hy']

private theorem ofFn_equal_iff {width : ℕ} {f g : Fin width → Bool} :
    List.ofFn f = List.ofFn g ↔ f = g := by
  refine ⟨fun h => ?_, congrArg List.ofFn⟩
  funext j
  have hread := congrArg (fun word : List Bool => word.getD j.val false) h
  simpa only [getD_ofFn, dite_eq_left j.isLt, Fin.eta] using hread

theorem paddedAgree_in_out {R : Type} {a h : ℕ} (X : State a h) (u : X.network.Site)
    (z : X.network.Half u) (i j : Fin (2 ^ a)) (width : ℕ)
    (hin : slotWidth X u true i ≤ width) (hout : slotWidth X u false j ≤ width) :
    paddedAgree (decodeInputBit (R := R))
        ((fieldBits X u z true i).map inputBit) ((fieldBits X u z false j).map inputBit) ↔
      inWord X u z i width = outWord X u z j width := by
  rw [paddedAgree_iff_wordAtWidth decodeInputBit width]
  · rw [map_decodeInputBit_inputBit, map_decodeInputBit_inputBit, wordAtWidth_in, wordAtWidth_out]
    exact ofFn_equal_iff
  · rw [List.length_map, fieldBits_length]; exact hin
  · rw [List.length_map, fieldBits_length]; exact hout

theorem paddedAgree_out_zero {R : Type} {a h : ℕ} (X : State a h) (u : X.network.Site)
    (z : X.network.Half u) (j : Fin (2 ^ a)) (width : ℕ) (hout : slotWidth X u false j ≤ width) :
    paddedAgree (decodeInputBit (R := R)) ((fieldBits X u z false j).map inputBit) [] ↔
      outWord X u z j width = fun _ => false := by
  rw [paddedAgree_iff_wordAtWidth decodeInputBit width]
  · rw [map_decodeInputBit_inputBit, List.map_nil, wordAtWidth_out, wordAtWidth_zero, ← List.ofFn_const]
    exact ofFn_equal_iff
  · rw [List.length_map, fieldBits_length]; exact hout
  · exact Nat.zero_le _

theorem paddedAgree_out_full {R : Type} {a h : ℕ} (X : State a h) (u : X.network.Site)
    (z : X.network.Half u) (j : Fin (2 ^ a)) (width : ℕ) (hout : slotWidth X u false j ≤ width)
    (word : Fin width → Bool) :
    paddedAgree (decodeInputBit (R := R)) ((fieldBits X u z false j).map inputBit)
      ((List.ofFn word).map inputBit) ↔ outWord X u z j width = word := by
  rw [paddedAgree_iff_wordAtWidth decodeInputBit width]
  · have hself : asWord width word = word := by funext k; simp [asWord, k.isLt]
    rw [map_decodeInputBit_inputBit, map_decodeInputBit_inputBit, wordAtWidth_out, wordAtWidth_ofFn, hself]
    exact ofFn_equal_iff
  · rw [List.length_map, fieldBits_length]; exact hout
  · rw [List.length_map, List.length_ofFn]

end P1SolFactor.SolHalf
