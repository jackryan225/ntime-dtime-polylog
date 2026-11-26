import P1P5.Factor0Target
import P1Benes.Settings
import P1SolC10P.Primitives
import P1SolFmt.FigureTools

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-- Coordinate order, from index zero upward. -/
def coordinateBits {h : ℕ} (w : BitWord h) : List Bool :=
  List.ofFn fun i => P1Benes.zbool (w i)

private theorem digit_zbool (z : ZMod 2) : Bits.digit (P1Benes.zbool z) = z.val := by
  revert z
  decide

theorem coordinateBits_length {h : ℕ} (w : BitWord h) : (coordinateBits w).length = h :=
  List.length_ofFn

theorem coordinateBits_cons {h : ℕ} (w : BitWord (h + 1)) :
    coordinateBits w = P1Benes.zbool (w 0) :: coordinateBits (Fin.tail w) := by
  rw [coordinateBits, List.ofFn_succ]
  rfl

theorem coordinateBits_snoc {h : ℕ} (w : BitWord (h + 1)) :
    coordinateBits w = coordinateBits (Fin.init w) ++ [P1Benes.zbool (w (Fin.last h))] := by
  apply List.ext_getElem
  · simp only [coordinateBits_length, List.length_append, List.length_singleton]
  · intro i hi hj
    by_cases he : i < h
    · rw [List.getElem_append_left (by rwa [coordinateBits_length])]
      simp only [coordinateBits, List.getElem_ofFn, Fin.init, Fin.castSucc_mk]
    · have hi' : i = h := by rw [coordinateBits_length] at hi; omega
      subst i
      rw [List.getElem_append_right (by rw [coordinateBits_length])]
      simp only [coordinateBits_length, Nat.sub_self, List.getElem_cons_zero, coordinateBits,
        List.length_ofFn, List.getElem_ofFn, Fin.last]

/-- The networking code treats coordinate zero as the least significant bit. -/
theorem coordinateBits_value {h : ℕ} (w : BitWord h) :
    Bits.value (coordinateBits w) = (laneEquiv h w).val := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [coordinateBits_cons, Bits.value_cons, digit_zbool, ih]
    change (w 0).val + 2 * (finFunctionFinEquiv (show Fin h → Fin 2 from Fin.tail w)).val =
      (finFunctionFinEquiv (show Fin (h + 1) → Fin 2 from w)).val
    have hw : (finFunctionFinEquiv (show Fin (h + 1) → Fin 2 from w)).val =
        ∑ i : Fin (h + 1), (w i).val * 2 ^ i.val :=
      finFunctionFinEquiv_apply (show Fin (h + 1) → Fin 2 from w)
    have ht : (finFunctionFinEquiv (show Fin h → Fin 2 from Fin.tail w)).val =
        ∑ i : Fin h, (Fin.tail w i).val * 2 ^ i.val :=
      finFunctionFinEquiv_apply (show Fin h → Fin 2 from Fin.tail w)
    rw [hw, ht, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ', Fin.tail]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The request code treats coordinate zero as the most significant bit. -/
theorem coordinateBits_reverse_value {h : ℕ} (w : BitWord h) :
    Bits.value (coordinateBits w).reverse = (bitWordFinEquiv h w).val := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [coordinateBits_cons, List.reverse_cons, Bits.value_append, List.length_reverse,
      coordinateBits_length, ih, bitWordFinEquiv_val, Bits.value_cons, Bits.value_nil]
    simp only [Nat.mul_zero, Nat.add_zero, digit_zbool]

/-- Beneš uses the same high-to-low coordinate order as the requests. -/
theorem label_eq_bitWordFinEquiv (n : ℕ) (w : BitWord (n + 1)) :
    P1Benes.label n w = bitWordFinEquiv (n + 1) w := by
  apply Fin.ext
  rw [← coordinateBits_reverse_value]
  induction n with
  | zero =>
    rw [P1Benes.label_zero, P1Benes.Net.splitLow_symm_val, coordinateBits_cons]
    simp only [coordinateBits, List.ofFn_zero, List.reverse_singleton, Fin.val_zero,
      Nat.mul_zero, Nat.zero_add, Bits.value_cons, Bits.value_nil, Nat.add_zero]
    cases P1Benes.zbool (w 0) <;> rfl
  | succ n ih =>
    rw [P1Benes.label_succ, P1Benes.Net.splitLow_symm_val, coordinateBits_snoc,
      List.reverse_append, List.reverse_singleton]
    simp only [List.singleton_append, Bits.value_cons, Prod.fst, Prod.snd, ih]
    cases P1Benes.zbool (w (Fin.last (n + 1))) <;> simp only [Bits.d0, Bits.d1, if_true,
      Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_comm]

theorem coordinateBits_addrOf {t h : ℕ} (typ : BitWord t) (lane : BitWord h) :
    coordinateBits (addrOf typ lane) = coordinateBits typ ++ coordinateBits lane := by
  apply List.ext_getElem
  · simp only [coordinateBits_length, List.length_append]
  · intro i hi hj
    by_cases ht : i < t
    · rw [List.getElem_append_left (by simpa only [coordinateBits_length] using ht)]
      simp only [coordinateBits, List.getElem_ofFn, addrOf, ht, dite_true]
    · rw [List.getElem_append_right (by simpa only [coordinateBits_length] using Nat.le_of_not_gt ht)]
      simp only [coordinateBits, List.getElem_ofFn, List.length_ofFn, addrOf, ht, dite_false]

theorem addressNumber {t h : ℕ} (typ : BitWord t) (lane : BitWord h) :
    (bitWordFinEquiv (t + h) (addrOf typ lane)).val =
      (bitWordFinEquiv h lane).val + 2 ^ h * (bitWordFinEquiv t typ).val := by
  rw [← coordinateBits_reverse_value, coordinateBits_addrOf, List.reverse_append, Bits.value_append]
  simp only [coordinateBits_reverse_value, List.length_reverse, coordinateBits_length]

/-- Reverse the bits in a fixed-width binary word. -/
def reverseNum (p : Tally × ℕ) : ℕ :=
  P1Batch.bval (Bits.short p.1.length p.2).reverse

theorem reverseNum_poly : Poly reverseNum := by
  let R := P1SolFmt.SolFigure.inputRegime (Tally × ℕ)
  have hf : Carry.Figure R (fun p => p.2) :=
    P1SolC10P.SolC10prog.asFigure (show Poly (Prod.snd : Tally × ℕ → ℕ) from by fun_prop)
  have ht : Staff.Realizes R (fun p => p.1.length) :=
    P1SolFmt.SolFigure.realizes_of_tally (show Poly (Prod.fst : Tally × ℕ → Tally) from by fun_prop)
  exact P1SolC10P.SolC10prog.poly_bval ((show Poly (fun p : Tally × ℕ => Bits.short p.1.length p.2)
    from hf.write ht).rev)

theorem reverseNum_lane {h : ℕ} (w : BitWord h) :
    reverseNum (tally h, (laneEquiv h w).val) = (bitWordFinEquiv h w).val := by
  have hs : Bits.short h (laneEquiv h w).val = coordinateBits w := by
    apply Bits.word_inject
    · rw [Bits.short_length, coordinateBits_length]
    · rw [Bits.value_short, Nat.mod_eq_of_lt (laneEquiv h w).isLt, coordinateBits_value]
  simp only [reverseNum, tally_length, hs, P1SolC10P.SolC10prog.bval_eq_value,
    coordinateBits_reverse_value]

theorem reverseNum_request {h : ℕ} (w : BitWord h) :
    reverseNum (tally h, P1ChkFinal.bwNum w) = (laneEquiv h w).val := by
  have hs : Bits.short h (P1ChkFinal.bwNum w) = (coordinateBits w).reverse := by
    apply Bits.word_inject
    · rw [Bits.short_length, List.length_reverse, coordinateBits_length]
    · unfold P1ChkFinal.bwNum
      rw [Bits.value_short, Nat.mod_eq_of_lt (bitWordFinEquiv h w).isLt, coordinateBits_reverse_value]
  simp only [reverseNum, tally_length, hs, List.reverse_reverse, P1SolC10P.SolC10prog.bval_eq_value,
    coordinateBits_value]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.reverseNum_request
