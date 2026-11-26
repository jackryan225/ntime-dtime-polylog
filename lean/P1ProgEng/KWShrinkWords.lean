import P1P5.KWRefresh

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code Carry Staff
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

private abbrev wordReg : Strip.Regime (ℕ × Tally) := ⟨size, send, Dom.base _⟩

/-- The unary clock limits both binary exponent materialization and enumeration. -/
def internalClock (p : ℕ × Tally) : Tally :=
  tally (min (2 ^ min p.1 p.2.length) p.2.length)

theorem internalClock_poly : Poly internalClock := by
  have hu : Poly (fun p : ℕ × Tally => tally (min p.1 p.2.length)) :=
    P1ProgEng.SolKWR.poly_tallyMin Easy.fst.poly (poly_lengthNat Easy.snd.poly)
      (P1ProgEng.SolKWR.length_dom Easy.snd.poly)
  have hw : Carry.Figure wordReg (fun p => 2 ^ min p.1 p.2.length) :=
    ⟨_, hu.compose easy_flash.poly, fun p => by rw [flash_v, tally_length]⟩
  have hlen : Realizes wordReg (fun p => p.2.length) := by
    change Poly (fun p : ℕ × Tally => tally p.2.length)
    simpa only [recover_tally] using (Easy.snd.poly : Poly (Prod.snd : ℕ × Tally → Tally))
  have hb := Carry.Figure.of_spoken hlen
  have hmin : Carry.Figure wordReg (fun p => min (2 ^ min p.1 p.2.length) p.2.length) := by
    convert hw.variant hb (hw.compare_ hb) using 1
    funext p
    split <;> omega
  exact hmin.pay ((P1ProgEng.SolKWR.length_dom Easy.snd.poly).mono fun p => min_le_right _ _)

/-- Each index yields its fixed-width little-endian word. With a valid clock
the list contains every word once. -/
def internalWords (p : ℕ × Tally) : List Bits.Word :=
  (Iter.lineup (internalClock p)).map (fun i =>
    Bits.resize (tally (min p.1 p.2.length), Carry.born i.length))

theorem internalWords_poly : Poly internalWords := by
  have hw : Poly (fun p : ℕ × Tally => tally (min p.1 p.2.length)) :=
    P1ProgEng.SolKWR.poly_tallyMin Easy.fst.poly (poly_lengthNat Easy.snd.poly)
      (P1ProgEng.SolKWR.length_dom Easy.snd.poly)
  have hi := internalClock_poly.compose Iter.poly_line
  have hf : Poly (fun p : Tally × Tally => Bits.resize (p.1, Carry.born p.2.length)) :=
    (Bits.easy_resize (Easy.fst.pair (Easy.snd.compose easy_chart))).poly
  exact (hw.pair hi).compose (Code.Poly.push [] [] hf)

theorem internalWords_eq (w : ℕ) (pad : Tally) (h : 2 ^ w ≤ pad.length) :
    internalWords (w, pad) = List.ofFn (fun i : Fin (2 ^ w) => Bits.short w i.val) := by
  have hwidth : w ≤ pad.length := (Nat.lt_two_pow_self).le.trans h
  unfold internalWords internalClock
  simp only [min_eq_left hwidth, min_eq_left h, Iter.lined, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, tally_length]
  apply Bits.word_inject
  · rw [Bits.short_length]
    exact Bits.sized_length _ _
  · rw [Bits.value_short]
    change Bits.value (Bits.sized w (Carry.born i.val)) = _
    rw [Bits.sized_low, Carry.birthValue]

end P1ProgEng.SolKWS

#print axioms P1ProgEng.SolKWS.internalWords_poly
#print axioms P1ProgEng.SolKWS.internalWords_eq
