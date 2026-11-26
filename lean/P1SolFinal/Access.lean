import P1ChkFinal.Progs
import P1Batch.Statement
import P1Batch.Sort

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit

abbrev Word := List Bool
abbrev Req := Word × Word

theorem value_bin (n : ℕ) : Bits.value (bin n) = n := by
  rw [← P1Batch.bval_eq_value, bval_bin]

theorem value_bits (n : ℕ) : Bits.value n.bits = n := by
  rw [← P1Batch.bval_eq_value]
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    simp only [P1Batch.bval, ih, Nat.bit_val]
    exact Nat.add_comm _ _

theorem value_field (w : Word) : bitsVal w = Bits.value w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp only [bitsVal, Bits.value_cons, Bits.d0, Bits.d1, Bool.false_eq_true, ite_false,
      ite_true, ih]

def less (i : Req) : Bool := (Bits.sub i).2

theorem less_eq (a b : Word) : less (a, b) = decide (Bits.value a < Bits.value b) :=
  Bool.eq_iff_iff.mpr ((Bits.sub_borrow a b).trans decide_eq_true_iff.symm)

@[fun_prop] theorem easy_choose {X Y : Type*} [Codec X] [Codec Y] {v : X → Bool} {f g : X → Y}
    (h : Easy v) (hf : Easy f) (hg : Easy g) : Easy (fun x => bif v x then f x else g x) :=
  (h.pair (hf.pair hg)).compose (Easy.ifst (X := Y × Y) Easy.snd Easy.fst)

@[fun_prop] theorem easy_less : Easy less := (Bits.easy_sub Easy.identity).compose Easy.snd

def minus (i : Req) : Word := bif less i then [] else (Bits.sub i).1

theorem minus_eq (a b : Word) : Bits.value (minus (a, b)) = Bits.value a - Bits.value b := by
  unfold minus
  rw [less_eq]
  by_cases h : Bits.value a < Bits.value b
  · rw [decide_eq_true h, Bool.cond_true, Bits.value_nil, Nat.sub_eq_zero_of_le h.le]
  · rw [decide_eq_false h, Bool.cond_false, Bits.sub_val_le _ _ (Nat.le_of_not_gt h)]

@[fun_prop] theorem easy_minus : Easy minus := by
  unfold minus
  fun_prop

def smaller (i : Req) : Word := bif less i then i.1 else i.2

theorem smaller_eq (a b : Word) : Bits.value (smaller (a, b)) = min (Bits.value a) (Bits.value b) := by
  unfold smaller
  rw [less_eq]
  by_cases h : Bits.value a < Bits.value b
  · simp only [h, decide_true, Bool.cond_true, min_eq_left h.le]
  · simp only [h, decide_false, Bool.cond_false, min_eq_right (Nat.le_of_not_gt h)]

@[fun_prop] theorem easy_smaller : Easy smaller := by
  unfold smaller
  fun_prop

def clipped (i : Word × Req) : Req :=
  let start := smaller (i.2.1, i.1)
  (start, smaller (i.2.2, minus (i.1, start)))

@[fun_prop] theorem easy_clipped : Easy clipped := by
  unfold clipped
  dsimp only
  fun_prop

def slice (i : Req × Word) : Word :=
  (i.2.drop (Bits.value i.1.1)).take (Bits.value i.1.2)

theorem clipped_start (q : Req) (u : Word) :
    Bits.value (clipped (bin u.length, q)).1 = min (Bits.value q.1) u.length := by
  change Bits.value (smaller (q.1, bin u.length)) = _
  rw [smaller_eq, value_bin]

theorem clipped_width (q : Req) (u : Word) :
    Bits.value (clipped (bin u.length, q)).2 =
      min (Bits.value q.2) (u.length - min (Bits.value q.1) u.length) := by
  change Bits.value (smaller (q.2, minus (bin u.length, (clipped (bin u.length, q)).1))) = _
  rw [smaller_eq, minus_eq, value_bin, clipped_start]

theorem clipped_end (q : Req) (u : Word) :
    Bits.value (clipped (bin u.length, q)).1 + Bits.value (clipped (bin u.length, q)).2 ≤ u.length := by
  rw [clipped_start, clipped_width]
  have h₁ := min_le_right (Bits.value q.1) u.length
  have h₂ := min_le_right (Bits.value q.2) (u.length - min (Bits.value q.1) u.length)
  omega

theorem slice_clipped (q : Req) (u : Word) : slice (clipped (bin u.length, q), u) = slice (q, u) := by
  unfold slice
  rw [clipped_start, clipped_width]
  by_cases h : Bits.value q.1 ≤ u.length
  · rw [min_eq_left h, ← List.length_drop]
    by_cases hw : Bits.value q.2 ≤ (u.drop (Bits.value q.1)).length
    · rw [min_eq_left hw]
    · have hw' := Nat.le_of_not_ge hw
      rw [min_eq_right hw', List.take_length, List.take_of_length_le hw']
  · have e := Nat.le_of_not_ge h
    rw [min_eq_right e, List.drop_eq_nil_of_le (le_refl u.length), List.drop_eq_nil_of_le e]
    simp only [List.take_nil]

theorem size_bin_linear (n : ℕ) : size (bin n) ≤ 2 * n + 3 := by
  rw [size_listBool]
  have h := length_bin_log n
  have h' := Nat.log_le_self 2 n
  omega

set_option maxHeartbeats 3000000 in
theorem computes_slice (hl : LenHyp) :
    Computes (fun i : Req × Word => size i) slice := by
  let d := fun i : Req × Word => clipped (bin i.2.length, i.1)
  let a := fun i : Req × Word => Bits.value (d i).1
  let w := fun i : Req × Word => Bits.value (d i).2
  let pre := fun i : Req × Word => i.2.take (a i)
  let rest := fun i : Req × Word => i.2.drop (a i)
  let field := fun i : Req × Word => (rest i).take (w i)
  let post := fun i : Req × Word => (rest i).drop (w i)
  have h₁ : Easy (fun i : Req × Word => (i.2, (i.1, i.2))) := by fun_prop
  have T₂ := (hl.on (fun i : Req × Word => i.2)).left (fun i => send (i.1, i.2))
  have h₃ : Easy (fun i : Word × (Req × Word) => (clipped (i.1, i.2.1), i.2.2)) := by fun_prop
  have T₃ := h₃.on (fun i : Req × Word => (bin i.2.length, (i.1, i.2)))
  have h₄ : Easy (fun i : Req × Word => (i.1.1, (i.1.2, i.2))) := by fun_prop
  have T₄ := h₄.on (fun i : Req × Word => (d i, i.2))
  have T₅ : Task (fun i : Req × Word => a i + ((d i).1).length)
      (fun i => send ((d i).1, ((d i).2, i.2)))
      (fun i => send (tally (a i), ((d i).2, i.2))) := by
    simpa only [P1Batch.bval_eq_value, a, send_prod] using
      (P1Batch.countdown.on (fun i : Req × Word => (d i).1)).left (fun i => send ((d i).2, i.2))
  have h₆ : Easy (fun j : Tally × (Word × Word) => ((j.1, j.2.2), j.2.1)) := by fun_prop
  have T₆ := h₆.on (fun i : Req × Word => (tally (a i), ((d i).2, i.2)))
  have T₇ : Task (fun i : Req × Word => size (tally (a i)) + size (pre i))
      (fun i => send ((tally (a i), i.2), (d i).2))
      (fun i => send ((pre i, rest i), (d i).2)) := by
    simpa only [cutLists, tally_length, pre, rest, send_prod] using
      ((Computes.cut (X := Bool)).on (fun i : Req × Word => (tally (a i), i.2))).left
        (fun i => send (d i).2)
  have h₈ : Easy (fun j : (Word × Word) × Word => (j.2, j.1.2)) := by fun_prop
  have T₈ := h₈.on (fun i : Req × Word => ((pre i, rest i), (d i).2))
  have T₉ : Task (fun i : Req × Word => w i + ((d i).2).length)
      (fun i => send ((d i).2, rest i))
      (fun i => send (tally (w i), rest i)) := by
    simpa only [P1Batch.bval_eq_value, w, send_prod] using
      (P1Batch.countdown.on (fun i : Req × Word => (d i).2)).left (fun i => send (rest i))
  have T₁₀ : Task (fun i : Req × Word => size (tally (w i)) + size (field i))
      (fun i => send (tally (w i), rest i))
      (fun i => send (field i, post i)) := by
    simpa only [cutLists, tally_length, field, post] using
      (Computes.cut (X := Bool)).on (fun i : Req × Word => (tally (w i), rest i))
  have T₁₁ := (Easy.fst (X := Word) (Y := Word)).on (fun i => (field i, post i))
  have H := ((((((((((h₁.on (id : Req × Word → Req × Word)).compose T₂).compose T₃).compose T₄).compose T₅).compose T₆).compose
    T₇).compose T₈).compose T₉).compose T₁₀).compose T₁₁
  obtain ⟨C, hC⟩ := easy_clipped.length
  refine (H.bound (50 + 20 * C) ?_).conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  · intro i
    have hd := hC (bin i.2.length, i.1)
    have hbin := size_bin_linear i.2.length
    have haw : a i + w i ≤ i.2.length := clipped_end i.1 i.2
    have hp : (pre i).length ≤ a i := List.length_take_le _ _
    have hr : (rest i).length ≤ i.2.length := by
      simp only [rest, List.length_drop]
      omega
    have hf : (field i).length ≤ w i := List.length_take_le _ _
    have hpost : (post i).length ≤ i.2.length := by
      simp only [post, List.length_drop]
      omega
    change size (d i) ≤ C * size (bin i.2.length, i.1) at hd
    simp only [id_eq, size_prod, size_listBool, size_tally, tally_length] at hd ⊢
    simp only [size_listBool] at hbin
    have hb : C * (2 * (bin i.2.length).length + 1 +
        (2 * i.1.1.length + 1 + (2 * i.1.2.length + 1) + 1) + 1 + 1) ≤
        C * (2 * i.2.length + 3 + (2 * i.1.1.length + 1 + (2 * i.1.2.length + 1) + 1) + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hd hb ⊢
    omega
  · exact congrArg send (slice_clipped i.1 i.2)

end P1ChkFinal.SolFinal
