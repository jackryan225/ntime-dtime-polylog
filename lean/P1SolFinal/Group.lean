import P1SolFinal.SumFields
import P1ChkFinal.Checks

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

theorem fixedChunks_zero (w : Word) : fixedChunks 0 w = [] := by
  rw [fixedChunks, dite_eq_left (Or.inl rfl)]

theorem easy_fixedChunks : Easy (fun i : Tally × Word => fixedChunks i.1.length i.2) := by
  let valid (_ : Tally) (_ : Word) := True
  let a (u : Tally) (w : Word) := size (u, w)
  have h₀ : Task (fun i : {w // valid [] w} => a [] i.val)
      (fun i => send i.val) (fun i => send (fixedChunks 0 i.val)) := by
    have h := Task.const (send ([] : List Word)) (fun i : {w // valid [] w} => send i.val)
    refine (h.mono (b' := fun i => a [] i.val) (fun i => ?_)).conform
      (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
    · change size i.val ≤ size (([] : Tally), i.val)
      simp only [size_prod, size_nil]
      omega
    · rw [fixedChunks_zero]
  have h₁ := fixedChunks_task.on (fun i : {p : Unit × Tally × Word // valid (p.1 :: p.2.1) p.2.2} =>
    ⟨(i.val.1 :: i.val.2.1, i.val.2.2), by simp only [List.length_cons, Nat.zero_lt_succ]⟩)
  exact (Task.byList Word Unit (fun u w => send (fixedChunks u.length w)) a
    (D := valid) (p := send) h₀ h₁).on (fun i : Tally × Word => ⟨i, trivial⟩)

theorem fixedChunks_field_le (k : ℕ) (w : Word) :
    ∀ x ∈ fixedChunks k w, x.length ≤ k := by
  by_cases hk : k = 0
  · rw [hk, fixedChunks_zero]
    exact fun _ hx => False.elim (List.not_mem_nil hx)
  suffices h : ∀ n, ∀ w : Word, w.length = n → ∀ x ∈ fixedChunks k w, x.length ≤ k from h _ _ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw x hx
    subst n
    by_cases hn : w = []
    · rw [hn, fixedChunks_nil] at hx
      exact False.elim (List.not_mem_nil hx)
    rw [fixedChunks_step k w hk hn] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact h.symm ▸ List.length_take_le k w
    · refine ih _ ?_ _ rfl _ h
      have hp : 0 < w.length := List.length_pos_iff.mpr hn
      have hkp : 0 < k := Nat.pos_of_ne_zero hk
      rw [List.length_drop]
      omega

theorem fixedChunks_count (k : ℕ) (w : Word) :
    (fixedChunks k w).length * k ≤ w.length + k := by
  by_cases hk : k = 0
  · simp only [hk, Nat.mul_zero, Nat.zero_le]
  suffices h : ∀ n, ∀ w : Word, w.length = n → (fixedChunks k w).length * k ≤ w.length + k from h _ _ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw
    subst n
    by_cases hn : w = []
    · simp only [hn, fixedChunks_nil, List.length_nil, Nat.zero_mul, Nat.zero_le]
    rw [fixedChunks_step k w hk hn, List.length_cons, Nat.add_mul, Nat.one_mul]
    by_cases hkw : k ≤ w.length
    · have hp : 0 < w.length := List.length_pos_iff.mpr hn
      have hkp : 0 < k := Nat.pos_of_ne_zero hk
      have hdrop : (w.drop k).length < w.length := by rw [List.length_drop]; omega
      have h := ih _ hdrop (w.drop k) rfl
      rw [List.length_drop] at h
      omega
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_ge hkw), fixedChunks_nil, List.length_nil, Nat.zero_mul]
      omega

theorem fixedChunks_clip (k : ℕ) (w : Word) :
    fixedChunks (min k w.length) w = fixedChunks k w := by
  by_cases e : k ≤ w.length
  · rw [min_eq_left e]
  · by_cases hw : w = []
    · rw [hw, fixedChunks_nil, fixedChunks_nil]
    have hk : 0 < w.length := List.length_pos_iff.mpr hw
    have hk' : w.length ≤ k := Nat.le_of_not_ge e
    have hk'' : k ≠ 0 := by omega
    rw [min_eq_right hk', fixedChunks_step _ w (Nat.ne_of_gt hk) hw, fixedChunks_step k w hk'' hw,
      List.take_length, List.take_of_length_le hk', List.drop_eq_nil_of_le (le_refl w.length),
      List.drop_eq_nil_of_le hk', fixedChunks_nil, fixedChunks_nil]

theorem fixedChunks_sum (k n : ℕ) (w : Word) :
    ((fixedChunks k (w.take (n * k))).map Bits.value).sum =
      pre (fun t => Bits.value ((w.drop (t * k)).take k)) n := by
  induction n generalizing w with
  | zero =>
    simp only [Nat.zero_mul, List.take_zero, fixedChunks_nil, List.map_nil, List.sum_nil, pre_zero]
  | succ n ih =>
    by_cases hz : k = 0
    · simp only [hz, Nat.mul_zero, List.take_zero, fixedChunks_nil, List.map_nil, List.sum_nil,
        Bits.value_nil, pre, Finset.sum_const_zero]
    by_cases hw : w = []
    · simp only [hw, List.take_nil, fixedChunks_nil, List.map_nil, List.sum_nil, List.drop_nil,
        Bits.value_nil, pre, Finset.sum_const_zero]
    have hlen : 0 < w.length := List.length_pos_iff.mpr hw
    have hp : 0 < (n + 1) * k := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hz)
    have hprefix : w.take ((n + 1) * k) ≠ [] := by
      apply List.length_pos_iff.mp
      rw [List.length_take]
      exact lt_min hp hlen
    have hhead : (w.take ((n + 1) * k)).take k = w.take k := by
      rw [List.take_take, min_eq_left (by rw [Nat.add_mul, Nat.one_mul]; omega)]
    have htail : (w.take ((n + 1) * k)).drop k = (w.drop k).take (n * k) := by
      rw [List.drop_take, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
    have hpre : pre (fun t => Bits.value ((w.drop (t * k)).take k)) (n + 1) =
        Bits.value (w.take k) + pre (fun t => Bits.value (((w.drop k).drop (t * k)).take k)) n := by
      simp only [pre, Finset.sum_range_succ', Nat.zero_mul, List.drop_zero, List.drop_drop,
        Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [fixedChunks_step _ _ hz hprefix, List.map_cons, List.sum_cons, hhead, htail, ih, hpre]

/-- Compute a binary length while keeping both inputs. -/
theorem easy_lenPair {S : Type*} [Codec S] (hl : LenHyp) :
    Easy (fun i : S × Word => (bin i.2.length, i)) := by
  have e : Easy (fun i : S × Word => (i.2, i)) := by fun_prop
  have T := (hl.on (fun i : S × Word => i.2)).left (fun i => send i)
  apply Easy.of_bound (Task.compose (e.on (id : S × Word → S × Word)) T) 2
  intro i
  simp only [id_eq, size_prod, size_listBool, Nat.mul_add]
  omega

set_option maxHeartbeats 1000000 in
theorem easy_tallyWidth (hl : LenHyp) :
    Easy (fun i : Word × Word => (tally (min (Bits.value i.1) i.2.length), i.2)) := by
  let d : Word × Word → Word := fun i => smaller (i.1, bin i.2.length)
  have h₁ := easy_lenPair (S := Word) hl
  have e : Easy (fun p : Word × (Word × Word) => (smaller (p.2.1, p.1), p.2.2)) := by fun_prop
  have h₂ := h₁.compose e
  have T := (P1Batch.countdown.on d).left (fun i => send i.2)
  obtain ⟨C, hC⟩ := h₂.length
  refine Easy.of_bound (((h₂.on (id : Word × Word → Word × Word)).compose T).conform
    (fun _ => rfl) (fun _ => rfl) (fun i => ?_)) (C + 2) (fun i => ?_)
  · simp only [d, send_prod, P1Batch.bval_eq_value, smaller_eq, value_bin]
  · have hd := hC i
    have he : P1Batch.bval (d i) ≤ i.2.length := by
      change P1Batch.bval (smaller (i.1, bin i.2.length)) ≤ i.2.length
      rw [P1Batch.bval_eq_value, smaller_eq, value_bin]
      exact min_le_right _ _
    change size (d i, i.2) ≤ C * size i at hd
    simp only [id_eq, size_prod, size_listBool, Nat.add_mul] at hd ⊢
    omega

/-- Sum the full and truncated fields that are actually present in the requested interval. -/
def sumFields (i : Word × Word) : Word :=
  let k := min (Bits.value i.1) i.2.length
  wordSum (tally k, fixedChunks k i.2)

theorem sumFields_value (width : Word) (w : Word) :
    Bits.value (sumFields (width, w)) = ((fixedChunks (Bits.value width) w).map Bits.value).sum := by
  unfold sumFields
  rw [wordSum_value (tally _) _ (fun x hx => by rw [tally_length]; exact fixedChunks_field_le _ _ _ hx)]
  rw [fixedChunks_clip]

set_option maxHeartbeats 1200000 in
theorem easy_sumFields (hl : LenHyp) : Easy sumFields := by
  let k : Word × Word → ℕ := fun i => min (Bits.value i.1) i.2.length
  let groups : Word × Word → Tally × List Word := fun i => (tally (k i), fixedChunks (k i) i.2)
  have h₁ := easy_tallyWidth hl
  have e : Easy (fun i : Tally × Word => (i.1, fixedChunks i.1.length i.2)) :=
    Easy.fst.pair easy_fixedChunks
  have h₂ := h₁.compose e
  have h₂' : Easy groups := by simpa only [groups, k, tally_length] using h₂
  obtain ⟨C, hC⟩ := h₂'.length
  refine Easy.of_bound ((h₂'.on (id : Word × Word → Word × Word)).compose ((wordSum_task hl).on groups))
    (C + 20) (fun i => ?_)
  have hb := fixedChunks_count (k i) i.2
  have hk : k i ≤ i.2.length := min_le_right _ _
  have hlen := hC i
  change size (groups i) ≤ C * size i at hlen
  have hCount := length_le_size (groups i).2
  change (groups i).2.length ≤ size (groups i).2 at hCount
  have hCount' : (groups i).2.length ≤ C * size i := by
    rw [size_prod] at hlen
    omega
  have hk' : (fixedChunks (k i) i.2).length ≤ 2 * i.2.length := by
    by_cases hz : k i = 0
    · rw [hz, fixedChunks_zero, List.length_nil]
      exact Nat.zero_le _
    · have hp : 0 < k i := Nat.pos_of_ne_zero hz
      have he := Nat.le_mul_of_pos_right (fixedChunks (k i) i.2).length hp
      omega
  have hh : (groups i).2.length * (4 * (groups i).1.length + 4) ≤ 16 * i.2.length := by
    change (fixedChunks (k i) i.2).length * (4 * (tally (k i)).length + 4) ≤ _
    rw [tally_length, Nat.mul_add, Nat.mul_left_comm]
    omega
  simp only [id_eq, Nat.add_mul]
  have hsz : i.2.length ≤ size i := by simp only [size_prod, size_listBool]; omega
  omega

end P1ChkFinal.SolFinal
