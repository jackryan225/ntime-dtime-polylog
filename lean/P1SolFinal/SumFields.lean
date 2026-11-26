import P1SolFinal.FixedChunks
import P1SolFinal.Prepare
import P1Batch.Moves

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

abbrev Limb := Tally × Word
abbrev SumState := Limb × Word

def limbAdd (i : Word × Limb) : Bool × Limb :=
  let t := cutLists (i.2.1, Bits.add (i.2.2, i.1))
  (!numEq (t.2, []), (i.2.1, t.1))

theorem easy_limbAdd : Easy limbAdd := by
  let c : Word × Limb → Word × Word := fun i => cutLists (i.2.1, Bits.add (i.2.2, i.1))
  have hc : Easy c := by unfold c; fun_prop
  have hw : Easy (fun i : Word × Limb => i.2.1) := by fun_prop
  exact ((((hc.sndCompose.pair (Easy.const [])).compose easy_numEq).compose easy_bnot).pair
    (hw.pair hc.fstCompose))

def addCarry (b : Bool) (l : Word) : Word := bif b then true :: l else l

theorem carry_task {X : Type*} (b : X → Bool) (l : X → Word) :
    Task (fun _ => 0) (fun x => .fork (send (b x)) (send (l x)))
      (fun x => send (addCarry (b x) (l x))) := by
  apply Task.control b
  · refine Task.self.conform (fun _ => rfl) (fun _ => rfl) ?_
    intro x
    simp only [addCarry, x.property, Bool.cond_false]
  · have h := Task.supply (Tree.atom true) (fun x : {x // b x = true} => send (l x.val))
    refine h.conform (fun _ => rfl) (fun _ => rfl) ?_
    intro x
    simp only [addCarry, x.property, Bool.cond_true, send_cons]
    rfl

def sumStep (s : SumState) (w : Word) : SumState :=
  let a := limbAdd (w, s.1)
  (a.2, addCarry a.1 s.2)

set_option maxHeartbeats 1000000 in
theorem sumStep_task :
    Task (fun i : Word × SumState => size i.1 + size i.2.1 + 1)
      (fun i => send i) (fun i => send (sumStep i.2 i.1)) := by
  let x : Word × SumState → Word := Prod.fst
  let s : Word × SumState → Limb := fun i => i.2.1
  let l : Word × SumState → Word := fun i => i.2.2
  let f := fun i => limbAdd (x i, s i)
  have T₁ := P1Batch.assocL (fun i => send (x i)) (fun i => send (s i)) (fun i => send (l i))
  have T₂ := (easy_limbAdd.on (fun i => (x i, s i))).left (fun i => send (l i))
  have T₃ := P1Batch.assocR (fun i => send (f i).1) (fun i => send (f i).2) (fun i => send (l i))
  have T₄ := P1Batch.swap12 (fun i => send (f i).1) (fun i => send (f i).2) (fun i => send (l i))
  have T₅ := (carry_task (fun i => (f i).1) l).right (fun i => send (f i).2)
  have H := ((((T₁.compose T₂).compose T₃).compose T₄).compose T₅)
  obtain ⟨C, hC⟩ := easy_limbAdd.length
  refine H.bound (10 + 10 * C) fun i => ?_
  have hs := hC (x i, s i)
  change size (f i) ≤ C * size (x i, s i) at hs
  simp only [size_prod] at hs
  change size (x i) + size (x i, s i) + size (f i).1 +
    (size (f i).1 + size (f i).2) + (size (f i).2 + 0) + 1 ≤
    (10 + 10 * C) * (size (x i) + size (s i) + 1 + 1)
  simp only [size_prod, Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hs ⊢
  omega

def sumValue (s : SumState) : ℕ := Bits.value s.1.2 + 2 ^ s.1.1.length * s.2.length

theorem sumStep_ruler (s : SumState) (w : Word) : (sumStep s w).1.1 = s.1.1 := rfl

theorem sumStep_lowLength (s : SumState) (w : Word) (h : s.1.2.length = s.1.1.length) :
    (sumStep s w).1.2.length = s.1.1.length := by
  simp only [sumStep, limbAdd, cutLists, List.length_take, Bits.add_length, h]
  omega

theorem sumStep_value (s : SumState) (w : Word) (h : s.1.2.length = s.1.1.length)
    (hw : w.length ≤ s.1.1.length) :
    sumValue (sumStep s w) = sumValue s + Bits.value w := by
  let k := s.1.1.length
  let t := Bits.add (s.1.2, w)
  let lo := t.take k
  let hi := t.drop k
  have hlo : lo.length = k := sumStep_lowLength s w h
  have ht := Bits.value_append lo hi
  change Bits.value (t.take k ++ t.drop k) = Bits.value lo + 2 ^ lo.length * Bits.value hi at ht
  rw [List.take_append_drop, hlo] at ht
  have hv := Bits.add_val s.1.2 w
  change Bits.value t = _ at hv
  have hs := Bits.value_lt s.1.2
  have hwb := (Bits.value_lt w).trans_le (Nat.pow_le_pow_right (by decide) hw)
  change Bits.value w < 2 ^ k at hwb
  rw [h] at hs
  change Bits.value s.1.2 < 2 ^ k at hs
  have hhi : Bits.value hi ≤ 1 := by
    by_contra! hb
    have hh := Nat.mul_le_mul_left (2 ^ k) (show 2 ≤ Bits.value hi by omega)
    rw [Nat.mul_comm (2 ^ k) 2] at hh
    omega
  change Bits.value lo + 2 ^ k * (addCarry (!numEq (hi, [])) s.2).length =
    Bits.value s.1.2 + 2 ^ k * s.2.length + Bits.value w
  rw [numEq_eq, Bits.value_nil]
  by_cases hz : Bits.value hi = 0
  · simp only [hz, decide_true, Bool.not_true, addCarry, Bool.cond_false, Nat.mul_zero, Nat.add_zero] at ht ⊢
    omega
  · have h₁ : Bits.value hi = 1 := by omega
    simp only [h₁, show decide ((1 : ℕ) = 0) = false from rfl, Bool.not_false, addCarry,
      Bool.cond_true, List.length_cons, Nat.mul_add, Nat.mul_one] at ht ⊢
    omega

def sumFold (r : Tally) (l : List Word) : SumState :=
  l.foldl sumStep ((r, fill false r), [])

theorem sumFold_props (r : Tally) (l : List Word) (hl : ∀ w ∈ l, w.length ≤ r.length) :
    (sumFold r l).1.1 = r ∧ (sumFold r l).1.2.length = r.length ∧
      sumValue (sumFold r l) = (l.map Bits.value).sum := by
  have helper (s : SumState) (l : List Word) (hs : s.1.1 = r) (hlo : s.1.2.length = r.length)
      (hl : ∀ w ∈ l, w.length ≤ r.length) :
      (l.foldl sumStep s).1.1 = r ∧ (l.foldl sumStep s).1.2.length = r.length ∧
        sumValue (l.foldl sumStep s) = sumValue s + (l.map Bits.value).sum := by
    induction l generalizing s with
    | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero, hs, hlo, and_self]
    | cons a t ih =>
      have hw : a.length ≤ r.length := hl a List.mem_cons_self
      have h₁ : (sumStep s a).1.1 = r := (sumStep_ruler s a).trans hs
      have h₂ : (sumStep s a).1.2.length = r.length := (sumStep_lowLength s a (hlo.trans (congrArg List.length hs.symm))).trans
        (congrArg List.length hs)
      obtain ⟨e₁, e₂, e₃⟩ := ih (sumStep s a) h₁ h₂ (fun w e => hl w (List.mem_cons_of_mem _ e))
      rw [List.foldl_cons, List.map_cons, List.sum_cons]
      exact ⟨e₁, e₂, by
        rw [e₃, sumStep_value s a (by rw [hlo, hs]) (by rwa [hs]), Nat.add_assoc]⟩
  have h := helper ((r, fill false r), []) l rfl (by simp only [fill_eq, List.length_replicate]) hl
  simpa only [sumFold, sumValue, fill_eq, Bits.zeroes, List.length_nil, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add] using h

def sumCost (s : SumState) (w : Word) : ℕ := size w + size s.1 + 1

theorem sumWalk_bound (r : Tally) (l : List Word) (s : SumState)
    (hr : s.1.1 = r) (hl : s.1.2.length = r.length) :
    P1Batch.walkCost sumCost sumStep s l ≤ costSum size l + l.length * (4 * r.length + 4) := by
  induction l generalizing s with
  | nil => simp only [P1Batch.walkCost, costSum, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons a l ih =>
    have h₁ : (sumStep s a).1.1 = r := (sumStep_ruler s a).trans hr
    have h₂ : (sumStep s a).1.2.length = r.length := by rw [sumStep_lowLength s a (by rwa [hr]), hr]
    have hh := ih (sumStep s a) h₁ h₂
    simp only [P1Batch.walkCost, sumCost, size_prod, size_tally, size_listBool, hr, hl,
      costSum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem sumFold_carries (r : Tally) (l : List Word) : (sumFold r l).2.length ≤ l.length := by
  have aux (s : SumState) : (l.foldl sumStep s).2.length ≤ s.2.length + l.length := by
    induction l generalizing s with
    | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero, le_refl]
    | cons a l ih =>
      have h := ih (sumStep s a)
      have he : (sumStep s a).2.length ≤ s.2.length + 1 := by
        unfold sumStep addCarry
        cases e : (limbAdd (a, s.1)).1 <;>
          simp only [e, Bool.cond_false, Bool.cond_true, List.length_cons] <;> omega
      simp only [List.foldl_cons, List.length_cons]
      omega
  simpa only [sumFold, List.length_nil, Nat.zero_add] using aux ((r, fill false r), [])

def wordSum (i : Tally × List Word) : Word :=
  let r := sumFold i.1 i.2
  r.1.2 ++ bin r.2.length

theorem wordSum_value (r : Tally) (l : List Word) (hl : ∀ w ∈ l, w.length ≤ r.length) :
    Bits.value (wordSum (r, l)) = (l.map Bits.value).sum := by
  obtain ⟨h₁, h₂, h₃⟩ := sumFold_props r l hl
  simp only [wordSum, Bits.value_append, h₂, value_bin]
  simpa only [sumValue, h₁] using h₃

set_option maxHeartbeats 1500000 in
/-- The folded low limb has fixed width, and each overflow is appended to a list in constant time. -/
theorem wordSum_task (hl : LenHyp) :
    Computes (fun i : Tally × List Word => size i + i.2.length * (4 * i.1.length + 4)) wordSum := by
  let I := Tally × List Word
  let init : I → SumState := fun i => ((i.1, fill false i.1), [])
  let st : I → SumState := fun i => sumFold i.1 i.2
  have h₁ : Easy (fun i : I => (i.2, init i)) := by unfold init; fun_prop
  have T₁ := h₁.on (id : I → I)
  have step : Task (fun p : Word × SumState × Unit => sumCost p.2.1 p.1)
      (fun p => .fork (send p.1) (send p.2.1)) (fun p => send (sumStep p.2.1 p.1)) :=
    sumStep_task.on (fun p : Word × SumState × Unit => (p.1, p.2.1))
  have T₂' := (P1Batch.foldLeftS (fun (_ : Unit) (w : Word) => send w)
    (fun (_ : Unit) (s : SumState) => send s)
    (fun (_ : Unit) => sumStep) (fun (_ : Unit) => sumCost) step).on
      (fun i : I => (i.2, init i, ()))
  have T₂ : Task (fun i : I => P1Batch.walkCost sumCost sumStep (init i) i.2 + size i.2)
      (fun i => send (i.2, init i)) (fun i => send (st i)) := by
    simpa only [Task.forest_send, send_prod, size, init, st, sumFold] using T₂'
  have T₃' := (hl.on (fun i : I => (st i).2)).right (fun i => send (st i).1)
  have T₃ : Task (fun i : I => size (st i).1 + (st i).2.length)
      (fun i => send (st i)) (fun i => send ((st i).1, bin (st i).2.length)) := by
    simpa only [send_prod, size] using T₃'
  have e₄ : Easy (fun j : Limb × Word => j.1.2 ++ j.2) := by fun_prop
  have T₄ := e₄.on (fun i : I => ((st i).1, bin (st i).2.length))
  have T := (((T₁.compose T₂).compose T₃).compose T₄)
  refine T.bound 15 fun i => ?_
  have hwalk := sumWalk_bound i.1 i.2 (init i) rfl (by simp only [init, fill_eq, List.length_replicate])
  have hcarry := sumFold_carries i.1 i.2
  have hlow (l : List Word) (s : SumState) (hr : s.1.1 = i.1) (hs : s.1.2.length = i.1.length) :
      (l.foldl sumStep s).1.1 = i.1 ∧ (l.foldl sumStep s).1.2.length = i.1.length := by
    induction l generalizing s with
    | nil => exact ⟨hr, hs⟩
    | cons a l ih =>
      exact ih (sumStep s a) (hr : (sumStep s a).1.1 = i.1)
        ((sumStep_lowLength s a (by rwa [hr])).trans (congrArg List.length hr))
  obtain ⟨hR, hL⟩ := hlow i.2 (init i) rfl (by simp only [init, fill_eq, List.length_replicate])
  change (st i).1.1 = i.1 at hR
  change (st i).1.2.length = i.1.length at hL
  change (st i).2.length ≤ i.2.length at hcarry
  have hbin := size_bin_linear (st i).2.length
  have hc := costSum_le_length_size i.2
  have hs : size (st i).1 = 4 * i.1.length + 3 := by
    change size ((st i).1.1, (st i).1.2) = _
    simp only [size_prod, size_tally, size_listBool, hR, hL]
    omega
  have hi : size i = size i.1 + size i.2 + 1 := rfl
  change size i + (P1Batch.walkCost sumCost sumStep (init i) i.2 + size i.2) +
    (size (st i).1 + (st i).2.length) + size ((st i).1, bin (st i).2.length) + 1 ≤
    15 * (size i + i.2.length * (4 * i.1.length + 4) + 1)
  simp only [hi, size_prod, hs, size_tally]
  omega

end P1ChkFinal.SolFinal
