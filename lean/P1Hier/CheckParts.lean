import P1Hier.ColPhase

/-!
# P1Hier.CheckParts: `check_task` from four phase tasks

`Check c y T τ` = `lenB && (tabB && (chainB && colsB))` (`check_bool`). Each phase is a stack task;
later phases run only when the earlier ones accept, so their budgets may use the earlier facts
(`|τ| ≤ T + 1` makes the row loops cost `(T+1)·(table)`, and rows in the table bound `size τ`).

PROVED here: `keep`, `seqAnd` (short-circuit sequencing with budgets), `check_bool`,
`check_task_of_phases` (the assembly).
PROVED: the four phase tasks `len_task`, `tab_task` (TabPhase), `chain_task`, `cols_task`
(`ColPhase.cols_core`: one sweep over the tapes, each tape checked by the stack program of
`TapeLoop.tape_task`).
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Sequencing with short circuit -/

/-- Compute a bit and keep the input. -/
theorem keep {X : Type*} {p : X → Tree} {a : X → ℕ} {b : X → Bool}
    (h : Task a p (fun x => send (b x))) :
    Task (fun x => (p x).count + a x) p (fun x => .fork (.atom (b x)) (p x)) :=
  (Task.copy p).compose (Task.left h p)

/-- `b₁ && b₂`, where `b₂` is computed only when `b₁` holds. -/
theorem seqAnd {X : Type*} {p : X → Tree} {a₁ a₂ : X → ℕ} {b₁ b₂ : X → Bool}
    (h₁ : Task a₁ p (fun x => send (b₁ x)))
    (h₂ : Task (fun x : {x // b₁ x = true} => a₂ x.val) (fun x => p x.val)
      (fun x => send (b₂ x.val))) :
    Task (fun x => ((p x).count + a₁ x) + ((p x).count + a₂ x)) p
      (fun x => send (b₁ x && b₂ x)) := by
  have hk := keep h₁
  have hc : Task (fun x => (p x).count + a₂ x) (fun x => Tree.fork (Tree.atom (b₁ x)) (p x))
      (fun x => send (b₁ x && b₂ x)) := by
    apply Task.control b₁
    · have h0 := Task.const (send false) (fun x : {x // b₁ x = false} => p x.val)
      refine (Task.mono h0 (b' := fun x : {x // b₁ x = false} => (p x.val).count + a₂ x.val)
        (fun x => by omega)).conform (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      simp [x.property]
    · refine (Task.mono h₂ (b' := fun x : {x // b₁ x = true} => (p x.val).count + a₂ x.val)
        (fun x => by omega)).conform (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      simp [x.property]
  exact hk.compose hc

/-! ## The four phases -/

abbrev CIn := MCode × List Bool × ℕ × List Entry

def lenB (i : CIn) : Bool := decide (i.2.2.2.length ≤ i.2.2.1 + 1)

open Classical in
noncomputable def tabB (i : CIn) : Bool := decide (∀ e ∈ i.2.2.2, e ∈ i.1.table)

def chainB (i : CIn) : Bool := chainOK i.1.init i.2.2.2

open Classical in
noncomputable def colsB (i : CIn) : Bool :=
  decide (∀ k < i.1.nK, colOK (i.1.start i.2.1 k) (col k i.2.2.2) = true)

open Classical in
theorem check_bool (i : CIn) :
    decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2) = (lenB i && (tabB i && (chainB i && colsB i))) := by
  rw [Bool.eq_iff_iff]
  simp only [lenB, tabB, chainB, colsB, decide_eq_true_eq, Bool.and_eq_true]
  exact Iff.rfl

/-- Phase 1: `|τ| ≤ T + 1`, linear. -/
theorem len_task : Task (fun i : CIn => (send i).count) send (fun i => send (lenB i)) := by
  have hT : Easy (fun i : CIn => i.2.2.1) :=
    Easy.fstCompose (Easy.sndCompose (Easy.sndCompose easy_id))
  have hτ : Easy (fun i : CIn => i.2.2.2) :=
    Easy.sndCompose (Easy.sndCompose (Easy.sndCompose easy_id))
  have hR : Easy (fun i : CIn => () :: List.replicate i.2.2.1 ()) :=
    ((Easy.const ()).pair (hT.compose easy_tally)).compose Easy.cons
  have hs : Easy (fun i : CIn => !Code.Iter.small (() :: List.replicate i.2.2.1 (), i.2.2.2)) :=
    ((hR.pair hτ).compose Code.Iter.small_easy).compose Code.Iter.negate
  have e : (fun i : CIn => !Code.Iter.small (() :: List.replicate i.2.2.1 (), i.2.2.2)) = lenB := by
    funext i
    simp only [Code.Iter.small, lenB, List.length_cons, List.length_replicate]
    by_cases h : i.2.2.2.length ≤ i.2.2.1 + 1
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  rw [e] at hs
  exact hs

/-- OPEN. Phase 2: every row is a table entry. Per row: guard `size e ≤ size table`, then a
membership scan with one tree comparison per entry. -/
def tabBudget (i : CIn) : ℕ := (size i.1 + 1) ^ 2 * (i.2.2.1 + 1) + (send i).count

theorem size_table_le (c : MCode) : size c.table ≤ size c := by
  change size c.table ≤ size (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)
  simp only [size_prod]
  omega

theorem rowCost_le (tab : List Entry) (e : Entry) :
    rowCost tab e ≤ 5 * size e + 42 * (size tab + 1) ^ 2 := by
  simp only [rowCost, memBudget, size_prod, size_bit]
  nlinarith

theorem costSum_rowCost_le (tab : List Entry) (τ : List Entry) :
    costSum (rowCost tab) τ ≤ 5 * size τ + τ.length * (42 * (size tab + 1) ^ 2) := by
  induction τ with
  | nil => simp
  | cons e l ih =>
    simp only [costSum_cons, size_cons, List.length_cons]
    have := rowCost_le tab e
    nlinarith

open Classical in
/-- Phase 2: every row is a table entry (`TabPhase.allMemTask`). -/
theorem tab_task : Task (fun i : {i : CIn // lenB i = true} => tabBudget i.val)
    (fun i => send i.val) (fun i => send (tabB i.val)) := by
  have hcode : Easy (fun c : MCode => (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)) :=
    (Task.self (b := size) (p := send)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have htable : Easy (fun i : CIn => i.1.table) :=
    Easy.fst.compose (Easy.sndCompose (Easy.sndCompose (Easy.sndCompose (Easy.sndCompose
      (Easy.sndCompose hcode)))))
  have hτ : Easy (fun i : CIn => i.2.2.2) :=
    Easy.sndCompose (Easy.sndCompose (Easy.sndCompose easy_id))
  have hre : Easy (fun i : CIn => (i.2.2.2, i.1.table, true)) := hτ.pair (htable.pair (Easy.const true))
  have h1 := Task.on hre (fun x : {i : CIn // lenB i = true} => x.val)
  have h2 := Task.on allMemTask (fun x : {i : CIn // lenB i = true} => (x.val.2.2.2, x.val.1.table, true))
  have h3 := Task.on (Easy.snd (X := List Entry) (Y := Bool))
    (fun x : {i : CIn // lenB i = true} => (x.val.1.table, true && decide (∀ e ∈ x.val.2.2.2, e ∈ x.val.1.table)))
  have h123 := (h1.compose h2).compose h3
  refine (h123.bound 100 (b' := fun x : {i : CIn // lenB i = true} => tabBudget x.val) (fun x => ?_)).conform
    (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
  · rcases x with ⟨⟨c, y, T, τ⟩, hx⟩
    simp only [lenB, decide_eq_true_eq] at hx
    have hc := costSum_rowCost_le c.table τ
    have ht := size_table_le c
    have hsq : (size c.table + 1) ^ 2 ≤ (size c + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hlen : τ.length * (42 * (size c.table + 1) ^ 2) ≤ (T + 1) * (42 * (size c + 1) ^ 2) :=
      Nat.mul_le_mul hx (Nat.mul_le_mul_left _ hsq)
    have key : costSum (rowCost c.table) τ ≤ 5 * size τ + 42 * ((size c + 1) ^ 2 * (T + 1)) := by
      have : (T + 1) * (42 * (size c + 1) ^ 2) = 42 * ((size c + 1) ^ 2 * (T + 1)) := by ring
      omega
    have hsend : (send (c, y, T, τ)).count = size c + (size y + (size T + size τ + 1) + 1) + 1 := by
      change size (c, y, T, τ) = _; simp only [size_prod]
    simp only [tabBudget, size_prod, size_bit]
    rw [hsend]
    generalize costSum (rowCost c.table) τ = Cs at *
    generalize (size c + 1) ^ 2 * (T + 1) = P at *
    omega
  · simp [tabB]

/-- Phase 3: the states chain; it is an equality of two lists of `ℕ ⊕ Bool` (`chainOK_eq`),
tested through the prefix-free bit code `serL serRes`. Linear. -/
theorem chain_task : Task (fun i : CIn => (send i).count) send (fun i => send (chainB i)) := by
  have hcode : Easy (fun c : MCode => (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)) :=
    (Task.self (b := size) (p := send)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hinit : Easy (fun i : CIn => i.1.init) :=
    Easy.fst.compose (Easy.fstCompose (Easy.sndCompose (Easy.sndCompose (Easy.sndCompose
      (Easy.sndCompose hcode)))))
  have hτ : Easy (fun i : CIn => i.2.2.2) :=
    Easy.sndCompose (Easy.sndCompose (Easy.sndCompose easy_id))
  have hL1 : Easy (fun i : CIn => (Sum.inl i.1.init : ℕ ⊕ Bool) :: i.2.2.2.map (fun e => e.2.2)) :=
    ((hinit.compose (Easy.leftSum (Y := Bool))).pair
      (easy_map hτ (Easy.sndCompose Easy.snd))).compose Easy.cons
  have hL2 : Easy (fun i : CIn =>
      i.2.2.2.map (fun e => (Sum.inl e.1 : ℕ ⊕ Bool)) ++ [Sum.inr true]) :=
    easy_append (easy_map hτ (Easy.fst.compose (Easy.leftSum (Y := Bool)))) (Easy.const _)
  have h : Easy (fun i : CIn =>
      decide (serL serRes ((Sum.inl i.1.init : ℕ ⊕ Bool) :: i.2.2.2.map (fun e => e.2.2)) =
        serL serRes (i.2.2.2.map (fun e => (Sum.inl e.1 : ℕ ⊕ Bool)) ++ [Sum.inr true]))) :=
    ((hL1.compose (easy_serL easy_serRes)).pair (hL2.compose (easy_serL easy_serRes))).compose
      easy_eqBits
  have e : (fun i : CIn =>
      decide (serL serRes ((Sum.inl i.1.init : ℕ ⊕ Bool) :: i.2.2.2.map (fun e => e.2.2)) =
        serL serRes (i.2.2.2.map (fun e => (Sum.inl e.1 : ℕ ⊕ Bool)) ++ [Sum.inr true]))) =
      chainB := by
    funext i
    rw [chainB, chainOK_eq, decide_eq_decide]
    exact (serL_injective pf_serRes).eq_iff
  rw [e] at h
  exact h

theorem goodIn_of {i : CIn} (h : lenB i = true ∧ tabB i = true) : GoodIn i := by
  obtain ⟨h1, h2⟩ := h
  simp only [lenB, tabB, decide_eq_true_eq] at h1 h2
  exact ⟨h1, h2⟩

/-- Phase 4: `nK` column passes (peel the first cell of every row, then simulate one tape
on two stacks); rows are table entries here, so each pass costs `O((T+1)·size c)`. -/
theorem cols_task : Task (fun i : {i : CIn // lenB i = true ∧ tabB i = true} => checkBudget i.val)
    (fun i => send i.val) (fun i => send (colsB i.val)) := by
  have h := Task.on cols_core (fun i : {i : CIn // lenB i = true ∧ tabB i = true} =>
    (⟨i.val, goodIn_of i.property⟩ : Gh))
  refine h.conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  congr 1

/-! ## Assembly -/

theorem size_cin (i : CIn) : size i ≤ 3 * ((size i.1 + 1) ^ 2 * (i.2.1.length + i.2.2.1 + 1) +
    size i.2.2.2) + 10 := by
  rcases i with ⟨c, y, T, τ⟩
  have hy : size y = 2 * y.length + 1 := by
    induction y with
    | nil => rfl
    | cons b y ih => simp only [size_cons, size_bit, ih, List.length_cons]; omega
  have hT : size T = 2 * T + 1 := by
    change size (List.replicate T ()) = _
    induction T with
    | zero => rfl
    | succ T ih =>
      have hu : size () = 1 := rfl
      simp only [List.replicate_succ, size_cons, ih, hu]; omega
  simp only [size_prod, hy, hT]
  have h1 : y.length + T + 1 ≤ (size c + 1) ^ 2 * (y.length + T + 1) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : size c + 1 ≤ (size c + 1) ^ 2 * (y.length + T + 1) := by
    have : size c + 1 ≤ (size c + 1) ^ 2 := by nlinarith
    exact this.trans (Nat.le_mul_of_pos_right _ (by omega))
  omega

end P1Hier
