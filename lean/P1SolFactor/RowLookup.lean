import P1ProgEng.Lib
import Mathlib.Data.Nat.Bitwise

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng

/-- Registers used by a row lookup. All other registers are preserved. -/
structure Ports where
  table : ℕ
  output : ℕ
  index : ℕ
  table_ne_output : table ≠ output
  table_ne_index : table ≠ index
  output_ne_index : output ≠ index

variable {A : Type} (p : Ports)

/-- Extend any register assignment with the three fields used by a row lookup. -/
def regs (base : Reg A) (table output index : List A) : Reg A := fun j =>
  if j = p.table then table else if j = p.output then output else if j = p.index then index else base j

@[simp] theorem regs_table (base : Reg A) (t o i : List A) : regs p base t o i p.table = t := by
  simp only [regs, ite_true]

@[simp] theorem regs_output (base : Reg A) (t o i : List A) : regs p base t o i p.output = o := by
  simp only [regs, ite_eq_right p.table_ne_output.symm, ite_true]

@[simp] theorem regs_index (base : Reg A) (t o i : List A) : regs p base t o i p.index = i := by
  simp only [regs, ite_eq_right p.table_ne_index.symm, ite_eq_right p.output_ne_index.symm, ite_true]

theorem write_table (base : Reg A) (t o i t' : List A) :
    Function.update (regs p base t o i) p.table t' = regs p base t' o i := by
  funext j
  by_cases hj : j = p.table
  · subst j
    simp only [Function.update_self, regs_table]
  · simp only [Function.update_of_ne hj, regs, ite_eq_right hj]

theorem write_output (base : Reg A) (t o i o' : List A) :
    Function.update (regs p base t o i) p.output o' = regs p base t o' i := by
  funext j
  by_cases hj : j = p.output
  · subst j
    simp only [Function.update_self, regs_output]
  · simp only [Function.update_of_ne hj, regs, ite_eq_right hj]

theorem write_index (base : Reg A) (t o i i' : List A) :
    Function.update (regs p base t o i) p.index i' = regs p base t o i' := by
  funext j
  by_cases hj : j = p.index
  · subst j
    simp only [Function.update_self, regs_index]
  · simp only [Function.update_of_ne hj, regs, ite_eq_right hj]

theorem regs_eq (r : Reg A) {t o i : List A}
    (ht : r p.table = t) (ho : r p.output = o) (hi : r p.index = i) : regs p r t o i = r := by
  funext j
  by_cases htable : j = p.table
  · subst j
    rw [regs_table, ht]
  by_cases hout : j = p.output
  · subst j
    rw [regs_output, ho]
  by_cases hindex : j = p.index
  · subst j
    rw [regs_index, hi]
  simp only [regs, ite_eq_right htable, ite_eq_right hout, ite_eq_right hindex]

private theorem pop_table {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.pop p.table) (regs p base (x :: t) o i) (regs p base t o i) 1 :=
  (Runs.pop p.table).congr_out (by rw [regs_table, List.tail_cons, write_table])

private theorem push_table {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.push p.table x) (regs p base t o i) (regs p base (x :: t) o i) 1 :=
  (Runs.push p.table x).congr_out (by rw [regs_table, write_table])

private theorem push_output {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.push p.output x) (regs p base t o i) (regs p base t (x :: o) i) 1 :=
  (Runs.push p.output x).congr_out (by rw [regs_output, write_output])

private theorem pop_index {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.pop p.index) (regs p base t o (x :: i)) (regs p base t o i) 1 :=
  (Runs.pop p.index).congr_out (by rw [regs_index, List.tail_cons, write_index])

private theorem push_index {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.push p.index x) (regs p base t o i) (regs p base t o (x :: i)) 1 :=
  (Runs.push p.index x).congr_out (by rw [regs_index, write_index])

private theorem againOne {Γ : Scope A} {f g : Prog A} {r r' : Reg A} {n : ℕ}
    (h : Runs (f :: Γ) f r r' n) : Runs (g :: f :: Γ) (.again 1) r r' (n + 1) := by
  obtain ⟨k, hr, hk⟩ := h
  exact ⟨1 + k, .again rfl hr, by omega⟩

variable [DecidableEq A] (mark : A)

/-- Copy the first row, unwinding the calls to restore the original stack and write the copy in order. -/
def copyStep : Option A → Prog A
  | none => .pass
  | some x => if x = mark then .pass else
      .join (.pop p.table) (.join (.again 0) (.join (.push p.table x) (.push p.output x)))

def copyBody : Prog A := .look p.table (copyStep p mark)

private theorem runCopyBody {Γ : Scope A} (base : Reg A) (tail index : List A) :
    ∀ (row output : List A), mark ∉ row →
      Runs (copyBody p mark :: Γ) (copyBody p mark)
        (regs p base (row ++ mark :: tail) output index)
        (regs p base (row ++ mark :: tail) (row ++ output) index) (12 * row.length + 2) := by
  intro row
  induction row with
  | nil =>
    intro output _
    refine Runs.look' (c := copyStep p mark) (o := some mark) (by simp only [List.nil_append, regs_table,
      List.head?_cons]) ?_
    simpa only [copyStep, ite_eq_left rfl, ite_true, List.nil_append, List.length_nil,
      Nat.mul_zero, Nat.zero_add] using
      (Runs.pass (Γ := copyBody p mark :: Γ) (r := regs p base (mark :: tail) output index))
  | cons x row ih =>
    intro output hrow
    have hx : x ≠ mark := by
      intro e
      exact hrow (e ▸ List.mem_cons_self)
    have ht : mark ∉ row := fun h => hrow (List.mem_cons_of_mem x h)
    have hrecurse := Runs.again0 (ih output ht)
    have hstep := (pop_table p base x (row ++ mark :: tail) output index).join
      (hrecurse.join ((push_table p base x (row ++ mark :: tail) (row ++ output) index).join
        (push_output p base x (x :: (row ++ mark :: tail)) (row ++ output) index)))
    have hlook := Runs.look' (c := copyStep p mark) (o := some x)
      (show ((regs p base ((x :: row) ++ mark :: tail) output index) p.table).head? = some x by
        simp only [regs_table, List.cons_append, List.head?_cons])
      (by simpa only [copyStep, ite_eq_right hx, List.cons_append] using hstep)
    exact hlook.mono (by simp only [List.length_cons]; omega)

/-- Copy a delimited row, restoring the entire source. -/
theorem copy_runs {Γ : Scope A} (base : Reg A) (row tail output index : List A) (h : mark ∉ row) :
    Runs Γ (.tie (copyBody p mark)) (regs p base (row ++ mark :: tail) output index)
      (regs p base (row ++ mark :: tail) (row ++ output) index) (12 * row.length + 3) := by
  exact Runs.tie (runCopyBody p mark base tail index row output h)

/-- Transfer the first row including its delimiter, preserving order on the output stack. -/
def moveRowStep : Option A → Prog A
  | none => .pass
  | some x => if x = mark then .join (.pop p.table) (.push p.output x) else
      .join (.pop p.table) (.join (.again 0) (.push p.output x))

def moveRowBody : Prog A := .look p.table (moveRowStep p mark)

def moveRow : Prog A := .tie (moveRowBody p mark)

private theorem runMoveRowBody {Γ : Scope A} (base : Reg A) (tail output index : List A) :
    ∀ row, mark ∉ row →
      Runs (moveRowBody p mark :: Γ) (moveRowBody p mark)
        (regs p base (row ++ mark :: tail) output index)
        (regs p base tail (row ++ mark :: output) index) (10 * row.length + 5) := by
  intro row
  induction row with
  | nil =>
    intro _
    have hstep := (pop_table p (Γ := moveRowBody p mark :: Γ) base mark tail output index).join
      (push_output p base mark tail output index)
    have hhead : ((regs p base (mark :: tail) output index) p.table).head? = some mark := by
      simp only [regs_table, List.head?_cons]
    have hbranch : Runs (moveRowBody p mark :: Γ) (moveRowStep p mark (some mark))
        (regs p base (mark :: tail) output index) (regs p base tail (mark :: output) index) 4 := by
      simpa only [moveRowStep, ite_eq_left rfl, ite_true] using hstep
    exact Runs.look' (c := moveRowStep p mark) hhead hbranch
  | cons x row ih =>
    intro hclean
    have hx : x ≠ mark := fun h => hclean (h ▸ List.mem_cons_self)
    have hrest : mark ∉ row := fun h => hclean (List.mem_cons_of_mem x h)
    have hstep := (pop_table p base x (row ++ mark :: tail) output index).join
      ((Runs.again0 (ih hrest)).join (push_output p base x tail (row ++ mark :: output) index))
    have hhead : ((regs p base (x :: (row ++ mark :: tail)) output index) p.table).head? = some x := by
      simp only [regs_table, List.head?_cons]
    have hlook := Runs.look' (c := moveRowStep p mark) hhead
      (by simpa only [moveRowStep, ite_eq_right hx] using hstep)
    simp only [List.cons_append]
    exact hlook.mono (by simp only [List.length_cons]; omega)

theorem moveRow_runs {Γ : Scope A} (base : Reg A) (row tail output index : List A) (h : mark ∉ row) :
    Runs Γ (moveRow p mark) (regs p base (row ++ mark :: tail) output index)
      (regs p base tail (row ++ mark :: output) index) (10 * row.length + 6) :=
  Runs.tie (runMoveRowBody p mark base tail output index row h)

/-- Skip a row, call the enclosing lookup just after the delimiter, and restore the skipped row. -/
def skipStep : Option A → Prog A
  | none => .pass
  | some x => .join (.pop p.table)
      (.join (.again (if x = mark then 1 else 0)) (.push p.table x))

def skipBody : Prog A := .look p.table (skipStep p mark)

private theorem runSkipBody {Γ : Scope A} {next : Prog A} (base : Reg A)
    (tail output output' index index' : List A) {cost : ℕ}
    (hnext : Runs (next :: Γ) next (regs p base tail output index) (regs p base tail output' index') cost) :
    ∀ (row : List A), mark ∉ row →
      Runs (skipBody p mark :: next :: Γ) (skipBody p mark)
        (regs p base (row ++ mark :: tail) output index)
        (regs p base (row ++ mark :: tail) output' index') (10 * (row.length + 1) + cost) := by
  intro row
  induction row with
  | nil =>
    intro _
    have hcall := againOne (g := skipBody p mark) hnext
    have hstep := (pop_table p base mark tail output index).join
      (hcall.join (push_table p base mark tail output' index'))
    have hlook := Runs.look' (c := skipStep p mark) (o := some mark)
      (show ((regs p base (mark :: tail) output index) p.table).head? = some mark by
        simp only [regs_table, List.head?_cons])
      (by simpa only [skipStep, ite_eq_left rfl, ite_true] using hstep)
    exact hlook.mono (by simp only [List.length_nil]; omega)
  | cons x row ih =>
    intro hrow
    have hx : x ≠ mark := by
      intro e
      exact hrow (e ▸ List.mem_cons_self)
    have ht : mark ∉ row := fun h => hrow (List.mem_cons_of_mem x h)
    have hcall := Runs.again0 (ih ht)
    have hstep := (pop_table p base x (row ++ mark :: tail) output index).join
      (hcall.join (push_table p base x (row ++ mark :: tail) output' index'))
    have hlook := Runs.look' (c := skipStep p mark) (o := some x)
      (show ((regs p base ((x :: row) ++ mark :: tail) output index) p.table).head? = some x by
        simp only [regs_table, List.cons_append, List.head?_cons])
      (by simpa only [skipStep, ite_eq_right hx, List.cons_append] using hstep)
    exact hlook.mono (by simp only [List.length_cons]; omega)

/-- Dispatch on one unary index digit. The digit and the skipped row are restored on return. -/
def lookupStep : Option A → Prog A
  | none => .tie (copyBody p mark)
  | some x => .join (.pop p.index) (.join (.tie (skipBody p mark)) (.push p.index x))

def lookupBody : Prog A := .look p.index (lookupStep p mark)

/-- Look up a delimited row at a unary index. The alphabet letter encoding a digit can be arbitrary. -/
def lookup : Prog A := .tie (lookupBody p mark)

/-- Each row has its own delimiter, including the last row. -/
def encode (rows : List (List A)) : List A := rows.flatMap fun row => row ++ [mark]

omit [DecidableEq A] in
private theorem encode_cons (row : List A) (rows : List (List A)) :
    encode mark (row :: rows) = row ++ mark :: encode mark rows := by
  simp only [encode, List.flatMap_cons, List.append_assoc, List.singleton_append]

private theorem runLookupBody {Γ : Scope A} (base : Reg A) (m : ℕ) :
    ∀ (index : List A) (rows : List (List A)) (output : List A),
      index.length < rows.length → (∀ row ∈ rows, row.length ≤ m ∧ mark ∉ row) →
      Runs (lookupBody p mark :: Γ) (lookupBody p mark)
        (regs p base (encode mark rows) output index)
        (regs p base (encode mark rows) ((rows.getD index.length []) ++ output) index)
        (24 * (m + 1) * (index.length + 1)) := by
  intro index
  induction index with
  | nil =>
    intro rows output hi hrows
    cases rows with
    | nil => simp only [List.length_nil, Nat.lt_irrefl] at hi
    | cons row rest =>
      obtain ⟨hlen, hmark⟩ := hrows row List.mem_cons_self
      have hcopy := Runs.tie (runCopyBody p mark (Γ := lookupBody p mark :: Γ) base
        (encode mark rest) [] row output hmark)
      rw [encode_cons]
      refine (Runs.look' (c := lookupStep p mark) (o := none) (B := 12 * row.length + 2 + 1)
        (by simp only [regs_index, List.head?_nil]) ?_).mono ?_
      · simpa only [lookupStep, List.length_nil, List.getD_cons_zero] using hcopy
      · simp only [List.length_nil, Nat.zero_add, Nat.mul_one]; omega
  | cons x index ih =>
    intro rows output hi hrows
    cases rows with
    | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi
    | cons row rest =>
      obtain ⟨hlen, hmark⟩ := hrows row List.mem_cons_self
      have hrest : ∀ r ∈ rest, r.length ≤ m ∧ mark ∉ r :=
        fun r hr => hrows r (List.mem_cons_of_mem row hr)
      have hi' : index.length < rest.length := by simp only [List.length_cons] at hi; omega
      have hcall := ih rest output hi' hrest
      have hskip := Runs.tie (runSkipBody p mark base (encode mark rest) output
        ((rest.getD index.length []) ++ output) index index hcall row hmark)
      have hstep := (pop_index p base x (row ++ mark :: encode mark rest) output index).join
        (hskip.join (push_index p base x (row ++ mark :: encode mark rest)
          ((rest.getD index.length []) ++ output) index))
      have hlook := Runs.look' (c := lookupStep p mark) (o := some x)
        (show ((regs p base (row ++ mark :: encode mark rest) output (x :: index)) p.index).head? =
          some x by simp only [regs_index, List.head?_cons]) hstep
      rw [encode_cons]
      simp only [List.length_cons, List.getD_cons_succ]
      exact hlook.mono (by simp only [Nat.mul_succ]; omega)

/-- The selected row is pushed onto the output stack in its original order. Both input stacks are restored.
The bound scans at most `index.length + 1` rows of length at most `m`. -/
theorem lookup_runs {Γ : Scope A} (base : Reg A) (m : ℕ) (index : List A)
    (rows : List (List A)) (output : List A) (hi : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length ≤ m ∧ mark ∉ row) :
    Runs Γ (lookup p mark) (regs p base (encode mark rows) output index)
      (regs p base (encode mark rows) ((rows.getD index.length []) ++ output) index)
      (25 * (m + 1) * (index.length + 1)) := by
  refine (Runs.tie (runLookupBody p mark base m index rows output hi hrows)).mono ?_
  have hone : 1 ≤ (m + 1) * (index.length + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  rw [Nat.mul_assoc, Nat.mul_assoc, show 25 = 24 + 1 from rfl, Nat.add_mul, Nat.one_mul]
  omega

/-- A uniform lookup bound by the total number of rows. -/
theorem lookup_tally_runs {Γ : Scope A} (base : Reg A) (m i : ℕ) (digit : A)
    (rows : List (List A)) (output : List A) (hi : i < rows.length)
    (hrows : ∀ row ∈ rows, row.length ≤ m ∧ mark ∉ row) :
    Runs Γ (lookup p mark) (regs p base (encode mark rows) output (List.replicate i digit))
      (regs p base (encode mark rows) ((rows.getD i []) ++ output) (List.replicate i digit))
      (25 * (m + 1) * rows.length) := by
  have hi' : (List.replicate i digit).length < rows.length := by simpa only [List.length_replicate] using hi
  have hrun := lookup_runs p mark (Γ := Γ) base m (List.replicate i digit) rows output hi' hrows
  rw [List.length_replicate] at hrun
  exact hrun.mono (Nat.mul_le_mul_left _ hi)

section BinaryIndex

/-- Double the tally in the index register. -/
def doubleIndexStep (digit : A) : Option A → Prog A
  | none => .pass
  | some _ => .join (.pop p.index)
      (.join (.again 0) (.join (.push p.index digit) (.push p.index digit)))

def doubleIndexBody (digit : A) : Prog A := .look p.index (doubleIndexStep p digit)

omit [DecidableEq A] in
private theorem runDoubleIndexBody {Γ : Scope A} (base : Reg A) (table output : List A) (digit : A) :
    ∀ n, Runs (doubleIndexBody p digit :: Γ) (doubleIndexBody p digit)
      (regs p base table output (List.replicate n digit))
      (regs p base table output (List.replicate (2 * n) digit)) (12 * n + 2) := by
  intro n
  induction n with
  | zero =>
    exact Runs.look' (c := doubleIndexStep p digit)
      (show ((regs p base table output []) p.index).head? = none by simp only [regs_index, List.head?_nil])
      Runs.pass
  | succ n ih =>
    have hcall := Runs.again0 ih
    have hstep := (pop_index p base digit table output (List.replicate n digit)).join
      (hcall.join ((push_index p base digit table output (List.replicate (2 * n) digit)).join
        (push_index p base digit table output (digit :: List.replicate (2 * n) digit))))
    have hlook := Runs.look' (c := doubleIndexStep p digit)
      (show ((regs p base table output (digit :: List.replicate n digit)) p.index).head? = some digit by
        simp only [regs_index, List.head?_cons]) hstep
    rw [Nat.mul_succ, show 2 * n + 2 = Nat.succ (Nat.succ (2 * n)) from rfl]
    simp only [List.replicate_succ]
    exact hlook.mono (by omega)

/-- Append the low bit to the left of a binary word represented by a tally. -/
def addIndexBit (digit : A) (b : Bool) : Prog A := if b then .push p.index digit else .pass

omit [DecidableEq A] in
private theorem runAddIndexBit {Γ : Scope A} (base : Reg A) (table output : List A)
    (digit : A) (n : ℕ) (b : Bool) :
    Runs Γ (addIndexBit p digit b) (regs p base table output (List.replicate n digit))
      (regs p base table output (List.replicate (n + b.toNat) digit)) 1 := by
  cases b
  · exact Runs.pass
  · exact push_index p base digit table output (List.replicate n digit)

/-- Value of a little-endian binary row. -/
def binaryValue (bit : A → Bool) : List A → ℕ
  | [] => 0
  | x :: row => 2 * binaryValue bit row + (bit x).toNat

omit [DecidableEq A] in
theorem binaryValue_lt (bit : A → Bool) (row : List A) : binaryValue bit row < 2 ^ row.length := by
  induction row with
  | nil => exact Nat.zero_lt_one
  | cons x row ih =>
    have hbit : (bit x).toNat ≤ 1 := by cases bit x <;> decide
    simp only [binaryValue, List.length_cons, pow_succ]
    omega

omit [DecidableEq A] in
theorem binaryValue_testBits (bit : A → Bool) (letter : Bool → A) (hletter : ∀ b, bit (letter b) = b)
    (m x : ℕ) (hx : x < 2 ^ m) :
    binaryValue bit (List.ofFn fun i : Fin m => letter (x.testBit i.val)) = x := by
  induction m generalizing x with
  | zero =>
    simp only [List.ofFn_zero, binaryValue]
    rw [pow_zero] at hx
    omega
  | succ m ih =>
    have hx' : x / 2 < 2 ^ m := by rw [pow_succ] at hx; omega
    have hhigh (i : Fin m) : x.testBit i.succ.val = (x / 2).testBit i.val := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 2]
    have hlow : (x.testBit 0).toNat = x % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one]
      by_cases hp : x % 2 = 1
      · simp only [hp, decide_true, Bool.toNat_true]
      · simp only [decide_eq_false_iff_not.mpr hp, Bool.toNat_false]
        omega
    rw [List.ofFn_succ, binaryValue, hletter, Fin.val_zero, hlow]
    simp only [hhigh, ih _ hx']
    omega

def binaryIndexStep (bit : A → Bool) (digit : A) : Option A → Prog A
  | none => .pass
  | some x => if x = mark then .pass else
      .join (.pop p.table) (.join (.again 0) (.join (.tie (doubleIndexBody p digit))
        (.join (addIndexBit p digit (bit x)) (.push p.table x))))

def binaryIndexBody (bit : A → Bool) (digit : A) : Prog A := .look p.table (binaryIndexStep p mark bit digit)

/-- Convert the first delimited row into a tally without changing the original row. -/
def binaryIndex (bit : A → Bool) (digit : A) : Prog A := .tie (binaryIndexBody p mark bit digit)

private theorem runBinaryIndexBody {Γ : Scope A} (base : Reg A) (tail output : List A)
    (bit : A → Bool) (digit : A) : ∀ row, mark ∉ row →
    Runs (binaryIndexBody p mark bit digit :: Γ) (binaryIndexBody p mark bit digit)
      (regs p base (row ++ mark :: tail) output [])
      (regs p base (row ++ mark :: tail) output (List.replicate (binaryValue bit row) digit))
      (24 * (row.length + binaryValue bit row + 1)) := by
  intro row
  induction row with
  | nil =>
    intro _
    have hlook := Runs.look' (c := binaryIndexStep p mark bit digit) (o := some mark)
      (show ((regs p base (mark :: tail) output []) p.table).head? = some mark by
        simp only [regs_table, List.head?_cons])
      (show Runs (binaryIndexBody p mark bit digit :: Γ) (binaryIndexStep p mark bit digit (some mark))
        (regs p base (mark :: tail) output []) (regs p base (mark :: tail) output []) 1 by
        simpa only [binaryIndexStep, ite_eq_left rfl, ite_true] using
          (Runs.pass (Γ := binaryIndexBody p mark bit digit :: Γ)
            (r := regs p base (mark :: tail) output [])))
    exact hlook.mono (by simp only [List.length_nil, binaryValue]; omega)
  | cons x row ih =>
    intro hrow
    have hx : x ≠ mark := by
      intro e
      exact hrow (e ▸ List.mem_cons_self)
    have ht : mark ∉ row := fun h => hrow (List.mem_cons_of_mem x h)
    let v := binaryValue bit row
    have hcall := Runs.again0 (ih ht)
    have hdouble := Runs.tie (runDoubleIndexBody p (Γ := binaryIndexBody p mark bit digit :: Γ)
      base (row ++ mark :: tail) output digit v)
    have hbit := runAddIndexBit p (Γ := binaryIndexBody p mark bit digit :: Γ)
      base (row ++ mark :: tail) output digit (2 * v) (bit x)
    have hstep := (pop_table p base x (row ++ mark :: tail) output []).join
      (hcall.join (hdouble.join (hbit.join
        (push_table p base x (row ++ mark :: tail) output (List.replicate (2 * v + (bit x).toNat) digit)))))
    have hlook := Runs.look' (c := binaryIndexStep p mark bit digit) (o := some x)
      (show ((regs p base (x :: (row ++ mark :: tail)) output []) p.table).head? = some x by
        simp only [regs_table, List.head?_cons])
      (by simpa only [binaryIndexStep, ite_eq_right hx] using hstep)
    simp only [List.cons_append]
    exact hlook.mono (by simp only [List.length_cons, binaryValue, v]; omega)

/-- The original stack is restored. The index register starts empty and receives the decoded tally.
The doubling work is charged to the value, since each suffix value is at most half the next one. -/
theorem binaryIndex_runs {Γ : Scope A} (base : Reg A) (row tail output : List A)
    (bit : A → Bool) (digit : A) (hrow : mark ∉ row) :
    Runs Γ (binaryIndex p mark bit digit) (regs p base (row ++ mark :: tail) output [])
      (regs p base (row ++ mark :: tail) output (List.replicate (binaryValue bit row) digit))
      (25 * (row.length + binaryValue bit row + 1)) := by
  exact (Runs.tie (runBinaryIndexBody p mark base tail output bit digit row hrow)).mono (by omega)

/-- Convert the fixed-width encoding of `x` used by the permutation input. -/
theorem binaryIndex_testBits_runs {Γ : Scope A} (base : Reg A) (m x : ℕ) (hx : x < 2 ^ m)
    (bit : A → Bool) (letter : Bool → A) (hletter : ∀ b, bit (letter b) = b)
    (hmark : ∀ b, letter b ≠ mark) (digit : A) (tail output : List A) :
    let row := List.ofFn fun i : Fin m => letter (x.testBit i.val)
    Runs Γ (binaryIndex p mark bit digit) (regs p base (row ++ mark :: tail) output [])
      (regs p base (row ++ mark :: tail) output (List.replicate x digit)) (25 * (m + x + 1)) := by
  intro row
  have hrow : mark ∉ row := by
    intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact hmark (x.testBit i.val) hi
  have h := binaryIndex_runs p mark (Γ := Γ) base row tail output bit digit hrow
  have hval : binaryValue bit row = x := binaryValue_testBits bit letter hletter m x hx
  have hlen : row.length = m := List.length_ofFn
  rwa [hval, hlen] at h

end BinaryIndex

end P1SolFactor.SolRows
