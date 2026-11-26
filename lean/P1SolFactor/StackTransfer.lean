import P1SolFactor.RowLookup

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng

variable {A : Type} (p : Ports)

private theorem transfer_pop {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.pop p.table) (regs p base (x :: t) o i) (regs p base t o i) 1 :=
  (Runs.pop p.table).congr_out (by rw [regs_table, List.tail_cons, write_table])

private theorem transfer_push {Γ : Scope A} (base : Reg A) (x : A) (t o i : List A) :
    Runs Γ (.push p.output x) (regs p base t o i) (regs p base t (x :: o) i) 1 :=
  (Runs.push p.output x).congr_out (by rw [regs_output, write_output])

def transferPrefixStep (stop : A → Bool) : Option A → Prog A
  | none => .pass
  | some x => if stop x then .pop p.table else
      .join (.pop p.table) (.join (.again 0) (.push p.output x))

def transferPrefixBody (stop : A → Bool) : Prog A := .look p.table (transferPrefixStep p stop)

/-- Move a prefix in order. If a stopping letter is present, consume it from the source. -/
def transferPrefix (stop : A → Bool) : Prog A := .tie (transferPrefixBody p stop)

private theorem transferPrefixBody_runs {Γ : Scope A} (base : Reg A) (stop : A → Bool)
    (suffix output index : List A) (hstop : ∀ x, suffix.head? = some x → stop x = true) :
    ∀ front : List A, (∀ x ∈ front, stop x = false) →
      Runs (transferPrefixBody p stop :: Γ) (transferPrefixBody p stop)
        (regs p base (front ++ suffix) output index)
        (regs p base suffix.tail (front ++ output) index) (9 * front.length + 2) := by
  intro front
  induction front with
  | nil =>
    intro _
    cases suffix with
    | nil =>
      have hhead : ((regs p base [] output index) p.table).head? = none := by
        simp only [regs_table, List.head?_nil]
      exact Runs.look' (c := transferPrefixStep p stop) hhead
        (Runs.pass (Γ := transferPrefixBody p stop :: Γ) (r := regs p base [] output index))
    | cons x suffix =>
      have hhead : ((regs p base (x :: suffix) output index) p.table).head? = some x := by
        simp only [regs_table, List.head?_cons]
      have hx := hstop x rfl
      have hbranch : Runs (transferPrefixBody p stop :: Γ) (transferPrefixStep p stop (some x))
          (regs p base (x :: suffix) output index) (regs p base suffix output index) 1 := by
        simpa only [transferPrefixStep, hx, ite_true] using
          (transfer_pop p (Γ := transferPrefixBody p stop :: Γ) base x suffix output index)
      exact Runs.look' (c := transferPrefixStep p stop) hhead hbranch
  | cons x front ih =>
    intro hprefix
    have hx := hprefix x List.mem_cons_self
    have hrest : ∀ y ∈ front, stop y = false := fun y hy => hprefix y (List.mem_cons_of_mem x hy)
    have hstep := (transfer_pop p base x (front ++ suffix) output index).join
      ((Runs.again0 (ih hrest)).join (transfer_push p base x suffix.tail (front ++ output) index))
    have hhead : ((regs p base (x :: (front ++ suffix)) output index) p.table).head? = some x := by
      simp only [regs_table, List.head?_cons]
    have hlook := Runs.look' (c := transferPrefixStep p stop) hhead
      (by simpa only [transferPrefixStep, hx, Bool.false_eq_true, ite_false] using hstep)
    simp only [List.cons_append]
    exact hlook.mono (by simp only [List.length_cons]; omega)

theorem transferPrefix_runs {Γ : Scope A} (base : Reg A) (stop : A → Bool)
    (front suffix output index : List A) (hprefix : ∀ x ∈ front, stop x = false)
    (hstop : ∀ x, suffix.head? = some x → stop x = true) :
    Runs Γ (transferPrefix p stop) (regs p base (front ++ suffix) output index)
      (regs p base suffix.tail (front ++ output) index) (9 * front.length + 3) :=
  Runs.tie (transferPrefixBody_runs p base stop suffix output index hstop front hprefix)

theorem moveAll_runs {Γ : Scope A} (base : Reg A) (t o i : List A) :
    Runs Γ (transferPrefix p (fun _ => false)) (regs p base t o i)
      (regs p base [] (t ++ o) i) (9 * t.length + 3) := by
  have h := transferPrefix_runs (Γ := Γ) p base (fun _ => false) t [] o i (fun _ _ => rfl)
    (fun _ he => nomatch he)
  simpa only [List.append_nil, List.tail_nil] using h

variable [DecidableEq A] (mark : A)

theorem emitRow_runs {Γ : Scope A} (base : Reg A) (row tail output index : List A) (hrow : mark ∉ row) :
    Runs Γ (transferPrefix p (fun x => decide (x = mark))) (regs p base (row ++ mark :: tail) output index)
      (regs p base tail (row ++ output) index) (9 * row.length + 3) := by
  refine transferPrefix_runs p base (fun x => decide (x = mark)) row (mark :: tail) output index ?_ ?_
  · intro x hx
    apply decide_eq_false_iff_not.mpr
    rintro rfl
    exact hrow hx
  · intro x hx
    have h : mark = x := Option.some.inj hx
    exact decide_eq_true_eq.mpr h.symm

def takeTableRowStep : Option A → Prog A
  | none => .pass
  | some x => .join (.pop p.table)
      (.join (.again (if x = mark then 1 else 0)) (.push p.output x))

def takeTableRowBody : Prog A := .look p.table (takeTableRowStep p mark)

def takeTableStep : Option A → Prog A
  | none => .pass
  | some x => if x = mark then .pop p.table else .tie (takeTableRowBody p mark)

def takeTableBody : Prog A := .look p.table (takeTableStep p mark)

/-- Move a table of nonempty rows, dropping its extra terminating marker. -/
def takeTable : Prog A := .tie (takeTableBody p mark)

private theorem takeTableRowBody_runs {Γ : Scope A} {next : Prog A} (base : Reg A)
    (remaining tail output output' index : List A) {cost : ℕ}
    (hnext : Runs (next :: Γ) next (regs p base remaining output index) (regs p base tail output' index) cost) :
    ∀ row, mark ∉ row →
      Runs (takeTableRowBody p mark :: next :: Γ) (takeTableRowBody p mark)
        (regs p base (row ++ mark :: remaining) output index)
        (regs p base tail (row ++ mark :: output') index) (10 * (row.length + 1) + cost) := by
  intro row
  let scope := takeTableRowBody p mark :: next :: Γ
  induction row with
  | nil =>
    intro _
    have hcall : Runs scope (.again 1) (regs p base remaining output index)
        (regs p base tail output' index) (cost + 1) := by
      obtain ⟨n, hr, hn⟩ := hnext
      exact ⟨1 + n, .again rfl hr, by omega⟩
    have hstep := (transfer_pop p base mark remaining output index).join
      (hcall.join (transfer_push p base mark tail output' index))
    have hhead : ((regs p base (mark :: remaining) output index) p.table).head? = some mark := by
      simp only [regs_table, List.head?_cons]
    have hlook := Runs.look' (c := takeTableRowStep p mark) hhead
      (by simpa only [takeTableRowStep, ite_eq_left rfl, ite_true] using hstep)
    exact hlook.mono (by simp only [List.length_nil]; omega)
  | cons x row ih =>
    intro hc
    have hx : x ≠ mark := fun he => hc (he ▸ List.mem_cons_self)
    have hr : mark ∉ row := fun hm => hc (List.mem_cons_of_mem x hm)
    have hstep := (transfer_pop p base x (row ++ mark :: remaining) output index).join
      ((Runs.again0 (ih hr)).join (transfer_push p base x tail (row ++ mark :: output') index))
    have hhead : ((regs p base (x :: (row ++ mark :: remaining)) output index) p.table).head? = some x := by
      simp only [regs_table, List.head?_cons]
    have hlook := Runs.look' (c := takeTableRowStep p mark) hhead
      (by simpa only [takeTableRowStep, ite_eq_right hx] using hstep)
    simp only [List.cons_append]
    exact hlook.mono (by simp only [List.length_cons]; omega)

omit [DecidableEq A] in
private theorem encode_cons_for_transfer (row : List A) (rows : List (List A)) :
    encode mark (row :: rows) = row ++ mark :: encode mark rows := by
  simp only [encode, List.flatMap_cons, List.append_assoc, List.singleton_append]

private theorem takeTableBody_runs {Γ : Scope A} (base : Reg A) (tail output index : List A) :
    ∀ rows : List (List A), (∀ row ∈ rows, row ≠ [] ∧ mark ∉ row) →
      Runs (takeTableBody p mark :: Γ) (takeTableBody p mark)
        (regs p base (encode mark rows ++ mark :: tail) output index)
        (regs p base tail (encode mark rows ++ output) index) (15 * (encode mark rows).length + 2) := by
  intro rows
  induction rows with
  | nil =>
    intro _
    have hhead : ((regs p base (mark :: tail) output index) p.table).head? = some mark := by
      simp only [regs_table, List.head?_cons]
    have hbranch : Runs (takeTableBody p mark :: Γ) (takeTableStep p mark (some mark))
        (regs p base (mark :: tail) output index) (regs p base tail output index) 1 := by
      simpa only [takeTableStep, ite_eq_left rfl, ite_true] using
        (transfer_pop p (Γ := takeTableBody p mark :: Γ) base mark tail output index)
    exact Runs.look' (c := takeTableStep p mark) hhead hbranch
  | cons row rows ih =>
    intro hc
    obtain ⟨hn, hclean⟩ := hc row List.mem_cons_self
    have hrest : ∀ r ∈ rows, r ≠ [] ∧ mark ∉ r := fun r hr => hc r (List.mem_cons_of_mem row hr)
    have hnext := ih hrest
    have hrow := Runs.tie (takeTableRowBody_runs p mark base (encode mark rows ++ mark :: tail)
      tail output (encode mark rows ++ output) index hnext row hclean)
    cases row with
    | nil => exact (hn rfl).elim
    | cons x row =>
      have hx : x ≠ mark := fun he => hclean (he ▸ List.mem_cons_self)
      have hhead : ((regs p base ((x :: row) ++ mark :: (encode mark rows ++ mark :: tail)) output index)
          p.table).head? = some x := by simp only [regs_table, List.cons_append, List.head?_cons]
      have hlook := Runs.look' (c := takeTableStep p mark) hhead
        (by simpa only [takeTableStep, ite_eq_right hx] using hrow)
      rw [encode_cons_for_transfer]
      simp only [List.append_assoc, List.cons_append]
      exact hlook.mono (by simp only [List.length_append, List.length_cons]; omega)

/-- Moving a parked table consumes the extra marker and leaves the enclosing stack intact. -/
theorem takeTable_runs {Γ : Scope A} (base : Reg A) (rows : List (List A)) (tail output index : List A)
    (hrows : ∀ row ∈ rows, row ≠ [] ∧ mark ∉ row) :
    Runs Γ (takeTable p mark) (regs p base (encode mark rows ++ mark :: tail) output index)
      (regs p base tail (encode mark rows ++ output) index) (15 * (encode mark rows).length + 3) :=
  Runs.tie (takeTableBody_runs p mark base tail output index rows hrows)

end P1SolFactor.SolRows
