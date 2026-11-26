import P1SolFactor.StackRead

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng

variable {A : Type}

/-- The numbered field registers start at register 8. Registers 5 and 6 hold working copies. -/
def fieldReg (j : ℕ) : ℕ := 8 + j

def fieldPorts (j : ℕ) : Ports :=
  ⟨5, fieldReg j, 6, by unfold fieldReg; omega, by decide, by unfold fieldReg; omega⟩

def fieldFrame (base : Reg A) (key widths : List A) : Reg A :=
  Function.update (Function.update base 5 key) 6 widths

theorem fieldFrame_keep (base : Reg A) (key widths : List A) {i : ℕ} (h5 : i ≠ 5) (h6 : i ≠ 6) :
    fieldFrame base key widths i = base i := by
  simp only [fieldFrame, Function.update_of_ne h5, Function.update_of_ne h6]

theorem fieldFrame_empty (base : Reg A) (h5 : base 5 = []) (h6 : base 6 = []) :
    fieldFrame base [] [] = base := by
  calc
    fieldFrame base [] [] = fieldFrame base (base 5) (base 6) := by rw [h5, h6]
    _ = base := by simp only [fieldFrame, Function.update_eq_self]

theorem fieldReg_ne_five (j : ℕ) : fieldReg j ≠ 5 := by unfold fieldReg; omega

theorem fieldReg_ne_six (j : ℕ) : fieldReg j ≠ 6 := by unfold fieldReg; omega

private theorem regs_fieldPorts (base : Reg A) (j : ℕ) (key word widths : List A) :
    regs (fieldPorts j) base key word widths =
      fieldFrame (Function.update base (fieldReg j) word) key widths := by
  funext i
  by_cases h5 : i = 5
  · subst i
    simp [regs, fieldPorts, fieldFrame]
  by_cases h6 : i = 6
  · subst i
    simp [regs, fieldPorts, fieldFrame, (fieldReg_ne_six j).symm]
  simp [regs, fieldPorts, fieldFrame, Function.update_apply, h5, h6]

/-- Install the fields in consecutive registers, in order, above their original suffixes. -/
def putFields (base : Reg A) (j : ℕ) : List (List A) → Reg A
  | [] => base
  | word :: rest =>
    putFields (Function.update base (fieldReg j) (word ++ base (fieldReg j))) (j + 1) rest

theorem putFields_below (base : Reg A) (j : ℕ) (fields : List (List A)) {i : ℕ} (hi : i < fieldReg j) :
    putFields base j fields i = base i := by
  induction fields generalizing base j with
  | nil => rfl
  | cons word rest ih =>
    have hi' : i < fieldReg (j + 1) := by unfold fieldReg at *; omega
    rw [putFields, ih _ _ hi', Function.update_of_ne (Nat.ne_of_lt hi)]

theorem putFields_update_below (base : Reg A) (j : ℕ) (fields : List (List A)) {i : ℕ}
    (hi : i < fieldReg j) (value : List A) :
    putFields (Function.update base i value) j fields = Function.update (putFields base j fields) i value := by
  induction fields generalizing base j with
  | nil => rfl
  | cons word rest ih =>
    have hne := Nat.ne_of_lt hi
    have hi' : i < fieldReg (j + 1) := by unfold fieldReg at *; omega
    simp only [putFields, Function.update_of_ne hne.symm]
    rw [Function.update_comm hne, ih _ _ hi']

theorem putFields_at (base : Reg A) (j : ℕ) (fields : List (List A)) (k : ℕ)
    (hk : k < fields.length) :
    putFields base j fields (fieldReg (j + k)) = fields[k] ++ base (fieldReg (j + k)) := by
  induction fields generalizing base j k with
  | nil => simp at hk
  | cons word rest ih =>
    cases k with
    | zero =>
      have h : fieldReg j < fieldReg (j + 1) := by unfold fieldReg; omega
      simp only [putFields, Nat.add_zero, List.getElem_cons_zero, putFields_below _ _ _ h,
        Function.update_self]
    | succ k =>
      have hk' : k < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk
      have haddr : j + (k + 1) = j + 1 + k := by omega
      have hne : fieldReg (j + 1 + k) ≠ fieldReg j := by unfold fieldReg; omega
      simpa only [putFields, Nat.succ_eq_add_one, haddr, List.getElem_cons_succ, Function.update_of_ne hne]
        using ih (Function.update base (fieldReg j) (word ++ base (fieldReg j))) (j + 1) k hk'

theorem fieldFrame_putFields_at (base : Reg A) (j : ℕ) (fields : List (List A)) (k : ℕ)
    (hk : k < fields.length) (key widths : List A) :
    fieldFrame (putFields base j fields) key widths (fieldReg (j + k)) = fields[k] ++ base (fieldReg (j + k)) := by
  rw [fieldFrame_keep _ _ _ (fieldReg_ne_five _) (fieldReg_ne_six _), putFields_at _ _ _ _ hk]

theorem fieldFrame_after_load (base : Reg A) (j : ℕ) (fields : List (List A))
    (h5 : base 5 = []) (h6 : base 6 = []) : fieldFrame (putFields base j fields) [] [] = putFields base j fields := by
  apply fieldFrame_empty
  · rw [putFields_below _ _ _ (by unfold fieldReg; omega : 5 < fieldReg j), h5]
  · rw [putFields_below _ _ _ (by unfold fieldReg; omega : 6 < fieldReg j), h6]

/-- A concatenation of unary widths, one per field, including the zero-width fields. -/
def fieldWidths (digit stop : A) (fields : List (List A)) : List A :=
  fields.flatMap fun word => List.replicate word.length digit ++ [stop]

theorem fieldWidths_length (digit stop : A) (fields : List (List A)) :
    (fieldWidths digit stop fields).length = fields.flatten.length + fields.length := by
  induction fields with
  | nil => rfl
  | cons word fields ih =>
    simp only [fieldWidths, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil, List.flatten_cons] at ih ⊢
    omega

variable [DecidableEq A]

/-- Split a statically known number of fields from the two working stacks. -/
def splitFields (stop : A) (j : ℕ) : ℕ → Prog A
  | 0 => .pass
  | n + 1 => .join (readField (fieldPorts j) stop) (splitFields stop (j + 1) n)

private theorem readOne_runs {Γ : Scope A} (base : Reg A) (j : ℕ) (digit stop : A) (hds : digit ≠ stop)
    (word rest widths : List A) :
    Runs Γ (readField (fieldPorts j) stop)
      (fieldFrame base (word ++ rest) (List.replicate word.length digit ++ stop :: widths))
      (fieldFrame (Function.update base (fieldReg j) (word ++ base (fieldReg j))) rest widths)
      (12 * word.length + 3) := by
  have hr := readField_runs (Γ := Γ) (fieldPorts j) base digit stop hds word rest (base (fieldReg j)) widths
  simpa only [regs_fieldPorts, Function.update_eq_self] using hr

theorem splitFields_runs {Γ : Scope A} (base : Reg A) (j : ℕ) (digit stop : A) (hds : digit ≠ stop)
    (fields : List (List A)) (keyTail widthTail : List A) :
    Runs Γ (splitFields stop j fields.length)
      (fieldFrame base (fields.flatten ++ keyTail) (fieldWidths digit stop fields ++ widthTail))
      (fieldFrame (putFields base j fields) keyTail widthTail)
      (12 * fields.flatten.length + 5 * fields.length + 1) := by
  induction fields generalizing base j with
  | nil =>
    simpa only [splitFields, putFields, List.length_nil, List.flatten_nil, fieldWidths, List.flatMap_nil,
      List.nil_append, Nat.mul_zero, Nat.zero_add] using
      (Runs.pass (Γ := Γ) (r := fieldFrame base keyTail widthTail))
  | cons word fields ih =>
    have hr := readOne_runs (Γ := Γ) base j digit stop hds word
      (fields.flatten ++ keyTail) (fieldWidths digit stop fields ++ widthTail)
    have hrest := ih (Function.update base (fieldReg j) (word ++ base (fieldReg j))) (j + 1)
    have h := hr.join hrest
    simp only [List.length_cons, splitFields, List.flatten_cons, List.append_assoc, fieldWidths,
      List.flatMap_cons, List.singleton_append, putFields, List.length_append]
    exact h.mono (by omega)

end P1SolFactor.SolRows
