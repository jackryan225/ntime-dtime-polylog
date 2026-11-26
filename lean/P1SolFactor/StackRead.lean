import P1SolFactor.RowLookup

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng

variable {A : Type} (p : Ports)

private def copyAllStep : Option A → Prog A
  | none => .pass
  | some x =>
    .join (.pop p.table) (.join (.again 0) (.join (.push p.table x) (.push p.output x)))

private def copyAllBody : Prog A := .look p.table (copyAllStep p)

/-- Copy a stack in order, restoring the source. -/
def copyAll : Prog A := .tie (copyAllBody p)

theorem copyAll_runs {Γ : Scope A} (base : Reg A) (source output index : List A) :
    Runs Γ (copyAll p) (regs p base source output index)
      (regs p base source (source ++ output) index) (12 * source.length + 3) := by
  apply Runs.tie
  induction source with
  | nil =>
    exact Runs.look' (c := copyAllStep p) (o := none) (by simp)
      (Runs.pass (r := regs p base [] output index))
  | cons x source ih =>
    let r := regs p base (x :: source) output index
    have hpop : Runs (copyAllBody p :: Γ) (.pop p.table) r (regs p base source output index) 1 :=
      (Runs.pop p.table).congr_out (by dsimp only [r]; rw [regs_table, List.tail_cons, write_table])
    have hrestore : Runs (copyAllBody p :: Γ) (.push p.table x)
        (regs p base source (source ++ output) index)
        (regs p base (x :: source) (source ++ output) index) 1 :=
      (Runs.push p.table x).congr_out (by rw [regs_table, write_table])
    have hout : Runs (copyAllBody p :: Γ) (.push p.output x)
        (regs p base (x :: source) (source ++ output) index)
        (regs p base (x :: source) (x :: (source ++ output)) index) 1 :=
      (Runs.push p.output x).congr_out (by rw [regs_output, write_output])
    have hlook := Runs.look' (c := copyAllStep p) (o := some x)
      (show (r p.table).head? = some x by simp [r])
      (hpop.join ((Runs.again0 ih).join (hrestore.join hout)))
    exact hlook.mono (by simp only [List.length_cons]; omega)

theorem copyAll_at {Γ : Scope A} (r : Reg A) :
    Runs Γ (copyAll p) r (Function.update r p.output (r p.table ++ r p.output))
      (12 * (r p.table).length + 3) := by
  have hc := copyAll_runs (Γ := Γ) p r (r p.table) (r p.output) (r p.index)
  have hs := regs_eq p r rfl rfl rfl
  have hu := write_output p r (r p.table) (r p.output) (r p.index) (r p.table ++ r p.output)
  rw [hs] at hc hu
  exact hc.congr_out hu.symm

variable [DecidableEq A]

private def readFieldBit : Option A → Prog A
  | none => .pass
  | some x => .join (.pop p.index) (.join (.pop p.table) (.join (.again 0) (.push p.output x)))

private def readFieldStep (stop : A) : Option A → Prog A
  | none => .pass
  | some x => if x = stop then .pop p.index else .look p.table (readFieldBit p)

private def readFieldBody (stop : A) : Prog A := .look p.index (readFieldStep p stop)

/-- Consume a unary width and transfer exactly that many letters from the key to the output. -/
def readField (stop : A) : Prog A := .tie (readFieldBody p stop)

theorem readField_runs {Γ : Scope A} (base : Reg A) (digit stop : A) (hds : digit ≠ stop)
    (word rest output widths : List A) :
    Runs Γ (readField p stop)
      (regs p base (word ++ rest) output (List.replicate word.length digit ++ stop :: widths))
      (regs p base rest (word ++ output) widths) (12 * word.length + 3) := by
  apply Runs.tie
  let scope := readFieldBody p stop :: Γ
  induction word with
  | nil =>
    have hp : Runs scope (.pop p.index) (regs p base rest output (stop :: widths)) (regs p base rest output widths) 1 :=
      (Runs.pop p.index).congr_out (by rw [regs_index, List.tail_cons, write_index])
    have hlook := Runs.look' (c := readFieldStep p stop) (o := some stop)
      (show ((regs p base rest output (stop :: widths)) p.index).head? = some stop by simp)
      (by simpa only [readFieldStep, ite_true] using hp)
    exact hlook
  | cons x word ih =>
    let count := List.replicate word.length digit ++ stop :: widths
    let r := regs p base (x :: (word ++ rest)) output (digit :: count)
    let r' := regs p base (x :: (word ++ rest)) output count
    have hpopIndex : Runs scope (.pop p.index) r r' 1 :=
      (Runs.pop p.index).congr_out (by dsimp only [r, r']; rw [regs_index, List.tail_cons, write_index])
    have hpopKey : Runs scope (.pop p.table) r' (regs p base (word ++ rest) output count) 1 :=
      (Runs.pop p.table).congr_out (by dsimp only [r']; rw [regs_table, List.tail_cons, write_table])
    have hout : Runs scope (.push p.output x) (regs p base rest (word ++ output) widths)
        (regs p base rest (x :: (word ++ output)) widths) 1 :=
      (Runs.push p.output x).congr_out (by rw [regs_output, write_output])
    have hkey := Runs.look' (c := readFieldBit p) (o := some x)
      (show (r p.table).head? = some x by simp [r])
      (hpopIndex.join (hpopKey.join ((Runs.again0 ih).join hout)))
    have hlook := Runs.look' (c := readFieldStep p stop) (o := some digit)
      (show (r p.index).head? = some digit by simp [r])
      (by simpa only [readFieldStep, ite_eq_right hds] using hkey)
    exact hlook.mono (by simp only [List.length_cons]; omega)

/-- Framed form of the field reader, with all three modified registers explicit. -/
theorem readField_at {Γ : Scope A} {r : Reg A} (digit stop : A) (hds : digit ≠ stop)
    (word rest widths : List A) (hkey : r p.table = word ++ rest)
    (hwidth : r p.index = List.replicate word.length digit ++ stop :: widths) :
    Runs Γ (readField p stop) r
      (Function.update (Function.update (Function.update r p.table rest) p.index widths)
        p.output (word ++ r p.output)) (12 * word.length + 3) := by
  have hr := readField_runs (Γ := Γ) p r digit stop hds word rest (r p.output) widths
  have hs := regs_eq p r hkey rfl hwidth
  rw [hs] at hr
  refine hr.congr_out ?_
  conv_rhs => rw [← hs]
  rw [write_table, write_index, write_output, regs_output]

end P1SolFactor.SolRows
