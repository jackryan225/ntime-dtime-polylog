import P1SolFactor.RowLookup

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng
open scoped Classical

variable {A : Type}

/-- Equality of finite bit lists extended by false bits. -/
def paddedAgree (bit : A → Bool) (xs ys : List A) : Prop :=
  ∀ i, (xs.map bit).getD i false = (ys.map bit).getD i false

private def headBit (bit : A → Bool) (x : Option A) : Bool := (x.map bit).getD false

private theorem paddedAgree_step (bit : A → Bool) (xs ys : List A) :
    paddedAgree bit xs ys ↔
      headBit bit xs.head? = headBit bit ys.head? ∧ paddedAgree bit xs.tail ys.tail := by
  have hhead (zs : List A) : (zs.map bit).getD 0 false = headBit bit zs.head? := by
    cases zs <;> rfl
  have htail (zs : List A) (i : ℕ) : (zs.map bit).getD (i + 1) false = (zs.tail.map bit).getD i false := by
    cases zs <;> rfl
  constructor
  · intro h
    refine ⟨by rw [← hhead, ← hhead]; exact h 0, fun i => ?_⟩
    rw [← htail, ← htail]
    exact h (i + 1)
  · rintro ⟨h0, ht⟩ i
    cases i with
    | zero => rw [hhead, hhead]; exact h0
    | succ i => rw [htail, htail]; exact ht i

private def dropHead (j : ℕ) : Option A → Prog A
  | none => .pass
  | some _ => .pop j

private def restoreHead (j : ℕ) : Option A → Prog A
  | none => .pass
  | some x => .push j x

private theorem dropHead_runs {Γ : Scope A} (r : Reg A) (j : ℕ) :
    Runs Γ (dropHead j (r j).head?) r (Function.update r j (r j).tail) 1 := by
  cases hs : r j with
  | nil =>
    exact Runs.pass.congr_out (by rw [List.tail_nil, ← hs, Function.update_eq_self])
  | cons x xs =>
    simpa only [hs, List.head?_cons, List.tail_cons, dropHead] using
      (Runs.pop (Γ := Γ) (r := r) j)

private theorem restoreHead_runs {Γ : Scope A} (r : Reg A) (j : ℕ) (xs : List A)
    (hs : r j = xs.tail) :
    Runs Γ (restoreHead j xs.head?) r (Function.update r j xs) 1 := by
  cases xs with
  | nil =>
    exact Runs.pass.congr_out (by rw [show [] = r j from hs.symm, Function.update_eq_self])
  | cons x xs =>
    exact (Runs.push j x).congr_out (by rw [hs, List.tail_cons])

variable (p : Ports)

private def compareTails (x y : Option A) : Prog A :=
  .join (dropHead p.table x) (.join (dropHead p.index y)
    (.join (.again 0) (.join (restoreHead p.index y) (restoreHead p.table x))))

private def comparePair (bit : A → Bool) (yes no : A) (x y : Option A) : Prog A :=
  if x.isNone && y.isNone then .push p.output yes
  else if headBit bit x = headBit bit y then compareTails p x y
  else .push p.output no

private def comparePaddedBody (bit : A → Bool) (yes no : A) : Prog A :=
  .look p.table fun x => .look p.index (comparePair p bit yes no x)

/-- Compare two words with implicit zero padding, preserving both words. -/
def comparePadded (bit : A → Bool) (yes no : A) : Prog A := .tie (comparePaddedBody p bit yes no)

private theorem comparePadded_look {Γ : Scope A} (bit : A → Bool) (yes no : A)
    (base : Reg A) (xs ys out : List A) {s : Reg A} {cost : ℕ}
    (h : Runs Γ (comparePair p bit yes no xs.head? ys.head?) (regs p base xs out ys) s cost) :
    Runs Γ (comparePaddedBody p bit yes no) (regs p base xs out ys) s (cost + 2) := by
  exact Runs.look' (c := fun x => .look p.index (comparePair p bit yes no x))
    (show ((regs p base xs out ys) p.table).head? = xs.head? by rw [regs_table])
    (Runs.look' (c := comparePair p bit yes no xs.head?)
      (show ((regs p base xs out ys) p.index).head? = ys.head? by rw [regs_index]) h)

private theorem comparePadded_push {Γ : Scope A} (base : Reg A) (xs ys out : List A) (a : A) :
    Runs Γ (.push p.output a) (regs p base xs out ys) (regs p base xs (a :: out) ys) 1 :=
  (Runs.push p.output a).congr_out (by rw [regs_output, write_output])

private theorem compareTails_runs {Γ : Scope A} {body : Prog A} (base : Reg A) (xs ys out out' : List A)
    {cost : ℕ} (hr : Runs (body :: Γ) body (regs p base xs.tail out ys.tail)
      (regs p base xs.tail out' ys.tail) cost) :
    Runs (body :: Γ) (compareTails p xs.head? ys.head?)
      (regs p base xs out ys) (regs p base xs out' ys) (cost + 13) := by
  let scope := body :: Γ
  have hx : Runs scope (dropHead p.table xs.head?) (regs p base xs out ys) (regs p base xs.tail out ys) 1 := by
    simpa only [regs_table, write_table] using
      dropHead_runs (Γ := scope) (regs p base xs out ys) p.table
  have hy : Runs scope (dropHead p.index ys.head?) (regs p base xs.tail out ys) (regs p base xs.tail out ys.tail) 1 := by
    simpa only [regs_index, write_index] using
      dropHead_runs (Γ := scope) (regs p base xs.tail out ys) p.index
  have ry : Runs scope (restoreHead p.index ys.head?) (regs p base xs.tail out' ys.tail)
      (regs p base xs.tail out' ys) 1 := by
    simpa only [write_index] using
      restoreHead_runs (Γ := scope) (regs p base xs.tail out' ys.tail) p.index ys (by rw [regs_index])
  have rx : Runs scope (restoreHead p.table xs.head?) (regs p base xs.tail out' ys) (regs p base xs out' ys) 1 := by
    simpa only [write_table] using
      restoreHead_runs (Γ := scope) (regs p base xs.tail out' ys) p.table xs (by rw [regs_table])
  exact (hx.join (hy.join ((Runs.again0 hr).join (ry.join rx)))).mono (by omega)

private theorem comparePaddedBody_runs {Γ : Scope A} (base : Reg A) (bit : A → Bool) (yes no : A)
    (xs ys out : List A) :
    Runs (comparePaddedBody p bit yes no :: Γ) (comparePaddedBody p bit yes no)
      (regs p base xs out ys)
      (regs p base xs ((if paddedAgree bit xs ys then yes else no) :: out) ys)
      (16 * (xs.length + ys.length + 1)) := by
  let scope := comparePaddedBody p bit yes no :: Γ
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := hempty
    have h : paddedAgree bit ([] : List A) [] := fun _ => rfl
    rw [ite_eq_left h]
    have hp := comparePadded_push (Γ := scope) p base [] [] out yes
    have hc := comparePadded_look (Γ := scope) p bit yes no base [] [] out (by exact hp)
    exact hc.mono (show 3 ≤ 16 by decide)
  have hn : (xs.head?.isNone && ys.head?.isNone) = false := by
    cases xs <;> cases ys <;> simp_all
  by_cases hh : headBit bit xs.head? = headBit bit ys.head?
  · have hEq : paddedAgree bit xs ys ↔ paddedAgree bit xs.tail ys.tail := by
      simp only [paddedAgree_step bit xs ys, hh, true_and]
    have hchoice : (if paddedAgree bit xs ys then yes else no) =
        if paddedAgree bit xs.tail ys.tail then yes else no := if_congr hEq rfl rfl
    rw [hchoice]
    have hlt : xs.tail.length + ys.tail.length < xs.length + ys.length := by
      cases xs <;> cases ys <;> simp_all
      omega
    have hr := comparePaddedBody_runs (Γ := Γ) base bit yes no xs.tail ys.tail out
    have htc := compareTails_runs (Γ := Γ) p base xs ys out _ hr
    have hc := comparePadded_look (Γ := scope) p bit yes no base xs ys out
      (by simpa only [comparePair, hn, Bool.false_eq_true, ite_false, hh, ite_true] using htc)
    exact hc.mono (by omega)
  · have hfalse : ¬ paddedAgree bit xs ys := fun h => hh ((paddedAgree_step bit xs ys).mp h).1
    rw [ite_eq_right hfalse]
    have hp := comparePadded_push (Γ := scope) p base xs ys out no
    have hc := comparePadded_look (Γ := scope) p bit yes no base xs ys out
      (by simpa only [comparePair, hn, Bool.false_eq_true, ite_false, ite_eq_right hh] using hp)
    exact hc.mono (by omega)
termination_by xs.length + ys.length
decreasing_by exact hlt

theorem comparePadded_runs {Γ : Scope A} (base : Reg A) (bit : A → Bool) (yes no : A)
    (xs ys out : List A) :
    Runs Γ (comparePadded p bit yes no) (regs p base xs out ys)
      (regs p base xs ((if paddedAgree bit xs ys then yes else no) :: out) ys)
      (16 * (xs.length + ys.length + 1) + 1) :=
  Runs.tie (comparePaddedBody_runs p base bit yes no xs ys out)

theorem comparePadded_at {Γ : Scope A} (r : Reg A) (bit : A → Bool) (yes no : A) :
    Runs Γ (comparePadded p bit yes no) r
      (Function.update r p.output ((if paddedAgree bit (r p.table) (r p.index) then yes else no) :: r p.output))
      (16 * ((r p.table).length + (r p.index).length + 1) + 1) := by
  let result := if paddedAgree bit (r p.table) (r p.index) then yes else no
  have hr := comparePadded_runs (Γ := Γ) p r bit yes no (r p.table) (r p.index) (r p.output)
  have hs := regs_eq p r rfl rfl rfl
  have hu := write_output p r (r p.table) (r p.output) (r p.index) (result :: r p.output)
  rw [hs] at hr hu
  exact hr.congr_out hu.symm

end P1SolFactor.SolRows
