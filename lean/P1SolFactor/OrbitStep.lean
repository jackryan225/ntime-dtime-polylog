import P1SolFactor.RowLookup
import P1SolFactor.Specification

namespace P1SolFactor.SolOrbit

open OAI.Computability.IntegerMultiplication P1ProgEng
open P1Benes.Tab

section Clear

variable {A : Type}

theorem write_twice (r : Reg A) (j : ℕ) (xs ys : List A) :
    Function.update (Function.update r j xs) j ys = Function.update r j ys := by
  funext k
  by_cases hk : k = j
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]

/-- Pop letters up to the first letter satisfying `stop` or the end of the stack. -/
def clearStep (j : ℕ) (stop : A → Bool) : Option A → Prog A
  | none => .pass
  | some a => if stop a then .pass else .join (.pop j) (.again 0)

def clearBody (j : ℕ) (stop : A → Bool) : Prog A := .look j (clearStep j stop)

def clearTo (j : ℕ) (stop : A → Bool) : Prog A := .tie (clearBody j stop)

private theorem clearBody_runs {Γ : Scope A} (r : Reg A) (j : ℕ) (stop : A → Bool)
    (tail : List A) (htail : ∀ a, tail.head? = some a → stop a = true) :
    ∀ xs : List A, (∀ a ∈ xs, stop a = false) →
    Runs (clearBody j stop :: Γ) (clearBody j stop) (Function.update r j (xs ++ tail))
      (Function.update r j tail) (7 * xs.length + 2) := by
  intro xs
  induction xs with
  | nil =>
    intro _
    have hhead : ((Function.update r j tail) j).head? = tail.head? := by rw [Function.update_self]
    have hpass : clearStep j stop tail.head? = .pass := by
      cases h : tail.head? with
      | none => rfl
      | some a => simp only [clearStep, htail a h, ite_true]
    have hrun := Runs.look' (c := clearStep j stop) (Γ := clearBody j stop :: Γ) hhead
      (Runs.of_prog hpass (Runs.pass (r := Function.update r j tail)))
    exact hrun
  | cons x xs ih =>
    intro hxs
    have hx := hxs x List.mem_cons_self
    have hrest : ∀ a ∈ xs, stop a = false := fun a ha => hxs a (List.mem_cons_of_mem x ha)
    have hpop : Runs (clearBody j stop :: Γ) (.pop j) (Function.update r j ((x :: xs) ++ tail))
        (Function.update r j (xs ++ tail)) 1 := (Runs.pop j).congr_out (by
      rw [Function.update_self, List.cons_append, List.tail_cons, write_twice])
    have hstep := hpop.join (Runs.again0 (ih hrest))
    have hhead : ((Function.update r j ((x :: xs) ++ tail)) j).head? = some x := by
      simp only [Function.update_self, List.cons_append, List.head?_cons]
    have hlook := Runs.look' (c := clearStep j stop) hhead
      (by simpa only [clearStep, hx, Bool.false_eq_true, ite_false] using hstep)
    exact hlook.mono (by simp only [List.length_cons]; omega)

theorem clearTo_runs {Γ : Scope A} {r : Reg A} (j : ℕ) (stop : A → Bool) (xs tail : List A)
    (hinput : r j = xs ++ tail) (hxs : ∀ a ∈ xs, stop a = false)
    (htail : ∀ a, tail.head? = some a → stop a = true) :
    Runs Γ (clearTo j stop) r (Function.update r j tail) (7 * xs.length + 3) := by
  have hin : Function.update r j (xs ++ tail) = r := by
    funext k
    by_cases hk : k = j
    · subst k
      rw [Function.update_self, hinput]
    · rw [Function.update_of_ne hk]
  have h := Runs.tie (clearBody_runs (Γ := Γ) r j stop tail htail xs hxs)
  rwa [hin] at h

end Clear

def mark : SwitchSym := .inr ()

def word (m x : ℕ) : List SwitchSym := List.ofFn fun i : Fin m => .inl (x.testBit i.val)

def wordStack (m x : ℕ) (tail : List SwitchSym) : List SwitchSym := word m x ++ mark :: tail

def bitValue : SwitchSym → Bool := Sum.elim id (fun _ => false)

def isMark : SwitchSym → Bool := Sum.elim (fun _ => false) (fun _ => true)

def permRows {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) : List (List SwitchSym) :=
  List.ofFn fun i => word m (π i).val

theorem encode_permRows {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) :
    SolRows.encode mark (permRows π) = encPermRows π := by
  simp only [SolRows.encode, permRows, encPermRows, List.flatMap_def, List.map_ofFn, Function.comp_def, word, mark]

theorem permRows_length {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) : (permRows π).length = 2 ^ m := List.length_ofFn

theorem permRows_getD {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) (i : Fin (2 ^ m)) :
    (permRows π).getD i.val [] = word m (π i).val := by
  have hi : i.val < (permRows π).length := by rw [permRows_length]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [permRows, List.getElem_ofFn, Fin.eta]

theorem permRows_wellFormed {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) (row : List SwitchSym)
    (hr : row ∈ permRows π) : row.length ≤ m ∧ mark ∉ row := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨List.length_ofFn.le, ?_⟩
  intro h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  cases hi

private theorem testBit_succ_div (x j : ℕ) : x.testBit (j + 1) = (x / 2).testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 2]

private theorem flip_div (x : ℕ) : flipT x / 2 = x / 2 := by
  unfold flipT
  split <;> omega

private theorem flip_low (x : ℕ) : (flipT x).testBit 0 = !(x.testBit 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, Nat.div_one]
  unfold flipT
  by_cases h : x % 2 = 1
  · rw [ite_eq_left h]
    have hx : (x - 1) % 2 ≠ 1 := by omega
    simp only [h, hx, decide_false, decide_true, Bool.not_true]
  · rw [ite_eq_right h]
    have hx : (x + 1) % 2 = 1 := by omega
    simp only [h, hx, decide_false, decide_true, Bool.not_false]

theorem wordStack_succ (m x : ℕ) (tail : List SwitchSym) :
    wordStack (m + 1) x tail = .inl (x.testBit 0) :: wordStack m (x / 2) tail := by
  simp only [wordStack, word, List.ofFn_succ, List.cons_append, Fin.val_zero, Fin.val_succ, testBit_succ_div]

theorem wordStack_flip (m x : ℕ) (tail : List SwitchSym) :
    wordStack (m + 1) (flipT x) tail = .inl (!(x.testBit 0)) :: wordStack m (x / 2) tail := by
  rw [wordStack_succ, flip_div, flip_low]

/-- Toggle the first bit of a nonempty little-endian word. -/
def flipLow (j : ℕ) : Prog SwitchSym := .look j fun
  | some (.inl b) => .join (.pop j) (.push j (.inl (!b)))
  | _ => .pass

theorem flipLow_runs {Γ : Scope SwitchSym} {r : Reg SwitchSym} (j m x : ℕ) (tail : List SwitchSym)
    (hr : r j = wordStack (m + 1) x tail) :
    Runs Γ (flipLow j) r (Function.update r j (wordStack (m + 1) (flipT x) tail)) 5 := by
  rw [wordStack_succ] at hr
  rw [wordStack_flip]
  have hpop : Runs Γ (.pop j) r (Function.update r j (wordStack m (x / 2) tail)) 1 :=
    (Runs.pop j).congr_out (by rw [hr, List.tail_cons])
  have hpush : Runs Γ (.push j (.inl (!(x.testBit 0)))) (Function.update r j (wordStack m (x / 2) tail))
      (Function.update r j (.inl (!(x.testBit 0)) :: wordStack m (x / 2) tail)) 1 :=
    (Runs.push j _).congr_out (by rw [Function.update_self, write_twice])
  have hhead : (r j).head? = some (.inl (x.testBit 0)) := by rw [hr, List.head?_cons]
  exact Runs.look' (o := some (.inl (x.testBit 0))) hhead (hpop.join hpush)

/-- Remove the bits and keep the word delimiter, including any data parked underneath it. -/
theorem clearWord_runs {Γ : Scope SwitchSym} {r : Reg SwitchSym} (j m x : ℕ) (tail : List SwitchSym)
    (hr : r j = wordStack m x tail) :
    Runs Γ (clearTo j isMark) r (Function.update r j (mark :: tail)) (7 * m + 3) := by
  have hbits : ∀ a ∈ word m x, isMark a = false := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rfl
  have htail : ∀ a, (mark :: tail).head? = some a → isMark a = true := by
    intro a ha
    have e : mark = a := Option.some.inj ha
    rw [← e]
    rfl
  have h := clearTo_runs (Γ := Γ) j isMark (word m x) (mark :: tail) hr hbits htail
  simpa only [word, List.length_ofFn] using h

/-- Convert the binary query, append the indicated row in front of the previous output,
and clear the temporary tally. The two port assignments share the index register. -/
def lookupWord (query table : SolRows.Ports) : Prog SwitchSym :=
  .join (SolRows.binaryIndex query mark bitValue mark)
    (.join (SolRows.lookup table mark) (clearTo table.index (fun _ => false)))

theorem lookupWord_runs {Γ : Scope SwitchSym} {r : Reg SwitchSym} (query table : SolRows.Ports)
    (hsame : query.index = table.index) {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) (x : Fin (2 ^ m))
    (tail : List SwitchSym) (hquery : r query.table = wordStack m x.val tail)
    (htable : r table.table = encPermRows π) (hindex : r table.index = []) :
    Runs Γ (lookupWord query table) r (Function.update r table.output (word m (π x).val ++ r table.output))
      (70 * (m + 1) * 2 ^ m) := by
  let idx := List.replicate x.val mark
  let r₁ := Function.update r table.index idx
  let answer := word m (π x).val ++ r table.output
  let r₂ := Function.update r₁ table.output answer
  have hinput := SolRows.regs_eq query r hquery rfl (show r query.index = [] by rw [hsame, hindex])
  have hbitMark (b : Bool) : (Sum.inl b : SwitchSym) ≠ mark := by
    intro h
    change Sum.inl b = (Sum.inr () : SwitchSym) at h
    cases h
  have hconv := SolRows.binaryIndex_testBits_runs query mark (Γ := Γ) r m x.val x.isLt bitValue
    Sum.inl (fun _ => rfl) hbitMark mark tail (r query.output)
  change Runs Γ (SolRows.binaryIndex query mark bitValue mark)
    (SolRows.regs query r (wordStack m x.val tail) (r query.output) [])
    (SolRows.regs query r (wordStack m x.val tail) (r query.output) idx) (25 * (m + x.val + 1)) at hconv
  rw [← SolRows.write_index query r (wordStack m x.val tail) (r query.output) [] idx, hinput, hsame] at hconv
  have hrows : r₁ table.table = SolRows.encode mark (permRows π) := by
    dsimp only [r₁]
    rw [encode_permRows, Function.update_of_ne table.table_ne_index, htable]
  have hidx : r₁ table.index = idx := Function.update_self _ _ _
  have hout : r₁ table.output = r table.output := Function.update_of_ne table.output_ne_index _ _
  have htableInput := SolRows.regs_eq table r₁ hrows hout hidx
  have hlt : x.val < (permRows π).length := by rw [permRows_length]; exact x.isLt
  have hlookup := SolRows.lookup_tally_runs table mark (Γ := Γ) r₁ m x.val mark (permRows π)
    (r table.output) hlt (permRows_wellFormed π)
  rw [permRows_getD π x, permRows_length π,
    ← SolRows.write_output table r₁ (SolRows.encode mark (permRows π)) (r table.output) idx answer,
    htableInput] at hlookup
  have hrest : r₂ table.index = idx ++ [] := by
    dsimp only [r₂]
    rw [Function.update_of_ne table.output_ne_index.symm, hidx, List.append_nil]
  have hclear := clearTo_runs (Γ := Γ) table.index (fun _ : SwitchSym => false) idx [] hrest
    (fun _ _ => rfl) (fun _ h => nomatch h)
  rw [List.length_replicate] at hclear
  have hfinal : Function.update r₂ table.index [] = Function.update r table.output answer := by
    funext k
    by_cases hk : k = table.index
    · subst k
      rw [Function.update_self, Function.update_of_ne table.output_ne_index.symm, hindex]
    by_cases ho : k = table.output
    · subst k
      simp only [r₂, Function.update_of_ne table.output_ne_index, Function.update_self]
    simp only [r₂, r₁, Function.update_of_ne hk, Function.update_of_ne ho]
  have hseq := hconv.join (hlookup.join (hclear.congr_out hfinal))
  have hm : m ≤ m * 2 ^ m := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos m)
  have htotal : m + x.val + 1 ≤ (m + 1) * 2 ^ m := by
    rw [Nat.add_mul, Nat.one_mul]
    have hx := x.isLt
    omega
  refine hseq.mono ?_
  simp only [Nat.mul_assoc]
  omega

def forwardQuery : SolRows.Ports := ⟨3, 5, 4, by decide, by decide, by decide⟩
def forwardTable : SolRows.Ports := ⟨1, 5, 4, by decide, by decide, by decide⟩
def inverseQuery : SolRows.Ports := ⟨5, 3, 4, by decide, by decide, by decide⟩
def inverseTable : SolRows.Ports := ⟨2, 3, 4, by decide, by decide, by decide⟩

/-- The current address lives in register 3. Register 4 is a temporary tally, and 5 holds the
intermediate row. Registers 1 and 2 contain the permutation and its inverse. -/
def rhoRegs (base : Reg SwitchSym) (P Q current work : List SwitchSym) : Reg SwitchSym
  | 1 => P
  | 2 => Q
  | 3 => current
  | 4 => []
  | 5 => work
  | j => base j

private theorem rhoRegs_write_current (base : Reg SwitchSym) (P Q current work new : List SwitchSym) :
    Function.update (rhoRegs base P Q current work) 3 new = rhoRegs base P Q new work := by
  funext j
  rcases j with _|_|_|_|_|_|j <;> rfl

private theorem rhoRegs_write_work (base : Reg SwitchSym) (P Q current work new : List SwitchSym) :
    Function.update (rhoRegs base P Q current work) 5 new = rhoRegs base P Q current new := by
  funext j
  rcases j with _|_|_|_|_|_|j <;> rfl

/-- One step of the Beneš looping rule, `π⁻¹ (flip (π (flip x)))`. -/
def rho : Prog SwitchSym :=
  .join (flipLow 3) (.join (lookupWord forwardQuery forwardTable) (.join (flipLow 5)
    (.join (clearTo 3 isMark) (.join (lookupWord inverseQuery inverseTable) (clearTo 5 isMark)))))

/-- One orbit step on the exact binary permutation tables. The delimiter and the parked data
under each word are preserved. Both temporary registers return to their entry configuration. -/
theorem rho_runs {Γ : Scope SwitchSym} {m : ℕ} (π : Equiv.Perm (Fin (2 ^ (m + 1))))
    (x : Fin (2 ^ (m + 1))) (base : Reg SwitchSym) (tail workTail : List SwitchSym) :
    let P := encPermRows π
    let Q := encPermRows π.symm
    let y := rhoT (tabOf π) (tabOf π.symm) x.val
    Runs Γ rho (rhoRegs base P Q (wordStack (m + 1) x.val tail) (mark :: workTail))
      (rhoRegs base P Q (wordStack (m + 1) y tail) (mark :: workTail))
      (180 * (m + 2) * 2 ^ (m + 1)) := by
  intro P Q y
  let a := P1Benes.Net.flip0 m x
  let b := π a
  let c := P1Benes.Net.flip0 m b
  have h₁ := flipLow_runs (Γ := Γ)
    (r := rhoRegs base P Q (wordStack (m + 1) x.val tail) (mark :: workTail)) 3 m x.val tail rfl
  rw [rhoRegs_write_current, flipT_val x] at h₁
  have h₂ := lookupWord_runs (Γ := Γ)
    (r := rhoRegs base P Q (wordStack (m + 1) a.val tail) (mark :: workTail))
    forwardQuery forwardTable rfl π a tail rfl rfl rfl
  change Runs Γ (lookupWord forwardQuery forwardTable) _
    (Function.update (rhoRegs base P Q (wordStack (m + 1) a.val tail) (mark :: workTail)) 5
      (wordStack (m + 1) b.val workTail)) _ at h₂
  rw [rhoRegs_write_work] at h₂
  have h₃ := flipLow_runs (Γ := Γ) (r := rhoRegs base P Q (wordStack (m + 1) a.val tail)
    (wordStack (m + 1) b.val workTail)) 5 m b.val workTail rfl
  rw [rhoRegs_write_work, flipT_val b] at h₃
  have h₄ := clearWord_runs (Γ := Γ) (r := rhoRegs base P Q (wordStack (m + 1) a.val tail)
    (wordStack (m + 1) c.val workTail)) 3 (m + 1) a.val tail rfl
  rw [rhoRegs_write_current] at h₄
  have h₅ := lookupWord_runs (Γ := Γ) (r := rhoRegs base P Q (mark :: tail)
    (wordStack (m + 1) c.val workTail)) inverseQuery inverseTable rfl π.symm c workTail rfl rfl rfl
  change Runs Γ (lookupWord inverseQuery inverseTable) _
    (Function.update (rhoRegs base P Q (mark :: tail) (wordStack (m + 1) c.val workTail)) 3
      (wordStack (m + 1) (π.symm c).val tail)) _ at h₅
  rw [rhoRegs_write_current] at h₅
  have h₆ := clearWord_runs (Γ := Γ) (r := rhoRegs base P Q (wordStack (m + 1) (π.symm c).val tail)
    (wordStack (m + 1) c.val workTail)) 5 (m + 1) c.val workTail rfl
  rw [rhoRegs_write_work] at h₆
  have hout : y = (π.symm c).val := by
    dsimp only [y, c, b, a, rhoT]
    rw [flipT_val, tabOf_getD, flipT_val, tabOf_getD]
  rw [hout]
  have hrun := h₁.join (h₂.join (h₃.join (h₄.join (h₅.join h₆))))
  have hscale : m + 2 ≤ (m + 2) * 2 ^ (m + 1) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  refine hrun.mono ?_
  simp only [Nat.mul_assoc, show m + 1 + 1 = m + 2 from rfl]
  omega

end P1SolFactor.SolOrbit
