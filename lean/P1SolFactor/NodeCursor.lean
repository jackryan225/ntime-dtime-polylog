import P1SolFactor.OrbitStep
import P1SolFactor.StackTransfer

namespace P1SolFactor.SolOrbit

open OAI.Computability.IntegerMultiplication P1ProgEng

theorem wordStack_zero (m : ℕ) (tail : List SwitchSym) :
    wordStack m 0 tail = List.replicate m (.inl false) ++ mark :: tail := by
  simp [wordStack, word, List.ofFn_const]

/-- At full width, the even-address cursor wraps to the all-zero word. -/
theorem wordStack_wrap (m : ℕ) (tail : List SwitchSym) :
    wordStack m (2 ^ m) tail = wordStack m 0 tail := by
  have h (i : Fin m) : (2 ^ m).testBit i.val = false := Nat.testBit_two_pow_of_ne i.isLt.ne'
  simp [wordStack, word, h]

theorem wordStack_wrapEven (m : ℕ) (tail : List SwitchSym) :
    wordStack (m + 1) (2 * 2 ^ m) tail = wordStack (m + 1) 0 tail := by
  rw [Nat.mul_comm 2, ← pow_succ]
  exact wordStack_wrap _ _

def zeroCursorStep (p : SolRows.Ports) : Option SwitchSym → Prog SwitchSym
  | some (.inl b) => .join (.pop p.table) (.join (.again 0)
      (.join (.push p.table (.inl b)) (.push p.output (.inl false))))
  | _ => .pass

def zeroCursorBody (p : SolRows.Ports) : Prog SwitchSym := .look p.table (zeroCursorStep p)

/-- Read the width of the first row and prepend that many zero bits. -/
def zeroCursor (p : SolRows.Ports) : Prog SwitchSym := .tie (zeroCursorBody p)

private theorem zeroCursorBody_runs {Γ : Scope SwitchSym} (p : SolRows.Ports) (base : Reg SwitchSym)
    (tail output index : List SwitchSym) : ∀ m x : ℕ,
      Runs (zeroCursorBody p :: Γ) (zeroCursorBody p)
        (SolRows.regs p base (wordStack m x tail) output index)
        (SolRows.regs p base (wordStack m x tail) (List.replicate m (.inl false) ++ output) index)
        (12 * m + 2) := by
  intro m
  induction m with
  | zero =>
    intro x
    let r := SolRows.regs p base (mark :: tail) output index
    have hhead : (r p.table).head? = some mark := by simp only [r, SolRows.regs_table, List.head?_cons]
    exact Runs.look' (c := zeroCursorStep p) hhead (Runs.pass (Γ := zeroCursorBody p :: Γ) (r := r))
  | succ m ih =>
    intro x
    let low := x.testBit 0
    let rest := wordStack m (x / 2) tail
    let zeros := List.replicate m (Sum.inl false : SwitchSym) ++ output
    let scope := zeroCursorBody p :: Γ
    let cfg (a b : List SwitchSym) := SolRows.regs p base a b index
    have hpop : Runs scope (.pop p.table) (cfg (.inl low :: rest) output) (cfg rest output) 1 :=
      (Runs.pop p.table).congr_out (by simp only [cfg, SolRows.regs_table, List.tail_cons, SolRows.write_table])
    have hw₁ : Runs scope (.push p.table (.inl low)) (cfg rest zeros) (cfg (.inl low :: rest) zeros) 1 :=
      (Runs.push p.table _).congr_out (by simp only [cfg, SolRows.regs_table, SolRows.write_table])
    have hw₂ : Runs scope (.push p.output (.inl false)) (cfg (.inl low :: rest) zeros)
        (cfg (.inl low :: rest) (.inl false :: zeros)) 1 :=
      (Runs.push p.output _).congr_out (by simp only [cfg, SolRows.regs_output, SolRows.write_output])
    have hhead : ((cfg (.inl low :: rest) output) p.table).head? = some (.inl low) := by
      simp only [cfg, SolRows.regs_table, List.head?_cons]
    have hstep := hpop.join ((Runs.again0 (ih (x / 2))).join (hw₁.join hw₂))
    have h := Runs.look' (c := zeroCursorStep p) hhead hstep
    rw [wordStack_succ, List.replicate_succ, List.cons_append]
    exact h.mono (by omega)

theorem encPermRows_first {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) :
    ∃ tail, encPermRows π = wordStack m (π ⟨0, Nat.two_pow_pos m⟩).val tail := by
  cases ht : permRows π with
  | nil =>
    have hsize := permRows_length π
    rw [ht, List.length_nil] at hsize
    exact (Nat.ne_of_gt (Nat.two_pow_pos m) hsize.symm).elim
  | cons row rows =>
    have he := permRows_getD π ⟨0, Nat.two_pow_pos m⟩
    change (permRows π).getD 0 [] = word m (π ⟨0, Nat.two_pow_pos m⟩).val at he
    rw [ht, List.getD_cons_zero] at he
    refine ⟨SolRows.encode mark rows, ?_⟩
    rw [← encode_permRows, ht, he]
    simp only [SolRows.encode, List.flatMap_cons, List.append_assoc, List.singleton_append, wordStack]

theorem zeroCursor_runs {Γ : Scope SwitchSym} {r : Reg SwitchSym} (p : SolRows.Ports) {m : ℕ}
    (π : Equiv.Perm (Fin (2 ^ m))) (tail : List SwitchSym) (htable : r p.table = encPermRows π)
    (hout : r p.output = mark :: tail) :
    Runs Γ (zeroCursor p) r (Function.update r p.output (wordStack m 0 tail)) (12 * m + 3) := by
  obtain ⟨rest, hrest⟩ := encPermRows_first π
  let v := (π ⟨0, Nat.two_pow_pos m⟩).val
  have hr : r p.table = wordStack m v rest := htable.trans hrest
  have hstate := SolRows.regs_eq p r hr hout (show r p.index = r p.index from rfl)
  have h := Runs.tie (zeroCursorBody_runs (Γ := Γ) p r rest (mark :: tail) (r p.index) m v)
  rw [← wordStack_zero, ← SolRows.write_output p r (wordStack m v rest) (mark :: tail)
    (r p.index) (wordStack m 0 tail), hstate] at h
  exact h

/-- Length of a permutation table, including the row separators. -/
theorem encPermRows_length {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) :
    (encPermRows π).length = (m + 1) * 2 ^ m := by
  simp [encPermRows, List.length_flatten, List.map_ofFn, Function.comp_def, List.ofFn_const, Nat.mul_comm]

theorem takePermTable_runs {Γ : Scope SwitchSym} (p : SolRows.Ports) (base : Reg SwitchSym) {m : ℕ}
    (π : Equiv.Perm (Fin (2 ^ m))) (hm : 0 < m) (tail output index : List SwitchSym) :
    Runs Γ (SolRows.takeTable p mark)
      (SolRows.regs p base (encPermRows π ++ mark :: tail) output index)
      (SolRows.regs p base tail (encPermRows π ++ output) index) (15 * ((m + 1) * 2 ^ m) + 3) := by
  have hrow : ∀ row ∈ permRows π, row ≠ [] ∧ mark ∉ row := by
    intro row hr
    have hc := (permRows_wellFormed π row hr).2
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨?_, hc⟩
    intro h
    have hlen : (word m (π q).val).length = m := List.length_ofFn
    rw [h, List.length_nil] at hlen
    omega
  have h := SolRows.takeTable_runs p mark (Γ := Γ) base (permRows π) tail output index hrow
  rwa [encode_permRows π, encPermRows_length π] at h

end P1SolFactor.SolOrbit
