import P1SolFactor.NodeCursor

namespace P1SolFactor.SolOrbit

open OAI.Computability.IntegerMultiplication P1ProgEng

private theorem transferFrame {A : Type} {Γ : Scope A} {Prg : Prog A} {r : Reg A} (p : SolRows.Ports)
    {t o t' o' : List A} {cost : ℕ} (h : Runs Γ Prg (SolRows.regs p r t o (r p.index))
      (SolRows.regs p r t' o' (r p.index)) cost) (ht : r p.table = t) (ho : r p.output = o) :
    Runs Γ Prg r (Function.update (Function.update r p.table t') p.output o') cost := by
  have hs := SolRows.regs_eq p r ht ho (show r p.index = r p.index from rfl)
  rw [← SolRows.write_output p r t' o (r p.index) o',
    ← SolRows.write_table p r t o (r p.index) t', hs] at h
  exact h

theorem moveAll_at {A : Type} {Γ : Scope A} {r : Reg A} (p : SolRows.Ports) :
    Runs Γ (SolRows.transferPrefix p (fun _ => false)) r
      (Function.update (Function.update r p.table []) p.output (r p.table ++ r p.output))
      (9 * (r p.table).length + 3) :=
  transferFrame p (SolRows.moveAll_runs p r (r p.table) (r p.output) (r p.index)) rfl rfl

theorem emitRow_at {Γ : Scope SwitchSym} {r : Reg SwitchSym} (p : SolRows.Ports)
    (row tail : List SwitchSym) (hrow : mark ∉ row) (hs : r p.table = row ++ mark :: tail) :
    Runs Γ (SolRows.transferPrefix p (fun x => decide (x = mark))) r
      (Function.update (Function.update r p.table tail) p.output (row ++ r p.output))
      (9 * row.length + 3) :=
  transferFrame p (SolRows.emitRow_runs p mark r row tail (r p.output) (r p.index) hrow) hs rfl

theorem takePermTable_at {Γ : Scope SwitchSym} {r : Reg SwitchSym} (p : SolRows.Ports) {m : ℕ}
    (π : Equiv.Perm (Fin (2 ^ m))) (hm : 0 < m) (tail : List SwitchSym)
    (hs : r p.table = encPermRows π ++ mark :: tail) :
    Runs Γ (SolRows.takeTable p mark) r
      (Function.update (Function.update r p.table tail) p.output (encPermRows π ++ r p.output))
      (15 * ((m + 1) * 2 ^ m) + 3) :=
  transferFrame p (takePermTable_runs p r π hm tail (r p.output) (r p.index)) hs rfl

theorem clearAll_runs {A : Type} {Γ : Scope A} {r : Reg A} (j : ℕ) :
    Runs Γ (clearTo j (fun _ => false)) r (Function.update r j []) (7 * (r j).length + 3) :=
  clearTo_runs j (fun _ => false) (r j) [] (by rw [List.append_nil]) (fun _ _ => rfl) (fun _ h => nomatch h)

end P1SolFactor.SolOrbit
