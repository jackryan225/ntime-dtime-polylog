import P1SolFactor.HeaderRead
import P1SolFactor.StackRead

namespace P1SolFactor

open OAI.Computability.IntegerMultiplication P1ProgEng SolRows

variable {R : Type}

private def headerPorts : Ports := ⟨2, 6, 5, by decide, by decide, by decide⟩

/-- Copy the site header and dispatch on its leading unary rule tag. -/
def readSiteHeader (next : ℕ → Prog (P1P5.EvalSym R)) : Prog (P1P5.EvalSym R) :=
  .join (copyAll headerPorts) (readSmallPtr 6 6 next)

theorem readSiteHeader_runs {Γ : Scope (P1P5.EvalSym R)} {r s : Reg (P1P5.EvalSym R)}
    (next : ℕ → Prog (P1P5.EvalSym R)) (tag : ℕ) (rest : List (P1P5.EvalSym R))
    (htag : tag ≤ 6) (h6 : r 6 = []) (hr : r 2 = P1P5.encPtr tag ++ rest) {cost : ℕ}
    (hn : Runs Γ (next tag) (Function.update r 6 rest) s cost) :
    Runs Γ (readSiteHeader next) r s (cost + 12 * (r 2).length + 4 * (tag + 1) + 5) := by
  let mid := Function.update r 6 (r 2)
  have hc := copyAll_at (Γ := Γ) headerPorts r
  change Runs Γ (copyAll headerPorts) r (Function.update r 6 (r 2 ++ r 6)) (12 * (r 2).length + 3) at hc
  rw [h6, List.append_nil] at hc
  have hmid : mid 6 = P1P5.encPtr tag ++ rest := by
    simpa only [mid, Function.update_self] using hr
  have hr' : Function.update mid 6 rest = Function.update r 6 rest := by
    simp only [mid, Function.update_idem]
  have hread := readSmallPtr_runs 6 6 tag htag next rest hmid (by rw [hr']; exact hn)
  exact (hc.join hread).mono (by omega)

end P1SolFactor
