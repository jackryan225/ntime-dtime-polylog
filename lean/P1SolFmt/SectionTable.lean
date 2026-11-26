import P1SolFmt.FigureTools
import P1Wit.Layout

namespace P1SolFmt.SolFormat

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip P1Wit SolFigure

variable {X : Type} {r : Regime X}

private theorem mem_table (i : ℕ) (hi : i < 12) (f : Mem → X → ℕ) (z : X → ℕ) :
    ([f .layout, f .outAddr, f .outDisp, f .outFar, f .inAddr, f .inDisp,
      f .inFar, f .width, f .colour, f .offset, f .energy, f .terms][i]?).getD z =
      f (Mem.ofCode i) := by
  interval_cases i <;> rfl

/-- Dispatch the section number to the appropriate entry in the witness layout. -/
theorem sectionFigure (d : X → Dims) {s : X → ℕ}
    (hs : Realizes r s) (htop : Realizes r (fun x => (d x).top))
    (f : X → Kind → ℕ)
    (htrit : Figure r (fun x => f x .trit))
    (hstart : Figure r (fun x => f x .start))
    (hprev : Figure r (fun x => f x .prevOwn))
    (hnext : Figure r (fun x => f x .nextOwn))
    (hguess : Figure r (fun x => f x .guess))
    (hlev : ∀ k : Mem, Figure r (fun x => f x (.lev ((s x - 5) / 12) k)))
    (homega : Figure r (fun x => f x .Omega))
    (hchain : Figure r (fun x => f x .chain))
    (hzero : Figure r (fun x => f x .unused)) :
    Figure r (fun x => f x ((d x).kind (s x))) := by
  let fix := fun n => Staff.Realizes.fix (r := r) n
  let initial := [fun x => f x .trit, fun x => f x .start, fun x => f x .prevOwn,
    fun x => f x .nextOwn, fun x => f x .guess]
  let fLev := fun (k : Mem) x => f x (.lev ((s x - 5) / 12) k)
  let level := [fLev .layout, fLev .outAddr, fLev .outDisp, fLev .outFar, fLev .inAddr,
    fLev .inDisp, fLev .inFar, fLev .width, fLev .colour, fLev .offset, fLev .energy, fLev .terms]
  have hInitial : ∀ a ∈ initial, Figure r a := by
    intro a ha
    simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h <;> subst a <;> assumption
  have hLevel : ∀ a ∈ level, Figure r a := by
    intro a ha
    simp only [level, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h <;> subst a <;> exact hlev _
  have hOffset := (hs.minused (fix 5)).rem (fix 12)
  have hN := (fix 12).times (htop.plus (fix 1))
  have h := (figure_lookup initial hInitial hzero hs).variant
    ((figure_lookup level hLevel hzero hOffset).variant
      (homega.variant (hchain.variant hzero (hs.below ((fix 7).plus hN)))
        (hs.below ((fix 6).plus hN))) (hs.below ((fix 5).plus hN))) (hs.below (fix 5))
  convert h using 1
  funext x
  by_cases hi : s x < 5
  · interval_cases s x <;> norm_num [Dims.kind, initial]
  have hs0 : s x ≠ 0 := by omega
  have hs1 : s x ≠ 1 := by omega
  have hs2 : s x ≠ 2 := by omega
  have hs3 : s x ≠ 3 := by omega
  have hs4 : s x ≠ 4 := by omega
  simp only [Dims.kind, hi, hs0, hs1, hs2, hs3, hs4, ite_false, level]
  rw [mem_table _ (Nat.mod_lt _ (by decide))]
  by_cases hh : s x < 5 + 12 * ((d x).top + 1)
  · rw [ite_eq_left hh, ite_eq_left hh]
  rw [ite_eq_right hh, ite_eq_right hh]
  by_cases ho : s x = 5 + 12 * ((d x).top + 1)
  · simp only [ho, ite_eq_left, show 5 + 12 * ((d x).top + 1) < 6 + 12 * ((d x).top + 1) by omega]
  have hn : ¬s x < 6 + 12 * ((d x).top + 1) := by omega
  rw [ite_eq_right ho, ite_eq_right hn]
  by_cases hc : s x = 6 + 12 * ((d x).top + 1)
  · simp only [hc, ite_eq_left, show 6 + 12 * ((d x).top + 1) < 7 + 12 * ((d x).top + 1) by omega]
  have hn' : ¬s x < 7 + 12 * ((d x).top + 1) := by omega
  rw [ite_eq_right hc, ite_eq_right hn']

end P1SolFmt.SolFormat
