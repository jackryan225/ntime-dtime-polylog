import P1SolFactor.FactorSpec
import P1ProgEng.Lib

namespace P1SolFactor

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net P1ProgEng
open scoped Classical

noncomputable section

variable {R : Type} [CommRing R]

private def takeScalar : Option (P1P5.EvalSym R) → Prog (P1P5.EvalSym R)
  | some (.inl c) => .push 0 (.inl c)
  | _ => .push 0 (.inl 0)

/-- Prepend the supplied scalar for a successful test, or zero for a failed test. -/
def writeFactor (accepted : Bool) : Prog (P1P5.EvalSym R) :=
  if accepted then .look 3 takeScalar else .push 0 (.inl 0)

theorem writeFactor_runs {Γ : Scope (P1P5.EvalSym R)} (r : Reg (P1P5.EvalSym R))
    (accepted : Bool) (c : R) (hc : (r 3).head? = some (.inl c)) :
    Runs Γ (writeFactor accepted) r
      (Function.update r 0 (.inl (c * (if accepted then 1 else 0)) :: r 0)) 2 := by
  cases accepted
  · simp only [writeFactor, Bool.false_eq_true, ite_false, mul_zero]
    exact (Runs.push (Γ := Γ) (r := r) 0 (Sum.inl (0 : R))).mono (by decide : 1 ≤ 2)
  · simp only [writeFactor, ite_true, mul_one]
    exact Runs.look' (c := takeScalar) hc (Runs.push 0 (Sum.inl c))

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings) (u : (rnState V B I σ ha).network.Site) (c : R)

theorem factorRegsWith_scalar : factorRegsWith V B L I σ ha bset u c 3 = [.inl c] := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin <;> cases loc <;> simp [factorRegsWith]

theorem factorRegsWith_out : factorRegsWith V B L I σ ha bset u c 0 = [] := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin <;> cases loc <;> simp [factorRegsWith, factor0Regs]

/-- The twin-site condition is true for every half-label. The success branch writes its value. -/
theorem writeFactor_twin_runs {Γ : Scope (P1P5.EvalSym R)} {r : Reg (P1P5.EvalSym R)}
    (z : (rnState V B I σ ha).network.Half u) (htwin : u.1.2 = true)
    (hc : (r 3).head? = some (.inl c)) :
    Runs Γ (writeFactor true) r
      (Function.update r 0 (.inl (c * (if rnSiteOK V B L I σ ha bset u z then 1 else 0)) :: r 0)) 2 := by
  have hok : rnSiteOK V B L I σ ha bset u z := by simp [rnSiteOK, htwin]
  simpa [hok] using writeFactor_runs r true c hc

end RoutedSite

end

end P1SolFactor
