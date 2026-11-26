import P1SolFactor.HeaderRead
import P1SolFactor.ScalarOutput

namespace P1SolFactor

open OAI.Computability.IntegerMultiplication P1ProgEng SolRows SolHalf
open scoped Classical

noncomputable section

variable {R : Type}

/-- Register state after prepending the truth bit of a local test. -/
def putDecision (j : ℕ) (r : Reg (P1P5.EvalSym R)) (ok : Prop) : Reg (P1P5.EvalSym R) :=
  Function.update r j (inputBit (decide ok) :: r j)

theorem takeDecision_runs {Γ : Scope (P1P5.EvalSym R)} {r s : Reg (P1P5.EvalSym R)}
    (j : ℕ) (ok : Prop) (next : Bool → Prog (P1P5.EvalSym R)) {cost : ℕ}
    (hn : Runs Γ (next (decide ok)) r s cost) :
    Runs Γ (takeInputBit j next) (putDecision j r ok) s (cost + 4) := by
  have hhead : putDecision j r ok j = inputBit (decide ok) :: r j := by
    rw [putDecision, Function.update_self]
  have hr : Function.update (putDecision j r ok) j (r j) = r := by
    rw [putDecision, Function.update_idem, Function.update_eq_self]
  exact takeInputBit_runs j next _ (r j) hhead (by rw [hr]; exact hn)

/-- Check the second condition only when the first succeeded, with one final decision letter. -/
def andDecision (j : ℕ) (first second : Prog (P1P5.EvalSym R)) : Prog (P1P5.EvalSym R) :=
  .join first (takeInputBit j (fun b => if b then second else .push j (inputBit false)))

theorem andDecision_runs {Γ : Scope (P1P5.EvalSym R)} {r : Reg (P1P5.EvalSym R)}
    (j : ℕ) {p q : Prop} {first second : Prog (P1P5.EvalSym R)} {c₁ c₂ : ℕ}
    (hf : Runs Γ first r (putDecision j r p) c₁)
    (hs : Runs Γ second r (putDecision j r q) c₂) :
    Runs Γ (andDecision j first second) r (putDecision j r (p ∧ q)) (c₁ + c₂ + 7) := by
  let next : Bool → Prog (P1P5.EvalSym R) := fun b => if b then second else .push j (inputBit false)
  have hn : Runs Γ (next (decide p)) r (putDecision j r (p ∧ q)) (c₂ + 1) := by
    by_cases h : p
    · simpa only [next, h, decide_true, ite_true, true_and] using hs.mono (Nat.le_succ _)
    · simpa only [next, h, decide_false, Bool.false_eq_true, ite_false, false_and, putDecision] using
        (Runs.push (Γ := Γ) (r := r) j (inputBit false)).mono (show 1 ≤ c₂ + 1 by omega)
  exact (hf.join (takeDecision_runs j p next hn)).mono (by omega)

theorem compareDecision_runs {Γ : Scope (P1P5.EvalSym R)} (p : Ports) (r : Reg (P1P5.EvalSym R)) :
    Runs Γ (comparePadded p decodeInputBit (inputBit true) (inputBit false)) r
      (putDecision p.output r (paddedAgree decodeInputBit (r p.table) (r p.index)))
      (16 * ((r p.table).length + (r p.index).length + 1) + 1) := by
  have h := comparePadded_at (Γ := Γ) p r decodeInputBit (inputBit true) (inputBit false)
  by_cases hok : paddedAgree decodeInputBit (r p.table) (r p.index)
  · simpa only [putDecision, hok, ite_true, decide_true] using h
  · simpa only [putDecision, ite_eq_right hok, decide_eq_false_iff_not.mpr hok] using h

variable [CommRing R]

/-- Consume the decision and prepend the corresponding scalar-weighted value. -/
def emitDecision (j : ℕ) : Prog (P1P5.EvalSym R) :=
  takeInputBit j writeFactor

theorem emitDecision_runs {Γ : Scope (P1P5.EvalSym R)} (j : ℕ) (r : Reg (P1P5.EvalSym R))
    (ok : Prop) (c : R) (hc : (r 3).head? = some (.inl c)) :
    Runs Γ (emitDecision j) (putDecision j r ok)
      (Function.update r 0 (.inl (c * (if ok then 1 else 0)) :: r 0)) 6 := by
  apply takeDecision_runs j ok writeFactor
  have h := writeFactor_runs (Γ := Γ) r (decide ok) c hc
  by_cases hok : ok
  · simpa only [hok, decide_true, ite_true] using h
  · simpa only [ite_eq_right hok, decide_eq_false_iff_not.mpr hok, Bool.false_eq_true, ite_false] using h

end

end P1SolFactor
