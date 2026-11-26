import P1SolFactor.PaddedViews
import P1ProgEng.Lib

namespace P1SolFactor

open OAI.Computability.IntegerMultiplication P1ProgEng
open SolHalf

variable {A R : Type}

/-- Consume the first letter and continue with its value. -/
def takeLetter (j : ℕ) (next : A → Prog A) : Prog A :=
  .look j fun o => o.elim .pass fun x => .join (.pop j) (next x)

theorem takeLetter_runs {Γ : Scope A} {r s : Reg A} (j : ℕ) (next : A → Prog A)
    (x : A) (tail : List A) (hx : r j = x :: tail) {cost : ℕ}
    (hn : Runs Γ (next x) (Function.update r j tail) s cost) :
    Runs Γ (takeLetter j next) r s (cost + 4) := by
  have hp : Runs Γ (.pop j) r (Function.update r j tail) 1 := by
    simpa only [hx, List.tail_cons] using (Runs.pop (Γ := Γ) (r := r) j)
  have hhead : (r j).head? = some x := by rw [hx, List.head?_cons]
  exact (Runs.look' (c := fun o => o.elim .pass fun x => .join (.pop j) (next x)) hhead
    (hp.join hn)).mono (by omega)

private def ptrStop : P1P5.EvalSym R → Bool
  | .inl _ => false
  | .inr tok => decide (tok = P1P5.Tok.endPtr)

/-- Read a unary pointer whose value is bounded by a compile-time limit. -/
def readSmallPtr (j : ℕ) : ℕ → (ℕ → Prog (P1P5.EvalSym R)) → Prog (P1P5.EvalSym R)
  | 0, next => takeLetter j fun x => if ptrStop x then next 0 else .pass
  | limit + 1, next => takeLetter j fun x =>
    if ptrStop x then next 0
    else if decodeInputBit x then readSmallPtr j limit (fun n => next (n + 1))
    else .pass

theorem readSmallPtr_runs {Γ : Scope (P1P5.EvalSym R)} {r s : Reg (P1P5.EvalSym R)}
    (j limit d : ℕ) (hlim : d ≤ limit) (next : ℕ → Prog (P1P5.EvalSym R)) (tail : List (P1P5.EvalSym R))
    (hr : r j = P1P5.encPtr d ++ tail) {cost : ℕ}
    (hn : Runs Γ (next d) (Function.update r j tail) s cost) :
    Runs Γ (readSmallPtr j limit next) r s (cost + 4 * (d + 1)) := by
  induction d generalizing r limit next with
  | zero =>
    have he : r j = .inr P1P5.Tok.endPtr :: tail := by
      simpa only [P1P5.encPtr, List.replicate_zero, List.nil_append, List.singleton_append] using hr
    have hstop : ptrStop (.inr P1P5.Tok.endPtr : P1P5.EvalSym R) = true := rfl
    cases limit with
    | zero =>
      exact takeLetter_runs j _ _ tail he (by simpa only [hstop, ite_true] using hn)
    | succ rest =>
      exact takeLetter_runs j _ _ tail he (by simpa only [hstop, ite_true] using hn)
  | succ d ih =>
    cases limit with
    | zero => omega
    | succ limit =>
      let prev := Function.update r j (P1P5.encPtr d ++ tail)
      have he : r j = .inr P1P5.Tok.one :: (P1P5.encPtr d ++ tail) := by
        simpa only [P1P5.encPtr, List.replicate_succ, List.cons_append] using hr
      have hprev : prev j = P1P5.encPtr d ++ tail := by simp only [prev, Function.update_self]
      have hc : Function.update prev j tail = Function.update r j tail := by
        simp only [prev, Function.update_idem]
      have hi := ih (r := prev) limit (by omega) (fun n => next (n + 1)) hprev (by rw [hc]; exact hn)
      have hstop : ptrStop (.inr P1P5.Tok.one : P1P5.EvalSym R) = false := rfl
      have hone : decodeInputBit (.inr P1P5.Tok.one : P1P5.EvalSym R) = true := rfl
      have hstep : Runs Γ (takeLetter j fun x => if ptrStop x then next 0
          else if decodeInputBit x then readSmallPtr j limit (fun n => next (n + 1)) else .pass) r s
          ((cost + 4 * (d + 1)) + 4) :=
        takeLetter_runs j _ _ _ he (by simpa only [hstop, Bool.false_eq_true, ite_false, hone, ite_true] using hi)
      exact hstep.mono (by omega)

/-- Consume one encoded bit and continue with the decoded value. -/
def takeInputBit (j : ℕ) (next : Bool → Prog (P1P5.EvalSym R)) : Prog (P1P5.EvalSym R) :=
  takeLetter j fun x => next (decodeInputBit x)

theorem takeInputBit_runs {Γ : Scope (P1P5.EvalSym R)} {r s : Reg (P1P5.EvalSym R)}
    (j : ℕ) (next : Bool → Prog (P1P5.EvalSym R)) (b : Bool) (tail : List (P1P5.EvalSym R))
    (hx : r j = inputBit b :: tail) {cost : ℕ}
    (hn : Runs Γ (next b) (Function.update r j tail) s cost) :
    Runs Γ (takeInputBit j next) r s (cost + 4) :=
  takeLetter_runs j (fun x => next (decodeInputBit x)) _ tail hx (by simpa only [decodeInputBit_inputBit] using hn)

end P1SolFactor
