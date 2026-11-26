import P1ChkFinal.ProgC13link
import P1ProgDir.FamTask

/-!
# P1ChkFinal.FamC13link: the C13link program as `FamProg` with the cone budget of D14 (skeleton; lane P1-lean-greedy)

`progC13link` (ProgC13link.lean) gives a Task with budget `budget c + βW`, where `βW` is the budget of the cone program `WHyp`
(P1-lean-eval, Sol P1-sol-cone). D14: `βW ≤ c (Λ+1)(|u|+|x|+|ρ|) + 2^{O(C Mbar)} poly(log t)` with `Λ + 1 ≤ p + 1`, so the
budget has the factor `p + 1` of `lpCost2` on the linear part. `famProg_of_task` (FamTask.lean) takes only `budget c`.
* `FamProgBetaTarget`: the converter with an extra budget `βW` bounded in the D14 form (target of a Sol prover).
* `famC13link_of`: the C13link `FamProg` from that converter, `progC13link` and the cone program; waits only for the cone
  (`hW`) and the D14 bound of its budget (`hβ`), plus the Poly inputs of `progC13link` (`hrq`, `hdec`, `hfb`, `hM`).
-/

namespace P1ChkFinal.FamC13

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module P1Int

/-- The D14 form of a budget: `cβ (p + 1)(|x| + |u| + |ρ|) + (log₂(|x|+1) + |ρ| + 1)^cβ`. -/
def BetaBound (a b cβ : ℕ) (q : Qry) : ℕ :=
  cβ * (lpP2 a b q.1.length + 1) * (q.1.length + q.2.1.length + q.2.2.length) +
    (Nat.log 2 (q.1.length + 1) + q.2.2.length + 1) ^ cβ

/-- **Target: `famProg_of_task` with an extra budget in the D14 form** (statement only). -/
def FamProgBetaTarget : Prop :=
  ∀ {s : ℝ}, s ≤ 1 → ∀ {a b : ℕ}, 1 ≤ b → ∀ (ck : List Bool → List Bool → ℕ → Bool) (c cβ : ℕ)
    (βW : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) → ℕ),
    (∀ p, βW p ≤ BetaBound a b cβ p.val) →
    Code.Task (fun p : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) => budget c p.val + βW p)
      (fun p => send p.val) (fun p => send (ck p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) →
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc ck s a b cc n₂

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

open scoped Classical in
/-- **C13link (family 12) as `FamProg`**, from the converter, the cone program `hW` with its D14 bound `hβ`, and the inputs
of `progC13link`. -/
theorem famC13link_of (hconv : FamProgBetaTarget) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (bs : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims) (Wof : List Bool → List Bool → ℕ → F)
    (βW : QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) → ℕ) (cβ : ℕ) (hβ : ∀ p, βW p ≤ BetaBound a b cβ p.val)
    (hbh : BatchHyp) (hl : LenHyp) (hM : ∀ n, (dims n).fixedLen ≤ lpM2 s a b n)
    (hW : WHyp bs Wof (lpM2 s a b) (fun n => lpK2 a b n - 4) βW)
    (hrq : Poly (fun z : (List Bool × List Bool) × List Bool => (rqLink dims z, z)))
    (hdec : Poly (decLink bs))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC13 (dims n))) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C13linkw bs dims Wof x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := progC13link bs dims Wof (lpM2 s a b) (fun n => lpK2 a b n - 4) βW hbh hl hM hW hrq hdec hfb
  exact hconv hs hb (fun x u i => decide (C13linkw bs dims Wof x u i)) c cβ βW hβ T

end P1ChkFinal.FamC13

#print axioms P1ChkFinal.FamC13.famC13link_of
