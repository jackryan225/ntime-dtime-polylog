import P1Dispatch.Spec

namespace P1Dispatch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Int

/-- **(1) tight form.** -/
theorem ofTask_tight' {X : Type*} (q : X → List Bool × List Bool × List Bool) (β : X → ℕ)
    (ck : List Bool → List Bool → ℕ → Bool)
    (h : Task β (fun p => send (q p)) (fun p => send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ p : X,
      ProgAnswers Rc answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)) (c * (β p + 1)) := by
  exact ofTask_tight_proof q β ck h

open Classical in
/-- **(1) `P1Dispatch.ofTask`, form of D8.** -/
theorem ofTask' {X : Type*} (q : X → List Bool × List Bool × List Bool) (β : X → ℕ)
    (Ck : List Bool → List Bool → ℕ → Prop)
    (h : Task β (fun p => send (q p))
      (fun p => send (decide (Ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))))) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ p : X,
      ProgAnswers Rc answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (decide (Ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))
        (c * ((q p).1.length + (q p).2.1.length + (q p).2.2.length + β p + 1)) := by
  exact ofTask_proof q β Ck h

/-- **(1) finitely many families, one constant.** -/
theorem ofTask_fin' {ι : Type*} [Fintype ι] {X : Type*} (q : X → List Bool × List Bool × List Bool)
    (β : X → ℕ) (ck : ι → List Bool → List Bool → ℕ → Bool)
    (h : ∀ k, Task β (fun p => send (q p))
      (fun p => send (ck k (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))) :
    ∃ (Rc : ι → Prog Ltr) (c : ℕ), ∀ k p,
      ProgAnswers (Rc k) answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (ck k (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)) (c * (β p + 1)) := by
  exact ofTask_fin_proof q β ck h

end P1Dispatch

#print axioms P1Dispatch.ofTask_tight'
#print axioms P1Dispatch.ofTask'
#print axioms P1Dispatch.ofTask_fin'
