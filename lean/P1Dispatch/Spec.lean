import P1Dispatch.Runs

/-!
# P1Dispatch.Spec: proofs of `ofTask_tight`, `ofTask`, `ofTask_fin` (texts in `P1Dispatch.Statement`)

Owner: P1-lean-dispatch. `Rc = ofTaskProg c = conv ; c`, where `c` is the program of the Task.
Cost: `conv` takes `19 S + 43` steps (`S = |x| + |u| + |ρ|`, `conv_run`), the Task `t ≤ C (β + 1)` steps; and the
Task run itself shrinks register 0 from `2 S + 5` letters to one letter, so `2 S + 4 ≤ t` (`run_len_le`).
-/

namespace P1Dispatch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Int

theorem progAnswers_mono {A : Type} {R : Prog A} {ans : Option A → Bool} {regs : Reg A} {v : Bool}
    {B B' : ℕ} (h : ProgAnswers R ans regs v B) (hB : B ≤ B') : ProgAnswers R ans regs v B' := by
  obtain ⟨n, hn, r, hr, ha⟩ := h
  exact ⟨n, hn.trans hB, r, hr, ha⟩

theorem size_list : ∀ l : List Bool, size l = 2 * l.length + 1
  | [] => rfl
  | b :: l => by
    rw [size_cons, size_bit, size_list l, List.length_cons]
    ring

theorem count_send_triple (x u ρ : List Bool) :
    (send (x, u, ρ)).count = 2 * (x.length + u.length + ρ.length) + 5 := by
  have h : (send (x, u, ρ)).count = size (x, u, ρ) := rfl
  rw [h]
  simp only [size_prod, size_list]
  ring

/-- The empty deck. -/
def emptyDeck : Deck := fun _ => []

theorem letters_emptyDeck (k : ℕ) : letters emptyDeck k = [] := rfl

theorem ofTask_tight_proof {X : Type*} (q : X → List Bool × List Bool × List Bool) (β : X → ℕ)
    (ck : List Bool → List Bool → ℕ → Bool)
    (h : Task β (fun p => send (q p)) (fun p => send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ p : X,
      ProgAnswers Rc answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)) (c * (β p + 1)) := by
  obtain ⟨c, C, hc⟩ := h
  refine ⟨ofTaskProg c, 20 * C + 45, fun p => ?_⟩
  obtain ⟨t, ht, hrun⟩ := hc p [] emptyDeck
  have hconv := conv_run [] (q p).1 (q p).2.1 (q p).2.2
  have hall : Prog.Run [] (ofTaskProg c) (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
      (1 + (19 * ((q p).1.length + (q p).2.1.length + (q p).2.2.length) + 43) + 1 + t)
      (letters (pile 0 (send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))) emptyDeck)) :=
    Prog.Run.join hconv hrun
  have hlen := run_len_le hrun 0
  simp only [letters_here, letters_emptyDeck, List.append_nil, Tree.spell_length] at hlen
  have hsz : (send (q p)).count = 2 * ((q p).1.length + (q p).2.1.length + (q p).2.2.length) + 5 :=
    count_send_triple (q p).1 (q p).2.1 (q p).2.2
  have hsb : (send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))).count = 1 := rfl
  rw [hsz, hsb] at hlen
  refine ⟨_, ?_, _, hall, ?_⟩
  · have e : (20 * C + 45) * (β p + 1) = 20 * (C * (β p + 1)) + 45 * β p + 45 := by ring
    rw [e]
    generalize C * (β p + 1) = M at ht ⊢
    omega
  · rw [letters_here]
    rfl

open Classical in
theorem ofTask_proof {X : Type*} (q : X → List Bool × List Bool × List Bool) (β : X → ℕ)
    (Ck : List Bool → List Bool → ℕ → Prop)
    (h : Task β (fun p => send (q p))
      (fun p => send (decide (Ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))))) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ p : X,
      ProgAnswers Rc answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (decide (Ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))
        (c * ((q p).1.length + (q p).2.1.length + (q p).2.2.length + β p + 1)) := by
  obtain ⟨Rc, c, hR⟩ := ofTask_tight_proof q β (fun x u i => decide (Ck x u i)) h
  exact ⟨Rc, c, fun p => progAnswers_mono (hR p) (Nat.mul_le_mul_left c (by omega))⟩

theorem ofTask_fin_proof {ι : Type*} [Fintype ι] {X : Type*}
    (q : X → List Bool × List Bool × List Bool) (β : X → ℕ) (ck : ι → List Bool → List Bool → ℕ → Bool)
    (h : ∀ k, Task β (fun p => send (q p))
      (fun p => send (ck k (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)))) :
    ∃ (Rc : ι → Prog Ltr) (c : ℕ), ∀ k p,
      ProgAnswers (Rc k) answer (inputRegs Ltr.bit (q p).1 (q p).2.1 (q p).2.2)
        (ck k (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2)) (c * (β p + 1)) := by
  have hk := fun k => ofTask_tight_proof q β (ck k) (h k)
  choose Rc c hc using hk
  refine ⟨Rc, ∑ k, c k, fun k p => progAnswers_mono (hc k p) (Nat.mul_le_mul_right _ ?_)⟩
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end P1Dispatch
