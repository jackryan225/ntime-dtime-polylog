import P1Wrap.OuterSpec
import OAI.Computability.IntegerMultiplication.Interface

/-!
# From an OpenAI `Task` on the raw verifier input to a stack program (shared by pieces B and C of W3)

* `task_prog`: a `Task` whose query is the tree of a raw bit word gives one stack program over `Ltr` that runs
  from the raw word in register 0 (letters `Ltr.bit`) to the spelled answer tree in register 0, at cost
  `C (|input| + budget + 1)` (OpenAI's private `codeY` loader, as in `P1Hier.compile_task`).
* `OuterTask j a b`: the Task form of `OuterImpl` (budget `|w| + ν`, query the tree of `withGuess w x`).
* `outerImpl_of_task : OuterTask j a b → OuterImpl j a b`. So piece C is a pure Task-level statement.
-/

namespace P1Wrap.W3

open P1Int C1Challenge
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open private raw codeY inList_cost Ybase frame from OAI.Computability.IntegerMultiplication.Interface

/-- A task on raw words as one stack program over `Ltr`. -/
theorem task_prog {I : Type} (budget : I → ℕ) (input : I → List Bool) (out : I → Tree)
    (h : Task budget (fun i => send (input i)) out) :
    ∃ (p : Cmd) (C : ℕ), ∀ i, ∃ t, Prog.Run [] p (initRegs Ltr.bit (input i)) t
      (fun k => if k = 0 then (out i).spell else []) ∧ t ≤ C * ((input i).length + budget i + 1) := by
  obtain ⟨c, C, checked⟩ := h
  refine ⟨Prog.join (.tie codeY) c, C + 20, fun i => ?_⟩
  obtain ⟨j, hj, exec⟩ := checked i [] (fun _ => [])
  simp only [frame] at exec
  have sub := inList_cost _ _ [] [] 5 [] (Ybase []) (input i)
  simp only [List.append_nil] at sub
  have load := Prog.Run.tie sub
  have joined := Prog.Run.join load exec
  refine ⟨_, joined, ?_⟩
  have e1 : C * (budget i + 1) ≤ C * ((input i).length + budget i + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : (C + 20) * ((input i).length + budget i + 1) =
      C * ((input i).length + budget i + 1) + 20 * ((input i).length + budget i + 1) := by ring
  omega

/-- Reading the Boolean answer of a spelled `Bool` tree. -/
def obsBit : Option Ltr → Bool
  | some (.bit b) => b
  | _ => false

theorem obsBit_spell (v : Bool) :
    obsBit ((fun k : ℕ => if k = 0 then (send v).spell else ([] : List Ltr)) 0).head? = v := by
  simp [obsBit, send, Tree.spell]

/-- **Piece C, Task form**: for every machine `M`, a task computes `outerVerdict` from the tree of the raw input
`withGuess w x`, with budget `|w| + ν(|x|)`. -/
def OuterTask (j a b : ℕ) : Prop :=
  ∀ M : Machine, Task (fun i : List Bool × List Bool => i.1.length + nuOf j a b i.2.length)
    (fun i => send (withGuess i.1 i.2)) (fun i => send (outerVerdict M j a b i.1 i.2))

theorem outerImpl_of_task {j a b : ℕ} (h : OuterTask j a b) : OuterImpl j a b := by
  intro M
  obtain ⟨p, C, hp⟩ := task_prog _ (fun i : List Bool × List Bool => withGuess i.1 i.2) _ (h M)
  refine ⟨Ltr, inferInstance, p, Ltr.bit, fun _ _ e => Ltr.bit.inj e, obsBit, 3 * C, fun x w => ?_⟩
  obtain ⟨t, hrun, ht⟩ := hp (w, x)
  refine ⟨t, _, hrun, ?_, obsBit_spell _⟩
  have hl : (withGuess w x).length = 2 * w.length + 1 + x.length := length_withGuess' w x
  have hx : x.length ≤ nuOf j a b x.length := by unfold nuOf; omega
  have e1 : C * ((withGuess w x).length + (w.length + nuOf j a b x.length) + 1) ≤
      C * (3 * (w.length + nuOf j a b x.length + 1)) := Nat.mul_le_mul_left _ (by omega)
  have e2 : C * (3 * (w.length + nuOf j a b x.length + 1)) =
      3 * C * (w.length + nuOf j a b x.length + 1) := by ring
  simp only at ht
  omega

end P1Wrap.W3
