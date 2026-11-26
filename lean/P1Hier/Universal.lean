import OAI.Computability.MultitapeWeakETH.EncodedDecision
import OAI.Computability.IntegerMultiplication.Code.Repeat
import OAI.Computability.IntegerMultiplication.Code.Automata
import P1Hier.Spec

/-!
# P1Hier.Universal: W1 in OpenAI's Task framework, and the machine-level compiler

* `compile_task` (PROVED): a `Task` on raw bit words compiles to an OpenAI multitape machine with
  time LINEAR in input length + budget (the explicit form of `compile_word_decision`).
* `ofOAI`, `haltsWithin_ofOAI` (PROVED): OpenAI's `FiniteMultiTapeMachine` as a Challenge `Machine`.
* `checkBudget`: the budget `(size c + 1)² (|y| + T + 1) + size τ` of the W1 task; the task itself
  and W1 (`universal_checker`) are in `CheckAssembly.lean`.
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound

/-! ## Codecs -/

/-- Natural numbers in unary (a tally list). -/
instance instCodecNat : Codec ℕ := ⟨fun n => send (List.replicate n ())⟩

instance instCodecMCode : Codec MCode :=
  ⟨fun c => send (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)⟩

/-! ## W1 -/

/-- Budget of the universal check. -/
def checkBudget (i : MCode × List Bool × ℕ × List Entry) : ℕ :=
  (size i.1 + 1) ^ 2 * (i.2.1.length + i.2.2.1 + 1) + size i.2.2.2

/-! ## Compiling a task on raw words to a machine, with linear time -/

open private raw codeY inList_cost Ybase frame from OAI.Computability.IntegerMultiplication.Interface

private def observation : Option Ltr → Bool
  | some (.bit b) => b
  | _ => false

theorem multiTapeHaltsIn_mono {M : FiniteMultiTapeMachine} {x : List Bool} {b : Bool} {t t' : ℕ}
    (h : MultiTapeHaltsIn M x b t) (ht : t ≤ t') : MultiTapeHaltsIn M x b t' := by
  obtain ⟨k, hk, c, h1, h2, h3⟩ := h
  exact ⟨k, hk.trans ht, c, h1, h2, h3⟩

/-- A charged decision task on raw words becomes a machine whose time is linear in
input length plus budget. -/
theorem compile_task {I : Type} (budget : I → ℕ) (input : I → List Bool) (answer : I → Bool)
    (program : Task budget (fun i => send (input i)) (fun i => send (answer i))) :
    ∃ (M : FiniteMultiTapeMachine) (K : ℕ), ∀ i,
      MultiTapeHaltsIn M (input i) (answer i) (K * ((input i).length + budget i + 1)) := by
  classical
  obtain ⟨c, C, checked⟩ := program
  let p := Prog.join (.tie codeY) c
  obtain ⟨M, compile⟩ := OAI.Computability.MultitapeWeakETH.DecisionTapes.compile_program p Ltr.bit
    (fun _ _ => Ltr.bit.inj) observation
  refine ⟨M, 2 * C + 40, fun i => ?_⟩
  have result (i : I) :
      ∃ t ≤ 2*(11*(input i).length+C*(budget i+1)+8)+1, MultiTapeHaltsIn M (input i) (answer i) t := by
    obtain ⟨j,hj,exec⟩ := checked i [] (fun _ => [])
    simp only [frame] at exec
    have sub := inList_cost _ _ [] [] 5 [] (Ybase []) (input i)
    simp only [List.append_nil] at sub
    have load := Prog.Run.tie sub
    have joined := Prog.Run.join load exec
    have done := compile (input i) _ _ joined
    refine ⟨_,?_,by simpa [raw,Interface.letters_word,Tree.spell,observation] using done⟩
    omega
  obtain ⟨t, ht, h⟩ := result i
  refine multiTapeHaltsIn_mono h (le_trans ht ?_)
  nlinarith

/-! ## OpenAI machines as Challenge machines -/

def moveOf : HeadMove → C1Challenge.HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

/-- An OpenAI multitape machine, field for field, as a Challenge machine. -/
@[reducible] def ofOAI (M : FiniteMultiTapeMachine) : C1Challenge.Machine where
  K := M.K
  inputTape := M.inputTape
  Γ := M.Γ
  Q := M.Q
  initialState := M.initialState
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q r => (M.code q r).map fun out => (out.1, out.2.1, fun k => moveOf (out.2.2 k))
  accept := M.accept

def cfgOf (M : FiniteMultiTapeMachine) (c : M.Cfg) :
    C1Challenge.Cfg (ofOAI M).K (ofOAI M).Γ (ofOAI M).Q := ⟨c.q, c.tapes⟩

theorem moveOf_apply {Γ : Type} [Inhabited Γ] (m : HeadMove) (t : Turing.Tape Γ) :
    (moveOf m).apply t = m.apply t := by
  cases m <;> rfl

theorem step_ofOAI (M : FiniteMultiTapeMachine) (c : M.Cfg) :
    (ofOAI M).step (cfgOf M c) = (M.step c).map (cfgOf M) := by
  simp only [C1Challenge.Machine.step, FiniteMultiTapeMachine.step, multiTapeStep, ofOAI, cfgOf,
    Option.map_map]
  cases M.code c.q (fun k => (c.tapes k).head) with
  | none => rfl
  | some out =>
    simp only [Option.map_some, Function.comp, multiTapeUpdate]
    congr 2
    funext k
    exact moveOf_apply _ _

theorem bind_ofOAI (M : FiniteMultiTapeMachine) (c : Option M.Cfg) :
    Option.bind (c.map (cfgOf M)) (ofOAI M).step = (c.bind M.step).map (cfgOf M) := by
  cases c with
  | none => rfl
  | some c => exact step_ofOAI M c

theorem iterate_ofOAI (M : FiniteMultiTapeMachine) (k : ℕ) (c : Option M.Cfg) :
    (fun oc => Option.bind oc (ofOAI M).step)^[k] (c.map (cfgOf M)) =
      (runSteps M.step k c).map (cfgOf M) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, bind_ofOAI, ih]
    simp only [runSteps, Function.iterate_succ_apply]

theorem haltsWithin_ofOAI (M : FiniteMultiTapeMachine) (x : List Bool) (b : Bool) (T : ℕ)
    (h : MultiTapeHaltsIn M x b T) : C1Challenge.HaltsWithin (ofOAI M) x b T := by
  obtain ⟨k, hk, c, hrun, hstep, hacc⟩ := h
  refine ⟨k, hk, cfgOf M c, ?_, ?_, hacc⟩
  · have := iterate_ofOAI M k (some (M.init x))
    rw [hrun] at this
    exact this
  · rw [step_ofOAI, hstep]; rfl

end P1Hier
