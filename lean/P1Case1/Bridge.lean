import P1Case1.Flip
import OAI.Computability.DepthThree.Model

/-!
# P1, Case 1, task W0b: the Challenge machine model is OpenAI's `FiniteMultiTapeMachine`

`toOAI M` copies the fields of a `C1Challenge.Machine` into OpenAI's
`OAI.DepthThreeLowerBound.FiniteMultiTapeMachine` (the two `HeadMove` types are copies of each other).
Runs agree step by step, so `HaltsWithin M x b T ↔ MultiTapeHaltsIn (toOAI M) x b T`.

Consequence: the TRANS lower bound stated for OpenAI's machines (`TransLowerBoundOAI`, the text of
`research/g3/blind-noport/lean/TransDecision.lean`) gives the Challenge-model `TransLowerBound` used in
`P1Case1.Flip`.
-/

namespace P1Case1

open OAI.DepthThreeLowerBound

/-- The head moves of the Challenge file as OpenAI's head moves. -/
def moveOAI : C1Challenge.HeadMove → OAI.DepthThreeLowerBound.HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem moveOAI_apply {Γ : Type} [Inhabited Γ] (m : C1Challenge.HeadMove) (t : Turing.Tape Γ) :
    (moveOAI m).apply t = m.apply t := by
  cases m <;> rfl

/-- The Challenge machine as an OpenAI `FiniteMultiTapeMachine` (same tapes, alphabet, states, input
convention, transition table and answers). -/
def toOAI (M : C1Challenge.Machine) : FiniteMultiTapeMachine where
  K := M.K
  tapeFinite := M.tapeFinite
  tapeDecidableEq := M.tapeDecidableEq
  inputTape := M.inputTape
  Γ := M.Γ
  alphabetInhabited := M.alphabetInhabited
  alphabetFinite := M.alphabetFinite
  Q := M.Q
  stateFinite := M.stateFinite
  initialState := M.initialState
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q r => (M.code q r).map fun out => (out.1, out.2.1, fun k => moveOAI (out.2.2 k))
  accept := M.accept

/-- Configurations of the Challenge machine as configurations of `toOAI M`. -/
def cfgOAI (M : C1Challenge.Machine) (c : C1Challenge.Cfg M.K M.Γ M.Q) : (toOAI M).Cfg :=
  ⟨c.q, c.tapes⟩

theorem cfgOAI_injective (M : C1Challenge.Machine) : Function.Injective (cfgOAI M) := by
  rintro ⟨q, t⟩ ⟨q', t'⟩ h
  simp only [cfgOAI] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem step_cfgOAI (M : C1Challenge.Machine) (c : C1Challenge.Cfg M.K M.Γ M.Q) :
    (toOAI M).step (cfgOAI M c) = (M.step c).map (cfgOAI M) := by
  simp only [FiniteMultiTapeMachine.step, multiTapeStep, C1Challenge.Machine.step, cfgOAI, toOAI,
    Option.map_map]
  cases M.code c.q (fun k => (c.tapes k).head) with
  | none => rfl
  | some out =>
    simp only [Option.map_some, Function.comp_apply, multiTapeUpdate]
    show some _ = some (cfgOAI M _)
    simp only [cfgOAI]
    congr 2
    funext k
    exact moveOAI_apply _ _

theorem run_cfgOAI (M : C1Challenge.Machine) (c : C1Challenge.Cfg M.K M.Γ M.Q) (t : ℕ) :
    runSteps (toOAI M).step t (some (cfgOAI M c)) =
      ((fun oc => Option.bind oc M.step)^[t] (some c)).map (cfgOAI M) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold runSteps at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases (fun oc => Option.bind oc M.step)^[t] (some c) with
    | none => rfl
    | some d => simp only [Option.map_some, Option.bind_some, step_cfgOAI]

theorem init_cfgOAI (M : C1Challenge.Machine) (x : List Bool) :
    (toOAI M).init x = cfgOAI M (M.init x) := rfl

/-- **W0b.** The two halting predicates agree. -/
theorem haltsWithin_iff (M : C1Challenge.Machine) {x : List Bool} {b : Bool} {T : ℕ} :
    C1Challenge.HaltsWithin M x b T ↔ MultiTapeHaltsIn (toOAI M) x b T := by
  constructor
  · rintro ⟨t, ht, c, hrun, hstop, hacc⟩
    refine ⟨t, ht, cfgOAI M c, ?_, ?_, hacc⟩
    · rw [init_cfgOAI, run_cfgOAI, hrun]; rfl
    · rw [step_cfgOAI, hstop]; rfl
  · rintro ⟨t, ht, c', hrun, hstop, hacc⟩
    rw [init_cfgOAI, run_cfgOAI] at hrun
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hrun
    refine ⟨t, ht, c, hc, ?_, hacc⟩
    rw [step_cfgOAI] at hstop
    exact Option.map_eq_none_iff.mp hstop

/-- `M` decides TRANS at side `N` within `T` steps (OpenAI's machines; text of `TransDecision.lean`). -/
def DecidesTransInOAI (M : FiniteMultiTapeMachine) (N T : ℕ) : Prop :=
  ∀ X Y : Fin N → Fin N → Bool, MultiTapeHaltsIn M (transEncode X Y) (transAnswer X Y) T

/-- The TRANS decision lower bound for OpenAI's machines (text of `TransDecision.lean`). -/
def TransLowerBoundOAI : Prop := ∀ M : FiniteMultiTapeMachine, ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
  ∀ N ≥ N₀, ∀ T : ℕ, DecidesTransInOAI M N T → c * scale (2 * N * N) ≤ T

theorem decidesTransIn_iff (M : C1Challenge.Machine) (N T : ℕ) :
    DecidesTransIn M N T ↔ DecidesTransInOAI (toOAI M) N T :=
  forall_congr' fun _ => forall_congr' fun _ => haltsWithin_iff M

/-- **W0b, consequence.** The OpenAI-model TRANS lower bound gives the Challenge-model one. -/
theorem transLowerBound_of_oai (h : TransLowerBoundOAI) : TransLowerBound := by
  intro M
  obtain ⟨c, hc, N₀, hlow⟩ := h (toOAI M)
  exact ⟨c, hc, N₀, fun N hN T hdec => hlow N hN T ((decidesTransIn_iff M N T).mp hdec)⟩

end P1Case1
