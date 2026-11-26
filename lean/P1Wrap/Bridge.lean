import C1Challenge.Statement
import OAI.Computability.DepthThree.Model

/-!
# OpenAI machines as Challenge machines (VERBATIM copy of P1Case1/CoTransBridge.lean of lane case1b, 09:27Z; namespace renamed)

`fromOAI M` copies the fields of OpenAI's `FiniteMultiTapeMachine` into a `C1Challenge.Machine`
(the two `HeadMove` types are copies of each other). Runs agree step by step, so
`HaltsWithin (fromOAI M) x b T ↔ MultiTapeHaltsIn M x b T`.

Also: runs of a `C1Challenge.Machine` are deterministic (`haltsWithin_unique`).
-/

namespace P1Wrap.Bridge

open OAI.DepthThreeLowerBound

/-- OpenAI's head moves as head moves of the Challenge file. -/
def moveC : OAI.DepthThreeLowerBound.HeadMove → C1Challenge.HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem moveC_apply {Γ : Type} [Inhabited Γ] (m : OAI.DepthThreeLowerBound.HeadMove)
    (t : Turing.Tape Γ) : (moveC m).apply t = m.apply t := by
  cases m <;> rfl

/-- An OpenAI machine as a Challenge machine. -/
def fromOAI (M : FiniteMultiTapeMachine) : C1Challenge.Machine where
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
  code := fun q r => (M.code q r).map fun out => (out.1, out.2.1, fun k => moveC (out.2.2 k))
  accept := M.accept

/-- Configurations of `fromOAI M` as configurations of `M`. -/
def cfgO (M : FiniteMultiTapeMachine) (c : C1Challenge.Cfg (fromOAI M).K (fromOAI M).Γ (fromOAI M).Q) :
    M.Cfg :=
  ⟨c.q, c.tapes⟩

theorem step_cfgO (M : FiniteMultiTapeMachine)
    (c : C1Challenge.Cfg (fromOAI M).K (fromOAI M).Γ (fromOAI M).Q) :
    M.step (cfgO M c) = ((fromOAI M).step c).map (cfgO M) := by
  simp only [FiniteMultiTapeMachine.step, multiTapeStep, C1Challenge.Machine.step, cfgO, fromOAI,
    Option.map_map]
  cases M.code c.q (fun k => (c.tapes k).head) with
  | none => rfl
  | some out =>
    simp only [Option.map_some, Function.comp_apply, multiTapeUpdate]
    show some _ = some (cfgO M _)
    simp only [cfgO]
    congr 2
    funext k
    exact (moveC_apply _ _).symm

theorem run_cfgO (M : FiniteMultiTapeMachine)
    (c : C1Challenge.Cfg (fromOAI M).K (fromOAI M).Γ (fromOAI M).Q) (t : ℕ) :
    runSteps M.step t (some (cfgO M c)) =
      ((fun oc => Option.bind oc (fromOAI M).step)^[t] (some c)).map (cfgO M) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold runSteps at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases (fun oc => Option.bind oc (fromOAI M).step)^[t] (some c) with
    | none => rfl
    | some d => simp only [Option.map_some, Option.bind_some, step_cfgO]

theorem init_cfgO (M : FiniteMultiTapeMachine) (x : List Bool) :
    M.init x = cfgO M ((fromOAI M).init x) := rfl

theorem cfgO_injective (M : FiniteMultiTapeMachine) : Function.Injective (cfgO M) := by
  rintro ⟨q, t⟩ ⟨q', t'⟩ h
  simp only [cfgO] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The two halting predicates agree. -/
theorem haltsWithin_fromOAI (M : FiniteMultiTapeMachine) {x : List Bool} {b : Bool} {T : ℕ} :
    C1Challenge.HaltsWithin (fromOAI M) x b T ↔ MultiTapeHaltsIn M x b T := by
  constructor
  · rintro ⟨t, ht, c, hrun, hstop, hacc⟩
    refine ⟨t, ht, cfgO M c, ?_, ?_, hacc⟩
    · rw [init_cfgO, run_cfgO, hrun]; rfl
    · rw [step_cfgO, hstop]; rfl
  · rintro ⟨t, ht, c', hrun, hstop, hacc⟩
    rw [init_cfgO, run_cfgO] at hrun
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hrun
    refine ⟨t, ht, c, hc, ?_, hacc⟩
    rw [step_cfgO] at hstop
    exact Option.map_eq_none_iff.mp hstop

/-! ## Determinism of Challenge machines -/

section Det

variable {V : C1Challenge.Machine}

/-- The run map of the Challenge file. -/
abbrev runMap (V : C1Challenge.Machine) :
    Option (C1Challenge.Cfg V.K V.Γ V.Q) → Option (C1Challenge.Cfg V.K V.Γ V.Q) :=
  fun oc => Option.bind oc V.step

theorem iterate_none (t : ℕ) : (runMap V)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Function.iterate_succ_apply', ih, runMap, Option.bind_none]

theorem iterate_after_halt {c : C1Challenge.Cfg V.K V.Γ V.Q} (hc : V.step c = none) (s : ℕ) :
    (runMap V)^[s + 1] (some c) = none := by
  rw [Function.iterate_succ_apply]
  simp only [runMap, Option.bind_some, hc]
  exact iterate_none s

theorem haltsWithin_unique {x : List Bool} {b b' : Bool} {T T' : ℕ}
    (h : C1Challenge.HaltsWithin V x b T) (h' : C1Challenge.HaltsWithin V x b' T') : b = b' := by
  obtain ⟨t, -, c, hrun, hstop, hacc⟩ := h
  obtain ⟨t', -, c', hrun', hstop', hacc'⟩ := h'
  change (runMap V)^[t] (some (V.init x)) = some c at hrun
  change (runMap V)^[t'] (some (V.init x)) = some c' at hrun'
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · obtain ⟨s, rfl⟩ : ∃ s, t' = (s + 1) + t := ⟨t' - t - 1, by omega⟩
    rw [Function.iterate_add_apply, hrun, iterate_after_halt hstop] at hrun'
    exact absurd hrun' (by simp)
  · subst heq
    rw [hrun] at hrun'
    obtain rfl := Option.some.inj hrun'
    rw [← hacc, ← hacc']
  · obtain ⟨s, rfl⟩ : ∃ s, t = (s + 1) + t' := ⟨t - t' - 1, by omega⟩
    rw [Function.iterate_add_apply, hrun', iterate_after_halt hstop'] at hrun
    exact absurd hrun (by simp)

theorem haltsWithin_mono {x : List Bool} {b : Bool} {T T' : ℕ}
    (h : C1Challenge.HaltsWithin V x b T) (hT : T ≤ T') : C1Challenge.HaltsWithin V x b T' := by
  obtain ⟨t, ht, rest⟩ := h
  exact ⟨t, ht.trans hT, rest⟩

end Det

end P1Wrap.Bridge
