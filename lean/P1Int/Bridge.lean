import P1Int.Guards
import P1Int.Interfaces
import OAI.Computability.DepthThree.Model

/-!
# P1Int.Bridge: from `ParDecidesFrom` (Challenge machines) to OpenAI's machines (owner: copy B)

For P11 (Lemma P) and the count lane: the parity count of `ParDecidesFrom` is the parity count of the
OpenAI machine `toOAI V` at ANY time bound `T' ≥ τ n + |withGuess w x|`, which is the form that lane net's
`P1Net.contract_eq_count_withGuess` / `sum_contract_eq_count` uses (`T' = n_int * B`).
`toOAI`, `cfgOAI`, `haltsWithin_iff` are copied verbatim from research/p1/lean/Case1/P1Case1/Bridge.lean
(lane case1, task W0b; namespace renamed), without its TRANS part.
-/

namespace P1Int

open OAI.DepthThreeLowerBound C1Challenge

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

theorem withGuess_ofFn_length (g : ℕ) (w : Fin g → Bool) (x : List Bool) :
    (withGuess (List.ofFn w) x).length = 2 * g + 1 + x.length := by
  rw [P1Int.length_withGuess, List.length_ofFn]

/-- When every guess halts within `T`, accepting within `T` is the same as accepting within any
`T' ≥ T` for `toOAI V`. -/
theorem accept_iff_oai (V : Machine) (input : List Bool) {T T' : ℕ} (hT : T ≤ T')
    (hhalt : ∃ b, HaltsWithin V input b T) :
    HaltsWithin V input true T ↔ MultiTapeHaltsIn (toOAI V) input true T' := by
  constructor
  · intro h
    exact (haltsWithin_iff V).mp (h.mono hT)
  · intro h
    obtain ⟨b, hb⟩ := hhalt
    have h' := (haltsWithin_iff V).mpr h
    have := halts_unique V hb h'
    rw [this] at hb
    exact hb

open Classical in
/-- **For P11 / the count lane.** The parity statement of `ParDecidesFrom`, moved to OpenAI's machine
model at any time bound `T'` at least the full bound `τ n + 2 g + 1 + n`. -/
theorem parDecides_oai {V : Machine} {L : List Bool → Bool} {g τ : ℕ → ℕ} {n₀ : ℕ}
    (h : ParDecidesFrom V L g τ n₀) (x : List Bool) (hx : n₀ ≤ x.length) (T' : ℕ)
    (hT' : τ x.length + (2 * g x.length + 1 + x.length) ≤ T') :
    L x = true ↔ Odd (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
      MultiTapeHaltsIn (toOAI V) (withGuess (List.ofFn w) x) true T').card := by
  obtain ⟨hhalt, hpar⟩ := h x hx
  rw [hpar]
  have hfilter : (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
      HaltsWithin V (withGuess (List.ofFn w) x) true (τ x.length + (withGuess (List.ofFn w) x).length)) =
      (Finset.univ.filter fun w : Fin (g x.length) → Bool =>
        MultiTapeHaltsIn (toOAI V) (withGuess (List.ofFn w) x) true T') := by
    apply Finset.filter_congr
    intro w _
    apply accept_iff_oai V _ _ (hhalt w)
    rw [withGuess_ofFn_length]
    exact hT'
  rw [hfilter]

end P1Int
