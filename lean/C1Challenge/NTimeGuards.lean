import C1Challenge.NTime
import C1Challenge.NonVacuity
import Mathlib.Data.Set.Countable

/-!
# Guards for `NTIMEIn` (NTime.lean), before any proof builds on it (P1-lean-integ, 2026-11-25)

* `ntime_of_dtime`: `DTIMEIn L f → NTIMEIn L f` (a deterministic machine is a nondeterministic one); in particular
  DTIME(n) ⊆ NTIME(n) (`dtime_lin_sub_ntime_lin`).
* `ntime_firstBit`: a language that depends on its input is in NTIME(n).
* `ntime_const`: constant languages, with `T = 0` (small case: no step at all).
* `loop_not_witness`: a machine that never halts is never a witness (the clause "every computation halts" has teeth).
* `exists_not_ntime`: COUNTING. For every `f` the class `{L | NTIMEIn L f}` is countable (every machine has the language
  of a machine on `Fin a`, `Fin b`, `Fin c`, and those are countable), and the languages are not; so some language is not
  in NTIME(n).
-/

namespace C1Challenge
namespace NTimeGuards

/-- Configurations with equal state and tapes are equal. -/
theorem cfg_ext {K Γ Q : Type} [Inhabited Γ] {c d : Cfg K Γ Q} (hq : c.q = d.q)
    (ht : c.tapes = d.tapes) : c = d := by
  cases c; cases d; cases hq; cases ht; rfl

/-! ## G1: a deterministic machine as a nondeterministic one -/

/-- `M` with its (at most one) transition as a list. -/
def toN (M : Machine) : NMachine where
  K := M.K
  inputTape := M.inputTape
  Γ := M.Γ
  Q := M.Q
  initialState := M.initialState
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q s => (M.code q s).toList
  accept := M.accept

theorem next_toN (M : Machine) (c c' : Cfg M.K M.Γ M.Q) :
    (toN M).Next c c' ↔ M.step c = some c' := by
  unfold NMachine.Next Machine.step
  show (∃ out ∈ (M.code c.q (fun k => (c.tapes k).head)).toList, (toN M).apply c out = c') ↔ _
  cases M.code c.q (fun k => (c.tapes k).head) with
  | none => simp
  | some out =>
    simp
    try exact Iff.rfl

theorem halted_toN (M : Machine) (c : Cfg M.K M.Γ M.Q) : (toN M).Halted c ↔ M.step c = none := by
  unfold NMachine.Halted Machine.step
  show (M.code c.q (fun k => (c.tapes k).head)).toList = [] ↔ _
  cases M.code c.q (fun k => (c.tapes k).head) <;> simp

theorem reach_toN (M : Machine) (t : ℕ) : ∀ c c' : Cfg M.K M.Γ M.Q,
    (toN M).Reach c t c' ↔ (fun oc => Option.bind oc M.step)^[t] (some c) = some c' := by
  induction t with
  | zero =>
    intro c c'
    show c' = c ↔ some c = some c'
    rw [Option.some.injEq]
    exact eq_comm
  | succ t ih =>
    intro c c'
    show (∃ c₁, (toN M).Next c c₁ ∧ (toN M).Reach c₁ t c') ↔
      (fun oc => Option.bind oc M.step)^[t] (M.step c) = some c'
    constructor
    · rintro ⟨c₁, h1, h2⟩
      rw [(next_toN M c c₁).1 h1]
      exact (ih c₁ c').1 h2
    · intro h
      cases hs : M.step c with
      | none =>
        rw [hs, iterate_bind_none] at h
        cases h
      | some c₁ =>
        rw [hs] at h
        exact ⟨c₁, (next_toN M c c₁).2 hs, (ih c₁ c').2 h⟩

/-- **G1.** DTIME(f) ⊆ NTIME(f), with the same machine, constant and clock. -/
theorem ntime_of_dtime {L : List Bool → Bool} {f : ℕ → ℝ} (h : DTIMEIn L f) : NTIMEIn L f := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨toN M, C, fun x => ?_⟩
  obtain ⟨T, hT, t, htT, c, hc, hstop, hacc⟩ := hM x
  refine ⟨T, hT, fun c' hr => ?_, ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · have hr' := (reach_toN M (T + 1) (M.init x) c').1 hr
    obtain ⟨k, hk⟩ : ∃ k, T + 1 = t + 1 + k := ⟨T - t, by omega⟩
    rw [hk, run_after_halt M hc hstop k] at hr'
    cases hr'
  · exact ⟨t, c, (reach_toN M t (M.init x) c).2 hc, (halted_toN M c).2 hstop, hacc.trans hL⟩
  · obtain ⟨t', c', hr, hh, ha⟩ := hex
    exact halts_unique M ⟨t, le_rfl, c, hc, hstop, hacc⟩
      ⟨t', le_rfl, c', (reach_toN M t' (M.init x) c').1 hr, (halted_toN M c').1 hh, ha⟩

/-- DTIME(n) ⊆ NTIME(n). -/
theorem dtime_lin_sub_ntime_lin {L : List Bool → Bool} (h : DTIMEIn L (fun n => (n : ℝ))) :
    NTIMEIn L (fun n => (n : ℝ)) :=
  ntime_of_dtime h

/-! ## G2: a language that depends on its input is in NTIME(n) -/

theorem ntime_firstBit : NTIMEIn firstBit (fun n => (n : ℝ)) :=
  ntime_of_dtime (dtime_firstBit _ (fun n => Nat.cast_nonneg n))

example : firstBit [true] ≠ firstBit [] := firstBit_nonconstant

/-! ## G4: small cases -/

/-- One tape, no transition at all: halts at once (time `0`) and answers `b`. -/
def haltMachine (b : Bool) : NMachine where
  K := Unit
  inputTape := ()
  Γ := Option Bool
  Q := Unit
  initialState := ()
  inputSymbol := some
  input_injective := Option.some_injective Bool
  input_ne_blank := fun b => Option.some_ne_none b
  code := fun _ _ => []
  accept := fun _ => b

theorem ntime_const (b : Bool) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) : NTIMEIn (fun _ => b) f := by
  refine ⟨haltMachine b, 1, fun x => ⟨0, ?_, ?_, ?_⟩⟩
  · have := hf x.length
    push_cast
    linarith
  · rintro c ⟨c₁, ⟨out, hout, -⟩, -⟩
    cases hout
  · constructor
    · intro hb
      exact ⟨0, (haltMachine b).init x, rfl, rfl, hb⟩
    · rintro ⟨t, c, -, -, hc⟩
      exact hc

/-- One tape, one transition that writes the scanned symbol and stays: it never halts. -/
def loopMachine : NMachine where
  K := Unit
  inputTape := ()
  Γ := Option Bool
  Q := Unit
  initialState := ()
  inputSymbol := some
  input_injective := Option.some_injective Bool
  input_ne_blank := fun b => Option.some_ne_none b
  code := fun q s => [(q, s, fun _ => HeadMove.stay)]
  accept := fun _ => true

theorem loop_reach (c : Cfg loopMachine.K loopMachine.Γ loopMachine.Q) (t : ℕ) :
    loopMachine.Reach c t c := by
  induction t with
  | zero => exact rfl
  | succ t ih =>
    show ∃ c₁, loopMachine.Next c c₁ ∧ loopMachine.Reach c₁ t c
    refine ⟨c, ?_, ih⟩
    show ∃ out ∈ loopMachine.code c.q (loopMachine.scanned c), loopMachine.apply c out = c
    refine ⟨(c.q, loopMachine.scanned c, fun _ => HeadMove.stay), List.mem_singleton_self _, ?_⟩
    apply cfg_ext
    · rfl
    · funext k
      show HeadMove.stay.apply ((c.tapes k).write (c.tapes k).head) = c.tapes k
      exact Turing.Tape.write_self _

/-- The time clause has teeth: for no input and no `T` does the looping machine satisfy it. -/
theorem loop_not_witness (x : List Bool) (T : ℕ) :
    ¬ ∀ c, ¬ loopMachine.Reach (loopMachine.init x) (T + 1) c :=
  fun h => h _ (loop_reach _ _)

/-! ## G5: genuine branching (asked by the blind Gemini read, 17:01Z)

`forkMachine` branches at its first step into two different ACCEPTING halted configurations and one REJECTING one. It
witnesses `fun _ => true ∈ NTIME(n)`. Under "every computation accepts" (coNTIME), "exactly one accepts" (UTIME) or
"an odd number accepts" (parity) the same machine would not accept, so `NTIMEIn` uses "some computation accepts". -/

def forkMachine : NMachine where
  K := Unit
  inputTape := ()
  Γ := Option Bool
  Q := Option (Option Bool)
  initialState := none
  inputSymbol := some
  input_injective := Option.some_injective Bool
  input_ne_blank := fun b => Option.some_ne_none b
  code := fun q s => match q with
    | none => [(some (some true), s, fun _ => HeadMove.stay), (some (some false), s, fun _ => HeadMove.stay),
        (some none, s, fun _ => HeadMove.stay)]
    | some _ => []
  accept := fun q => match q with
    | some (some _) => true
    | _ => false

/-- The configuration after the branch `q'` at the first step. -/
def forkAfter (x : List Bool) (q' : Option (Option Bool)) : Cfg forkMachine.K forkMachine.Γ forkMachine.Q :=
  forkMachine.apply (forkMachine.init x) (q', forkMachine.scanned (forkMachine.init x), fun _ => HeadMove.stay)

theorem fork_code_none (s : forkMachine.K → forkMachine.Γ) :
    forkMachine.code none s = [(some (some true), s, fun _ => HeadMove.stay),
      (some (some false), s, fun _ => HeadMove.stay), (some none, s, fun _ => HeadMove.stay)] := rfl

theorem fork_step (x : List Bool) (q' : Option (Option Bool)) (hq : q' ≠ none) :
    forkMachine.Reach (forkMachine.init x) 1 (forkAfter x q') := by
  show ∃ c₁, forkMachine.Next (forkMachine.init x) c₁ ∧ forkMachine.Reach c₁ 0 (forkAfter x q')
  refine ⟨forkAfter x q', ?_, rfl⟩
  show ∃ out ∈ forkMachine.code none (forkMachine.scanned (forkMachine.init x)),
    forkMachine.apply (forkMachine.init x) out = forkAfter x q'
  refine ⟨(q', forkMachine.scanned (forkMachine.init x), fun _ => HeadMove.stay), ?_, rfl⟩
  rw [fork_code_none]
  rcases q' with _ | _ | b
  · exact absurd rfl hq
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · cases b
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.head _

theorem fork_no_second (x : List Bool) (c : Cfg forkMachine.K forkMachine.Γ forkMachine.Q) :
    ¬ forkMachine.Reach (forkMachine.init x) (1 + 1) c := by
  rintro ⟨c₁, ⟨out, hout, rfl⟩, c₂, ⟨out', hout', -⟩, -⟩
  rw [show (forkMachine.init x).q = none from rfl, fork_code_none] at hout
  rcases List.mem_cons.1 hout with rfl | h1
  · cases hout'
  rcases List.mem_cons.1 h1 with rfl | h2
  · cases hout'
  rcases List.mem_cons.1 h2 with rfl | h3
  · cases hout'
  cases h3

/-- On every input: a rejecting halted computation. -/
theorem fork_reject (x : List Bool) : ∃ t c, forkMachine.Reach (forkMachine.init x) t c ∧
    forkMachine.Halted c ∧ forkMachine.accept c.q = false :=
  ⟨1, forkAfter x (some none), fork_step x _ (Option.some_ne_none _), rfl, rfl⟩

/-- On every input: two DIFFERENT accepting halted computations. -/
theorem fork_two_accept (x : List Bool) : ∃ c c', c ≠ c' ∧
    forkMachine.Reach (forkMachine.init x) 1 c ∧ forkMachine.Halted c ∧ forkMachine.accept c.q = true ∧
    forkMachine.Reach (forkMachine.init x) 1 c' ∧ forkMachine.Halted c' ∧ forkMachine.accept c'.q = true := by
  refine ⟨forkAfter x (some (some true)), forkAfter x (some (some false)), ?_,
    fork_step x _ (Option.some_ne_none _), rfl, rfl, fork_step x _ (Option.some_ne_none _), rfl, rfl⟩
  intro h
  have h2 : (some (some true) : Option (Option Bool)) = some (some false) := congrArg Cfg.q h
  cases h2

/-- The branching machine witnesses `fun _ => true ∈ NTIME(n)` (time `1`). -/
theorem ntime_fork : NTIMEIn (fun _ => true) (fun n => (n : ℝ)) := by
  refine ⟨forkMachine, 1, fun x => ⟨1, ?_, fun c => fork_no_second x c, ?_⟩⟩
  · show ((1 : ℕ) : ℝ) ≤ 1 * ((x.length : ℝ) + 1)
    have := (Nat.cast_nonneg x.length : (0 : ℝ) ≤ x.length)
    push_cast
    linarith
  · exact ⟨fun _ => ⟨1, forkAfter x (some (some true)), fork_step x _ (Option.some_ne_none _), rfl, rfl⟩,
      fun _ => rfl⟩

/-! ## G6: EVERY computation must halt (asked by the blind Gemini read, 17:01Z)

`forkLoopMachine` has an accepting computation of one step AND a computation that never halts. It is never a witness:
"some computation halts within `T`" would not be enough. -/

def forkLoopMachine : NMachine where
  K := Unit
  inputTape := ()
  Γ := Option Bool
  Q := Option Bool
  initialState := none
  inputSymbol := some
  input_injective := Option.some_injective Bool
  input_ne_blank := fun b => Option.some_ne_none b
  code := fun q s => match q with
    | none => [(some true, s, fun _ => HeadMove.stay), (some false, s, fun _ => HeadMove.stay)]
    | some true => []
    | some false => [(some false, s, fun _ => HeadMove.stay)]
  accept := fun q => match q with
    | some true => true
    | _ => false

theorem forkLoop_stay (c : Cfg forkLoopMachine.K forkLoopMachine.Γ forkLoopMachine.Q) (hc : c.q = some false)
    (t : ℕ) : forkLoopMachine.Reach c t c := by
  induction t with
  | zero => exact rfl
  | succ t ih =>
    show ∃ c₁, forkLoopMachine.Next c c₁ ∧ forkLoopMachine.Reach c₁ t c
    refine ⟨c, ?_, ih⟩
    show ∃ out ∈ forkLoopMachine.code c.q (forkLoopMachine.scanned c), forkLoopMachine.apply c out = c
    refine ⟨(some false, forkLoopMachine.scanned c, fun _ => HeadMove.stay), ?_, ?_⟩
    · rw [hc]
      exact List.Mem.head _
    · apply cfg_ext
      · exact hc.symm
      · funext k
        show HeadMove.stay.apply ((c.tapes k).write (c.tapes k).head) = c.tapes k
        exact Turing.Tape.write_self _

/-- A fast accepting computation exists ... -/
theorem forkLoop_fast_accept (x : List Bool) :
    ∃ c, forkLoopMachine.Reach (forkLoopMachine.init x) 1 c ∧ forkLoopMachine.Halted c ∧
      forkLoopMachine.accept c.q = true := by
  let c₁ := forkLoopMachine.apply (forkLoopMachine.init x)
    (some true, forkLoopMachine.scanned (forkLoopMachine.init x), fun _ => HeadMove.stay)
  refine ⟨c₁, ?_, rfl, rfl⟩
  show ∃ c₂, forkLoopMachine.Next (forkLoopMachine.init x) c₂ ∧ forkLoopMachine.Reach c₂ 0 c₁
  refine ⟨c₁, ?_, rfl⟩
  show ∃ out ∈ forkLoopMachine.code none (forkLoopMachine.scanned (forkLoopMachine.init x)),
    forkLoopMachine.apply (forkLoopMachine.init x) out = c₁
  exact ⟨_, List.Mem.head _, rfl⟩

/-- ... but for no input and no `T` does the machine satisfy the time clause. -/
theorem forkLoop_not_witness (x : List Bool) (T : ℕ) :
    ¬ ∀ c, ¬ forkLoopMachine.Reach (forkLoopMachine.init x) (T + 1) c := by
  intro h
  let c₁ := forkLoopMachine.apply (forkLoopMachine.init x)
    (some false, forkLoopMachine.scanned (forkLoopMachine.init x), fun _ => HeadMove.stay)
  apply h c₁
  show ∃ c₂, forkLoopMachine.Next (forkLoopMachine.init x) c₂ ∧ forkLoopMachine.Reach c₂ T c₁
  refine ⟨c₁, ?_, forkLoop_stay c₁ rfl T⟩
  show ∃ out ∈ forkLoopMachine.code none (forkLoopMachine.scanned (forkLoopMachine.init x)),
    forkLoopMachine.apply (forkLoopMachine.init x) out = c₁
  exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl⟩

/-! ## G3: counting -/

instance : Finite HeadMove :=
  Finite.of_injective (fun m : HeadMove => match m with
    | .left => (0 : Fin 3) | .stay => 1 | .right => 2)
    (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- Functions from a finite type to a countable type form a countable type. -/
instance (priority := low) countableFun {α β : Type} [Finite α] [Countable β] : Countable (α → β) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat β
  have hinj : Function.Injective (fun h : α → β => List.ofFn (fun i : Fin n => g (h (e.symm i)))) := by
    intro h₁ h₂ hh
    funext a
    have h3 := congrFun (List.ofFn_injective hh) (e a)
    simpa using hg h3
  exact hinj.countable

open Classical in
/-- The language of a nondeterministic machine. -/
noncomputable def lang (M : NMachine) (x : List Bool) : Bool :=
  decide (∃ t c, M.Reach (M.init x) t c ∧ M.Halted c ∧ M.accept c.q = true)

theorem eq_lang {L : List Bool → Bool} {f : ℕ → ℝ} (h : NTIMEIn L f) : ∃ M, L = lang M := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨M, funext fun x => ?_⟩
  obtain ⟨T, -, -, hiff⟩ := hM x
  refine Bool.eq_iff_iff.2 (hiff.trans ?_)
  simp only [lang, decide_eq_true_iff]

/-- A machine on `Fin a`, `Fin b`, `Fin c` as data: input tape, blank, initial state, input symbols, code, accept. -/
abbrev Data (a b c : ℕ) : Type :=
  Fin a × Fin b × Fin c × (Bool → Fin b) ×
    (Fin c → (Fin a → Fin b) → List (Fin c × (Fin a → Fin b) × (Fin a → HeadMove))) × (Fin c → Bool)

abbrev Code : Type := Σ p : ℕ × ℕ × ℕ, Data p.1 p.2.1 p.2.2

instance : Countable Code := inferInstance

/-- The machine of some data. -/
def ofData {a b c : ℕ} (d : Data a b c) (h1 : Function.Injective d.2.2.2.1)
    (h2 : ∀ x, d.2.2.2.1 x ≠ d.2.1) : NMachine where
  K := Fin a
  inputTape := d.1
  Γ := Fin b
  alphabetInhabited := ⟨d.2.1⟩
  Q := Fin c
  initialState := d.2.2.1
  inputSymbol := d.2.2.2.1
  input_injective := h1
  input_ne_blank := h2
  code := d.2.2.2.2.1
  accept := d.2.2.2.2.2

open Classical in
/-- The language of a code (constant `false` for codes that are not machines). -/
noncomputable def codeLang (k : Code) : List Bool → Bool :=
  if h : Function.Injective k.2.2.2.2.1 ∧ ∀ x, k.2.2.2.2.1 x ≠ k.2.2.1 then lang (ofData k.2 h.1 h.2)
  else fun _ => false

section Transport

variable (M : NMachine) {a b c : ℕ} (eK : M.K ≃ Fin a) (eΓ : M.Γ ≃ Fin b) (eQ : M.Q ≃ Fin c)

/-- The transported transition. -/
def tOut (out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)) : Fin c × (Fin a → Fin b) × (Fin a → HeadMove) :=
  (eQ out.1, eΓ ∘ out.2.1 ∘ eK.symm, out.2.2 ∘ eK.symm)

/-- The transported data. -/
def tData : Data a b c :=
  (eK M.inputTape, eΓ default, eQ M.initialState, eΓ ∘ M.inputSymbol,
   fun q s => (M.code (eQ.symm q) (eΓ.symm ∘ s ∘ eK)).map (tOut M eK eΓ eQ),
   M.accept ∘ eQ.symm)

theorem tData_inj : Function.Injective (tData M eK eΓ eQ).2.2.2.1 :=
  eΓ.injective.comp M.input_injective

theorem tData_ne (x : Bool) : (tData M eK eΓ eQ).2.2.2.1 x ≠ (tData M eK eΓ eQ).2.1 :=
  fun h => M.input_ne_blank x (eΓ.injective h)

/-- The transported machine. -/
def tM : NMachine := ofData (tData M eK eΓ eQ) (tData_inj M eK eΓ eQ) (tData_ne M eK eΓ eQ)

/-- `eΓ` as a pointed map (the blank of `tM` is `eΓ default`). -/
def tP : Turing.PointedMap M.Γ (tM M eK eΓ eQ).Γ := ⟨eΓ, rfl⟩

/-- The transported configuration. -/
def tC (cf : Cfg M.K M.Γ M.Q) : Cfg (tM M eK eΓ eQ).K (tM M eK eΓ eQ).Γ (tM M eK eΓ eQ).Q :=
  ⟨eQ cf.q, fun k => (cf.tapes (eK.symm k)).map (tP M eK eΓ eQ)⟩

theorem scanned_tC (cf : Cfg M.K M.Γ M.Q) :
    (tM M eK eΓ eQ).scanned (tC M eK eΓ eQ cf) = fun k => eΓ (M.scanned cf (eK.symm k)) := rfl

theorem code_tC (cf : Cfg M.K M.Γ M.Q) :
    (tM M eK eΓ eQ).code (tC M eK eΓ eQ cf).q ((tM M eK eΓ eQ).scanned (tC M eK eΓ eQ cf)) =
      (M.code cf.q (M.scanned cf)).map (tOut M eK eΓ eQ) := by
  rw [scanned_tC]
  show (M.code (eQ.symm (eQ cf.q)) (eΓ.symm ∘ (fun k => eΓ (M.scanned cf (eK.symm k))) ∘ eK)).map
      (tOut M eK eΓ eQ) = _
  have h1 : eQ.symm (eQ cf.q) = cf.q := eQ.symm_apply_apply _
  have h2 : (eΓ.symm ∘ (fun k => eΓ (M.scanned cf (eK.symm k))) ∘ eK) = M.scanned cf := by
    funext k
    simp
  rw [h1, h2]

theorem headMove_apply_map {Γ Γ' : Type} [Inhabited Γ] [Inhabited Γ'] (f : Turing.PointedMap Γ Γ')
    (m : HeadMove) (T : Turing.Tape Γ) : m.apply (T.map f) = (m.apply T).map f := by
  cases m <;> simp [HeadMove.apply, Turing.Tape.map_move]

theorem apply_tC (cf : Cfg M.K M.Γ M.Q) (out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)) :
    (tM M eK eΓ eQ).apply (tC M eK eΓ eQ cf) (tOut M eK eΓ eQ out) = tC M eK eΓ eQ (M.apply cf out) := by
  apply cfg_ext
  · rfl
  · funext k
    show (out.2.2 (eK.symm k)).apply
        (((cf.tapes (eK.symm k)).map (tP M eK eΓ eQ)).write ((tP M eK eΓ eQ) (out.2.1 (eK.symm k)))) =
      ((out.2.2 (eK.symm k)).apply ((cf.tapes (eK.symm k)).write (out.2.1 (eK.symm k)))).map (tP M eK eΓ eQ)
    have hw : ((cf.tapes (eK.symm k)).map (tP M eK eΓ eQ)).write ((tP M eK eΓ eQ) (out.2.1 (eK.symm k))) =
        ((cf.tapes (eK.symm k)).write (out.2.1 (eK.symm k))).map (tP M eK eΓ eQ) :=
      (Turing.Tape.map_write (tP M eK eΓ eQ) _ _).symm
    rw [hw, headMove_apply_map]

theorem next_tC (cf : Cfg M.K M.Γ M.Q)
    (d : Cfg (tM M eK eΓ eQ).K (tM M eK eΓ eQ).Γ (tM M eK eΓ eQ).Q) :
    (tM M eK eΓ eQ).Next (tC M eK eΓ eQ cf) d ↔ ∃ cf', M.Next cf cf' ∧ d = tC M eK eΓ eQ cf' := by
  unfold NMachine.Next
  rw [code_tC]
  constructor
  · rintro ⟨out', hout', rfl⟩
    obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hout'
    exact ⟨M.apply cf out, ⟨out, hout, rfl⟩, apply_tC M eK eΓ eQ cf out⟩
  · rintro ⟨cf', ⟨out, hout, rfl⟩, rfl⟩
    exact ⟨tOut M eK eΓ eQ out, List.mem_map.2 ⟨out, hout, rfl⟩, apply_tC M eK eΓ eQ cf out⟩

theorem reach_tC (t : ℕ) : ∀ (cf : Cfg M.K M.Γ M.Q)
    (d : Cfg (tM M eK eΓ eQ).K (tM M eK eΓ eQ).Γ (tM M eK eΓ eQ).Q),
    (tM M eK eΓ eQ).Reach (tC M eK eΓ eQ cf) t d ↔ ∃ cf', M.Reach cf t cf' ∧ d = tC M eK eΓ eQ cf' := by
  induction t with
  | zero =>
    intro cf d
    show d = tC M eK eΓ eQ cf ↔ ∃ cf', cf' = cf ∧ d = tC M eK eΓ eQ cf'
    constructor
    · rintro rfl
      exact ⟨cf, rfl, rfl⟩
    · rintro ⟨cf', rfl, rfl⟩
      rfl
  | succ t ih =>
    intro cf d
    show (∃ d₁, (tM M eK eΓ eQ).Next (tC M eK eΓ eQ cf) d₁ ∧ (tM M eK eΓ eQ).Reach d₁ t d) ↔
      ∃ cf', (∃ c₁, M.Next cf c₁ ∧ M.Reach c₁ t cf') ∧ d = tC M eK eΓ eQ cf'
    constructor
    · rintro ⟨d₁, h1, h2⟩
      obtain ⟨c₁, hc₁, rfl⟩ := (next_tC M eK eΓ eQ cf d₁).1 h1
      obtain ⟨cf', h3, rfl⟩ := (ih c₁ d).1 h2
      exact ⟨cf', ⟨c₁, hc₁, h3⟩, rfl⟩
    · rintro ⟨cf', ⟨c₁, hc₁, h3⟩, rfl⟩
      exact ⟨tC M eK eΓ eQ c₁, (next_tC M eK eΓ eQ cf _).2 ⟨c₁, hc₁, rfl⟩, (ih c₁ _).2 ⟨cf', h3, rfl⟩⟩

theorem halted_tC (cf : Cfg M.K M.Γ M.Q) :
    (tM M eK eΓ eQ).Halted (tC M eK eΓ eQ cf) ↔ M.Halted cf := by
  unfold NMachine.Halted
  rw [code_tC]
  exact List.map_eq_nil_iff

theorem accept_tC (cf : Cfg M.K M.Γ M.Q) :
    (tM M eK eΓ eQ).accept (tC M eK eΓ eQ cf).q = M.accept cf.q := by
  show M.accept (eQ.symm (eQ cf.q)) = M.accept cf.q
  rw [eQ.symm_apply_apply]

theorem init_tC (x : List Bool) : (tM M eK eΓ eQ).init x = tC M eK eΓ eQ (M.init x) := by
  apply cfg_ext
  · rfl
  · funext k
    show (if k = (tM M eK eΓ eQ).inputTape then Turing.Tape.mk₁ (x.map (tM M eK eΓ eQ).inputSymbol)
        else Turing.Tape.mk₁ []) =
      Turing.Tape.map (tP M eK eΓ eQ)
        (if eK.symm k = M.inputTape then Turing.Tape.mk₁ (x.map M.inputSymbol) else Turing.Tape.mk₁ [])
    by_cases h : eK.symm k = M.inputTape
    · have h' : k = (tM M eK eΓ eQ).inputTape := eK.symm_apply_eq.1 h
      rw [if_pos h', if_pos h, Turing.Tape.map_mk₁, List.map_map]
      all_goals rfl
    · have h' : ¬ k = (tM M eK eΓ eQ).inputTape := fun h'' => h (eK.symm_apply_eq.2 h'')
      rw [if_neg h', if_neg h, Turing.Tape.map_mk₁, List.map_nil]

theorem lang_tM : lang (tM M eK eΓ eQ) = lang M := by
  funext x
  refine Bool.eq_iff_iff.2 ?_
  simp only [lang, decide_eq_true_iff]
  rw [init_tC]
  constructor
  · rintro ⟨t, d, hr, hh, ha⟩
    obtain ⟨cf, hcf, rfl⟩ := (reach_tC M eK eΓ eQ t _ _).1 hr
    exact ⟨t, cf, hcf, (halted_tC M eK eΓ eQ cf).1 hh, (accept_tC M eK eΓ eQ cf).symm.trans ha⟩
  · rintro ⟨t, cf, hcf, hh, ha⟩
    exact ⟨t, tC M eK eΓ eQ cf, (reach_tC M eK eΓ eQ t _ _).2 ⟨cf, hcf, rfl⟩,
      (halted_tC M eK eΓ eQ cf).2 hh, (accept_tC M eK eΓ eQ cf).trans ha⟩

end Transport

theorem exists_code (M : NMachine) : ∃ k : Code, codeLang k = lang M := by
  refine ⟨⟨(Fintype.card M.K, Fintype.card M.Γ, Fintype.card M.Q),
    tData M (Fintype.equivFin M.K) (Fintype.equivFin M.Γ) (Fintype.equivFin M.Q)⟩, ?_⟩
  unfold codeLang
  split
  · exact lang_tM M (Fintype.equivFin M.K) (Fintype.equivFin M.Γ) (Fintype.equivFin M.Q)
  · rename_i h
    exact (h ⟨tData_inj M _ _ _, tData_ne M _ _ _⟩).elim

/-- For every clock `f`, the class NTIME(f) is countable. -/
theorem ntime_class_countable (f : ℕ → ℝ) : {L | NTIMEIn L f}.Countable := by
  have hsub : {L | NTIMEIn L f} ⊆ Set.range codeLang := by
    intro L hL
    obtain ⟨M, rfl⟩ := eq_lang hL
    obtain ⟨k, hk⟩ := exists_code M
    exact ⟨k, hk⟩
  exact Set.Countable.mono hsub (Set.countable_range codeLang)

/-- The languages are not countable (Cantor). -/
theorem not_countable_lang : ¬ (Set.univ : Set (List Bool → Bool)).Countable := by
  intro h
  have hc : Countable (List Bool → Bool) := Set.countable_univ_iff.1 h
  have hinj : Function.Injective (fun g : ℕ → Bool => fun l : List Bool => g l.length) := by
    intro g g' hg
    funext n
    have h1 := congrFun hg (List.replicate n false)
    simpa using h1
  have : Countable (ℕ → Bool) := hinj.countable
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (ℕ → Bool)
  classical
  apply Function.cantor_injective (fun s : Set ℕ => e (fun n => decide (n ∈ s)))
  intro s t hst
  have h2 := he hst
  ext n
  have h3 := congrFun h2 n
  simpa using h3

/-- **G3 (counting).** For every clock `f` some language is not in NTIME(f); in particular not in NTIME(n). -/
theorem exists_not_ntime (f : ℕ → ℝ) : ∃ L : List Bool → Bool, ¬ NTIMEIn L f := by
  by_contra h
  push Not at h
  exact not_countable_lang (Set.Countable.mono (fun L _ => h L) (ntime_class_countable f))

theorem exists_not_ntime_lin : ∃ L : List Bool → Bool, ¬ NTIMEIn L (fun n => (n : ℝ)) :=
  exists_not_ntime _

end NTimeGuards
end C1Challenge

#print axioms C1Challenge.NTimeGuards.ntime_of_dtime
#print axioms C1Challenge.NTimeGuards.dtime_lin_sub_ntime_lin
#print axioms C1Challenge.NTimeGuards.ntime_firstBit
#print axioms C1Challenge.NTimeGuards.ntime_const
#print axioms C1Challenge.NTimeGuards.loop_not_witness
#print axioms C1Challenge.NTimeGuards.exists_not_ntime_lin
#print axioms C1Challenge.NTimeGuards.ntime_fork
#print axioms C1Challenge.NTimeGuards.fork_reject
#print axioms C1Challenge.NTimeGuards.fork_two_accept
#print axioms C1Challenge.NTimeGuards.forkLoop_fast_accept
#print axioms C1Challenge.NTimeGuards.forkLoop_not_witness
