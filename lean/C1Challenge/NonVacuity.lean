import C1Challenge.Statement

/-!
# Non-vacuity of the C1 Challenge definitions

The first draft of `NTIMELinLog` (time bound `c * (n + 1)`, not counting the guess prefix) was vacuous: it
contained only constant languages (research/p1/lean/Case1/P1Case1/CoTransRefute.lean). These lemmas
guard the fixed definitions against that kind of error. All of them are sorry-free.

* `ntime_firstBit`: the NTIME side contains a language that depends on its input.
* `dtime_firstBit`: the DTIME side is not empty (so `¬ DTIMEIn` is not automatic).
* `ntime_of_dtime_linear`: every language in deterministic linear time is in the NTIME class.
* `guessLen_eq_floor`: `guessLen n = ⌊2 log₂ n⌋` for every `n` (with `Real.logb 2 0 = 0`).
* `halts_unique`, `HaltsWithin.mono`: the answer of a halting run is unique; time bounds are monotone.

Statements of the guards: G3-chief (board 1314). Proofs: P1-lean-integ.
-/

namespace C1Challenge

/-! ## Runs -/

section Runs

variable (M : Machine)

theorem iterate_bind_none (t : ℕ) :
    (fun oc => Option.bind oc M.step)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih

/-- After a halt the run is `none` forever. -/
theorem run_after_halt {input : List Bool} {s : ℕ} {c₀ : Cfg M.K M.Γ M.Q}
    (hs : (fun oc => Option.bind oc M.step)^[s] (some (M.init input)) = some c₀)
    (hstop : M.step c₀ = none) (k : ℕ) :
    (fun oc => Option.bind oc M.step)^[s + 1 + k] (some (M.init input)) = none := by
  rw [Nat.add_comm (s + 1) k, Function.iterate_add_apply, Function.iterate_succ_apply', hs]
  simp only [Option.bind_some, hstop]
  exact iterate_bind_none M k

/-- A machine gives at most one answer on an input. -/
theorem halts_unique {input : List Bool} {b b' : Bool} {T T' : ℕ}
    (h : HaltsWithin M input b T) (h' : HaltsWithin M input b' T') : b = b' := by
  obtain ⟨t, -, c, hc, hstop, hb⟩ := h
  obtain ⟨t', -, c', hc', hstop', hb'⟩ := h'
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ : ∃ k, t' = t + 1 + k := ⟨t' - t - 1, by omega⟩
    rw [run_after_halt M hc hstop k] at hc'
    exact absurd hc' (by simp)
  · subst heq
    rw [hc] at hc'
    cases hc'
    exact hb.symm.trans hb'
  · obtain ⟨k, rfl⟩ : ∃ k, t = t' + 1 + k := ⟨t - t' - 1, by omega⟩
    rw [run_after_halt M hc' hstop' k] at hc
    exact absurd hc (by simp)

end Runs

theorem HaltsWithin.mono {M : Machine} {input : List Bool} {b : Bool} {T T' : ℕ}
    (h : HaltsWithin M input b T) (hT : T ≤ T') : HaltsWithin M input b T' := by
  obtain ⟨t, ht, c, h1, h2, h3⟩ := h
  exact ⟨t, ht.trans hT, c, h1, h2, h3⟩

/-! ## The guess budget is the paper's `⌊2 log₂ n⌋` -/

theorem guessLen_eq_floor (n : ℕ) : (guessLen n : ℤ) = ⌊2 * Real.logb 2 n⌋ := by
  have h1 : (2 : ℝ) * Real.logb 2 n = Real.logb ((2 : ℕ) : ℝ) (((n ^ 2 : ℕ)) : ℝ) := by
    push_cast
    rw [Real.logb_pow]
    norm_num
  rw [h1, Real.floor_logb_natCast (by positivity), Int.log_natCast]
  rfl

/-! ## A language that depends on its input -/

/-- A language that depends on its input: the first bit is `true`. -/
def firstBit (x : List Bool) : Bool := x.headD false

theorem firstBit_nonconstant : firstBit [true] ≠ firstBit [] := by decide

/-- One tape, alphabet `Option Bool` (blank `none`), states `Option Bool` (`none` = start, `some b` = halted
with answer `b`). One step reads the first cell. -/
@[reducible] def firstBitMachine : Machine where
  K := Unit
  inputTape := ()
  Γ := Option Bool
  Q := Option Bool
  initialState := none
  inputSymbol := some
  input_injective := Option.some_injective Bool
  input_ne_blank := fun b => Option.some_ne_none b
  code := fun q r => match q with
    | none => some (some (decide (r () = some true)), r, fun _ => HeadMove.stay)
    | some _ => none
  accept := fun q => q.getD false

/-- The DTIME side contains `firstBit`, for every nonnegative bound (the machine reads one cell). -/
theorem dtime_firstBit (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) : DTIMEIn firstBit f := by
  refine ⟨firstBitMachine, 1, fun x => ⟨1, ?_, ?_⟩⟩
  · have := hf x.length
    push_cast
    linarith
  · refine ⟨1, le_rfl,
      ⟨some (decide (((firstBitMachine.init x).tapes ()).head = some true)),
        (firstBitMachine.init x).tapes⟩, ?_, rfl, ?_⟩
    · rw [Function.iterate_one]
      simp only [Option.bind_some, Machine.step, firstBitMachine]
      congr 1
    · cases x with
      | nil => rfl
      | cons b x => cases b <;> rfl

/-! ## Deterministic linear time is inside the NTIME class -/

section Erase

variable (M : Machine)

open Classical in
/-- The verifier: erase the guess prefix while moving right (state `inr false`: at a marker or at the
separator; state `inr true`: at a guess bit), then run `M` (states `inl q`). -/
@[reducible] noncomputable def eraseThen : Machine where
  K := M.K
  inputTape := M.inputTape
  Γ := M.Γ
  Q := M.Q ⊕ Bool
  initialState := Sum.inr false
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q r => match q with
    | Sum.inl q => (M.code q r).map fun out => (Sum.inl out.1, out.2.1, out.2.2)
    | Sum.inr true =>
        some (Sum.inr false, fun _ => default,
          fun k => if k = M.inputTape then HeadMove.right else HeadMove.stay)
    | Sum.inr false =>
        some (if r M.inputTape = M.inputSymbol false then Sum.inl M.initialState else Sum.inr true,
          fun _ => default, fun k => if k = M.inputTape then HeadMove.right else HeadMove.stay)
  accept := fun q => match q with
    | Sum.inl q => M.accept q
    | Sum.inr _ => false

/-- A configuration of `M` as a configuration of `eraseThen M`. -/
def embed (c : Cfg M.K M.Γ M.Q) : Cfg M.K M.Γ (M.Q ⊕ Bool) := ⟨Sum.inl c.q, c.tapes⟩

theorem step_embed (c : Cfg M.K M.Γ M.Q) :
    (eraseThen M).step (embed M c) = (M.step c).map (embed M) := by
  unfold Machine.step
  simp only [eraseThen, embed, Option.map_map]
  rfl

theorem run_embed (c : Cfg M.K M.Γ M.Q) (t : ℕ) :
    (fun oc => Option.bind oc (eraseThen M).step)^[t] (some (embed M c)) =
      ((fun oc => Option.bind oc M.step)^[t] (some c)).map (embed M) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases (fun oc => Option.bind oc M.step)^[t] (some c) with
    | none => rfl
    | some d =>
      rw [Option.map_some, Option.bind_some]
      exact step_embed M d

/-- Tapes with the list `l` on the input tape (head on its first letter) and blank elsewhere. -/
def tapesOf (l : List Bool) : M.K → Turing.Tape M.Γ := fun k =>
  if k = M.inputTape then Turing.Tape.mk₁ (l.map M.inputSymbol) else Turing.Tape.mk₁ []

theorem blank_cons :
    (Turing.ListBlank.mk ([] : List M.Γ)).cons default = Turing.ListBlank.mk [] := by
  rw [Turing.ListBlank.cons_mk]
  exact Quotient.sound' (Or.inr ⟨1, rfl⟩)

theorem head_tapesOf (a : Bool) (rest : List Bool) :
    (tapesOf M (a :: rest) M.inputTape).head = M.inputSymbol a := by
  simp [tapesOf, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']

/-- Erase the current cell everywhere and move the input head right. -/
theorem erase_tapes (a : Bool) (rest : List Bool) :
    (fun k => (if k = M.inputTape then HeadMove.right else HeadMove.stay).apply
      ((tapesOf M (a :: rest) k).write default)) = tapesOf M rest := by
  funext k
  by_cases hk : k = M.inputTape
  · subst hk
    simp only [tapesOf, ite_true, HeadMove.apply, Turing.Tape.mk₁, Turing.Tape.mk₂,
      Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Turing.ListBlank.tail_mk, List.map_cons, List.tail_cons,
      blank_cons]
  · simp only [tapesOf, hk, ite_false, HeadMove.apply, Turing.Tape.mk₁, Turing.Tape.mk₂,
      Turing.Tape.write_mk', Turing.ListBlank.tail_mk, List.tail_nil, blank_cons]

theorem input_ne : M.inputSymbol true ≠ M.inputSymbol false := fun h =>
  Bool.noConfusion (M.input_injective h)

theorem stepE_marker (rest : List Bool) :
    (eraseThen M).step ⟨Sum.inr false, tapesOf M (true :: rest)⟩ =
      some ⟨Sum.inr true, tapesOf M rest⟩ := by
  unfold Machine.step
  simp only [eraseThen, head_tapesOf, input_ne, ite_false, Option.map_some]
  rw [erase_tapes]

theorem stepE_bit (b : Bool) (rest : List Bool) :
    (eraseThen M).step ⟨Sum.inr true, tapesOf M (b :: rest)⟩ =
      some ⟨Sum.inr false, tapesOf M rest⟩ := by
  unfold Machine.step
  simp only [eraseThen, Option.map_some]
  rw [erase_tapes]

theorem stepE_sep (x : List Bool) :
    (eraseThen M).step ⟨Sum.inr false, tapesOf M (false :: x)⟩ = some (embed M (M.init x)) := by
  unfold Machine.step
  simp only [eraseThen, head_tapesOf, ite_true, Option.map_some]
  rw [erase_tapes]
  rfl

theorem length_pre (w : List Bool) : (w.flatMap fun b => [true, b]).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega

theorem erase_run (w x : List Bool) :
    (fun oc => Option.bind oc (eraseThen M).step)^[2 * w.length + 1]
        (some ⟨Sum.inr false, tapesOf M ((w.flatMap fun b => [true, b]) ++ false :: x)⟩) =
      some (embed M (M.init x)) := by
  induction w with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Function.iterate_one, Option.bind_some]
    exact stepE_sep M x
  | cons b w ih =>
    have hl : ((b :: w).flatMap fun b => [true, b]) ++ false :: x =
        true :: b :: ((w.flatMap fun b => [true, b]) ++ false :: x) := by simp
    have h2 : 2 * (b :: w).length + 1 = (2 * w.length + 1) + 1 + 1 := by
      simp only [List.length_cons]; ring
    rw [h2, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, hl]
    beta_reduce
    rw [Option.bind_some, stepE_marker, Option.bind_some, stepE_bit]
    exact ih

theorem halts_eraseThen {x : List Bool} {b : Bool} {T : ℕ} (h : HaltsWithin M x b T)
    (w : List Bool) : HaltsWithin (eraseThen M) (withGuess w x) b (2 * w.length + 1 + T) := by
  obtain ⟨t, ht, c, hc, hstop, hb⟩ := h
  refine ⟨t + (2 * w.length + 1), by omega, embed M c, ?_, ?_, hb⟩
  · rw [Function.iterate_add_apply]
    have h0 : (eraseThen M).init (withGuess w x) =
        ⟨Sum.inr false, tapesOf M ((w.flatMap fun b => [true, b]) ++ false :: x)⟩ := rfl
    rw [h0, erase_run, run_embed, hc]
    rfl
  · rw [step_embed, hstop]
    rfl

end Erase

/-- Every language in deterministic linear time is in the NTIME class (verifier: erase the guess prefix
while moving right, then run the deterministic machine). -/
theorem ntime_of_dtime_linear (L : List Bool → Bool) (h : DTIMEIn L (fun n => (n : ℝ))) :
    NTIMELinLog L := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨eraseThen M, ⌈C⌉₊ + 1, fun x => ?_⟩
  obtain ⟨T, hT, hhalt⟩ := hM x
  have hTc : T ≤ (⌈C⌉₊ + 1) * (x.length + 1) := by
    have hpos : (0 : ℝ) ≤ x.length + 1 := by positivity
    have h1 : (T : ℝ) ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) * (x.length + 1) := by
      calc (T : ℝ) ≤ C * (x.length + 1) := hT
        _ ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) * (x.length + 1) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          push_cast
          linarith [Nat.le_ceil C]
    exact_mod_cast h1
  have key : ∀ w : List Bool, HaltsWithin (eraseThen M) (withGuess w x) (L x)
      ((⌈C⌉₊ + 1) * ((withGuess w x).length + 1)) := by
    intro w
    apply (halts_eraseThen M hhalt w).mono
    have hlen : (withGuess w x).length = 2 * w.length + 1 + x.length := by
      simp only [withGuess, List.length_append, length_pre, List.length_cons]
      ring
    rw [hlen]
    have h3 : 2 * w.length + 1 ≤ (⌈C⌉₊ + 1) * (2 * w.length + 1) := by nlinarith
    calc 2 * w.length + 1 + T
        ≤ (⌈C⌉₊ + 1) * (2 * w.length + 1) + (⌈C⌉₊ + 1) * (x.length + 1) := by omega
      _ = (⌈C⌉₊ + 1) * (2 * w.length + 1 + x.length + 1) := by ring
  refine ⟨fun w _ => ⟨L x, key w⟩, ⟨fun hx => ?_, ?_⟩⟩
  · refine ⟨List.replicate (guessLen x.length) false, List.length_replicate .., ?_⟩
    rw [← hx]
    exact key _
  · rintro ⟨w, -, hw⟩
    exact halts_unique _ (key w) hw

/-- The NTIME side contains a non-constant language. -/
theorem ntime_firstBit : NTIMELinLog firstBit :=
  ntime_of_dtime_linear firstBit (dtime_firstBit _ fun n => Nat.cast_nonneg n)

end C1Challenge
