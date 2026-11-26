import P1Int.Interfaces
import C1Challenge.NonVacuity

/-!
# P1Int.Guards: non-vacuity of the interface `ParDecidesFrom` (owner: P1-lean-integ copy B)

Two drafts of the interfaces were vacuous (board 1297: `NTIMELinLog`; board 1362: `ParDecidesFrom` with guess
length = time, where the last guess bit is never read and the count of accepting guesses is always even).
This file checks the FIXED `ParDecidesFrom` (time `τ n + |withGuess w x|`) in the shapes used by W2 and Lemma P:

* `parDecides_firstBit`: for EVERY guess length `g` and every time function `τ ≥ 1`, the language
  `firstBit` (first bit of `x`, non-constant) has a parity verifier: it accepts only the all-zero guess, and
  then answers `firstBit x`. So the parity count is 1 or 0.
* `parDecides_shape_W2`: the shape of W2 conjunct 1 and of the Lemma P hypothesis (`a (n²+1)` guess bits,
  time `b (n²+1)`) admits a non-constant language, for every `a` and every `b ≥ 1`.

The machine `zeroThen M`: scan the guess prefix, erasing it; at a guess bit `1` halt with answer `false`;
at the separator start `M` on `x` (the tape then is exactly `M.init x`). Reuses the tape lemmas of
`C1Challenge.NonVacuity` (`tapesOf`, `erase_tapes`, `head_tapesOf`, `input_ne`, `halts_unique`).
-/

namespace P1Int

open C1Challenge

section ZeroThen

variable (M : Machine)

open Classical in
/-- States `inl q`: run `M`; `inr (some false)`: at a marker or at the separator; `inr (some true)`: at a
guess bit; `inr none`: halted with answer `false`. -/
@[reducible] noncomputable def zeroThen : Machine where
  K := M.K
  inputTape := M.inputTape
  Γ := M.Γ
  Q := M.Q ⊕ Option Bool
  initialState := Sum.inr (some false)
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q r => match q with
    | Sum.inl q => (M.code q r).map fun out => (Sum.inl out.1, out.2.1, out.2.2)
    | Sum.inr none => none
    | Sum.inr (some true) =>
        if r M.inputTape = M.inputSymbol true then some (Sum.inr none, r, fun _ => HeadMove.stay)
        else some (Sum.inr (some false), fun _ => default,
          fun k => if k = M.inputTape then HeadMove.right else HeadMove.stay)
    | Sum.inr (some false) =>
        some (if r M.inputTape = M.inputSymbol false then Sum.inl M.initialState
            else Sum.inr (some true),
          fun _ => default, fun k => if k = M.inputTape then HeadMove.right else HeadMove.stay)
  accept := fun q => match q with
    | Sum.inl q => M.accept q
    | Sum.inr _ => false

/-- A configuration of `M` as a configuration of `zeroThen M`. -/
def embedZ (c : Cfg M.K M.Γ M.Q) : Cfg M.K M.Γ (M.Q ⊕ Option Bool) := ⟨Sum.inl c.q, c.tapes⟩

theorem stepZ_embed (c : Cfg M.K M.Γ M.Q) :
    (zeroThen M).step (embedZ M c) = (M.step c).map (embedZ M) := by
  unfold Machine.step
  simp only [zeroThen, embedZ, Option.map_map]
  rfl

theorem runZ_embed (c : Cfg M.K M.Γ M.Q) (t : ℕ) :
    (fun oc => Option.bind oc (zeroThen M).step)^[t] (some (embedZ M c)) =
      ((fun oc => Option.bind oc M.step)^[t] (some c)).map (embedZ M) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases (fun oc => Option.bind oc M.step)^[t] (some c) with
    | none => rfl
    | some d =>
      rw [Option.map_some, Option.bind_some]
      exact stepZ_embed M d

theorem input_ne' : M.inputSymbol false ≠ M.inputSymbol true := fun h => (input_ne M) h.symm

theorem stepZ_marker (rest : List Bool) :
    (zeroThen M).step ⟨Sum.inr (some false), tapesOf M (true :: rest)⟩ =
      some ⟨Sum.inr (some true), tapesOf M rest⟩ := by
  unfold Machine.step
  simp only [zeroThen, head_tapesOf, input_ne, ite_false, Option.map_some]
  rw [erase_tapes]

theorem stepZ_zero (rest : List Bool) :
    (zeroThen M).step ⟨Sum.inr (some true), tapesOf M (false :: rest)⟩ =
      some ⟨Sum.inr (some false), tapesOf M rest⟩ := by
  unfold Machine.step
  simp only [zeroThen, head_tapesOf, input_ne', ite_false, Option.map_some]
  rw [erase_tapes]

theorem stepZ_one (rest : List Bool) :
    (zeroThen M).step ⟨Sum.inr (some true), tapesOf M (true :: rest)⟩ =
      some ⟨Sum.inr none, tapesOf M (true :: rest)⟩ := by
  unfold Machine.step
  simp only [zeroThen, head_tapesOf, ite_true, Option.map_some]
  congr 2

theorem stepZ_sep (x : List Bool) :
    (zeroThen M).step ⟨Sum.inr (some false), tapesOf M (false :: x)⟩ =
      some (embedZ M (M.init x)) := by
  unfold Machine.step
  simp only [zeroThen, head_tapesOf, ite_true, Option.map_some]
  rw [erase_tapes]
  rfl

/-- All guess bits zero: after `2|w| + 1` steps the machine is `M` at the start on `x`. -/
theorem zero_run (x : List Bool) : ∀ w : List Bool, (∀ b ∈ w, b = false) →
    (fun oc => Option.bind oc (zeroThen M).step)^[2 * w.length + 1]
        (some ⟨Sum.inr (some false), tapesOf M ((w.flatMap fun b => [true, b]) ++ false :: x)⟩) =
      some (embedZ M (M.init x))
  | [], _ => by
    simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Function.iterate_one, Option.bind_some]
    exact stepZ_sep M x
  | b :: w, hw => by
    have hb : b = false := hw b (List.mem_cons_self ..)
    subst hb
    have hl : ((false :: w).flatMap fun b => [true, b]) ++ false :: x =
        true :: false :: ((w.flatMap fun b => [true, b]) ++ false :: x) := by simp
    have h2 : 2 * (false :: w).length + 1 = (2 * w.length + 1) + 1 + 1 := by
      simp only [List.length_cons]; ring
    rw [h2, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, hl]
    beta_reduce
    rw [Option.bind_some, stepZ_marker, Option.bind_some, stepZ_zero]
    exact zero_run x w (fun b hb' => hw b (List.mem_cons_of_mem _ hb'))

/-- Some guess bit is `1`: the machine halts with answer `false` within `2|w|` steps. -/
theorem reject_run (x : List Bool) : ∀ w : List Bool, true ∈ w →
    ∃ t ≤ 2 * w.length, ∃ c : Cfg M.K M.Γ (M.Q ⊕ Option Bool),
      (fun oc => Option.bind oc (zeroThen M).step)^[t]
          (some ⟨Sum.inr (some false), tapesOf M ((w.flatMap fun b => [true, b]) ++ false :: x)⟩) =
        some c ∧ (zeroThen M).step c = none ∧ (zeroThen M).accept c.q = false
  | [], h => by simp at h
  | b :: w, h => by
    cases b with
    | true =>
      refine ⟨2, by simp, ⟨Sum.inr none, tapesOf M (true :: ((w.flatMap fun b => [true, b]) ++ false :: x))⟩,
        ?_, rfl, rfl⟩
      have hl : ((true :: w).flatMap fun b => [true, b]) ++ false :: x =
          true :: true :: ((w.flatMap fun b => [true, b]) ++ false :: x) := by simp
      rw [hl, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
      beta_reduce
      rw [Option.bind_some, stepZ_marker, Option.bind_some, stepZ_one]
    | false =>
      have hw : true ∈ w := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h' (by decide)
        · exact h'
      obtain ⟨t, ht, c, hc, hstop, hacc⟩ := reject_run x w hw
      refine ⟨t + 2, by simp only [List.length_cons]; omega, c, ?_, hstop, hacc⟩
      have hl : ((false :: w).flatMap fun b => [true, b]) ++ false :: x =
          true :: false :: ((w.flatMap fun b => [true, b]) ++ false :: x) := by simp
      rw [hl, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one]
      beta_reduce
      rw [Option.bind_some, stepZ_marker, Option.bind_some, stepZ_zero]
      exact hc

theorem initZ (w x : List Bool) :
    (zeroThen M).init (withGuess w x) =
      ⟨Sum.inr (some false), tapesOf M ((w.flatMap fun b => [true, b]) ++ false :: x)⟩ := rfl

theorem halts_zero {x : List Bool} {b : Bool} {T : ℕ} (h : HaltsWithin M x b T) (w : List Bool)
    (hw : ∀ c ∈ w, c = false) :
    HaltsWithin (zeroThen M) (withGuess w x) b (2 * w.length + 1 + T) := by
  obtain ⟨t, ht, c, hc, hstop, hb⟩ := h
  refine ⟨t + (2 * w.length + 1), by omega, embedZ M c, ?_, ?_, hb⟩
  · rw [Function.iterate_add_apply, initZ, zero_run M x w hw, runZ_embed, hc]
    rfl
  · rw [stepZ_embed, hstop]
    rfl

theorem halts_reject (x w : List Bool) (hw : true ∈ w) :
    HaltsWithin (zeroThen M) (withGuess w x) false (2 * w.length) := by
  obtain ⟨t, ht, c, hc, hstop, hacc⟩ := reject_run M x w hw
  exact ⟨t, ht, c, by rw [initZ]; exact hc, hstop, hacc⟩

end ZeroThen

/-- `firstBitMachine` answers `firstBit x` after one step. -/
theorem firstBit_halts (x : List Bool) : HaltsWithin firstBitMachine x (firstBit x) 1 := by
  refine ⟨1, le_rfl,
    ⟨some (decide (((firstBitMachine.init x).tapes ()).head = some true)),
      (firstBitMachine.init x).tapes⟩, ?_, rfl, ?_⟩
  · rw [Function.iterate_one]
    simp only [Option.bind_some, Machine.step, firstBitMachine]
    congr 1
  · cases x with
    | nil => rfl
    | cons b x => cases b <;> rfl

theorem length_withGuess (w x : List Bool) :
    (withGuess w x).length = 2 * w.length + 1 + x.length := by
  simp only [withGuess, List.length_append, length_pre, List.length_cons]
  ring

/-- **Guard.** For every guess length `g` and every time function `τ ≥ 1`, the non-constant language
`firstBit` has a parity verifier in the fixed sense of `ParDecidesFrom`. -/
theorem parDecides_firstBit (g τ : ℕ → ℕ) (hτ : ∀ n, 1 ≤ τ n) :
    ParDecidesFrom (zeroThen firstBitMachine) firstBit g τ 0 := by
  classical
  intro x _
  -- every guess halts within the bound, with answer `firstBit x` (all-zero guess) or `false`
  have run : ∀ w : Fin (g x.length) → Bool,
      ((∀ i, w i = false) ∧ HaltsWithin (zeroThen firstBitMachine) (withGuess (List.ofFn w) x)
          (firstBit x) (τ x.length + (withGuess (List.ofFn w) x).length)) ∨
      ((∃ i, w i = true) ∧ HaltsWithin (zeroThen firstBitMachine) (withGuess (List.ofFn w) x)
          false (τ x.length + (withGuess (List.ofFn w) x).length)) := by
    intro w
    have hlen := length_withGuess (List.ofFn w) x
    by_cases h : ∃ i, w i = true
    · right
      refine ⟨h, (halts_reject firstBitMachine x (List.ofFn w) (List.mem_ofFn.mpr h)).mono ?_⟩
      rw [hlen]; omega
    · left
      have hz : ∀ i, w i = false := fun i => by
        cases hi : w i
        · rfl
        · exact absurd ⟨i, hi⟩ h
      refine ⟨hz, (halts_zero firstBitMachine (firstBit_halts x) (List.ofFn w) ?_).mono ?_⟩
      · intro c hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        exact hz i
      · rw [hlen]; have := hτ x.length; omega
  refine ⟨fun w => ?_, ?_⟩
  · rcases run w with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  · -- the accepting guesses: only the all-zero guess, and only if `firstBit x`
    have acc : ∀ w : Fin (g x.length) → Bool,
        HaltsWithin (zeroThen firstBitMachine) (withGuess (List.ofFn w) x) true
          (τ x.length + (withGuess (List.ofFn w) x).length) ↔ (w = fun _ => false) ∧ firstBit x = true := by
      intro w
      rcases run w with ⟨hz, h⟩ | ⟨⟨i, hi⟩, h⟩
      · have hw : w = fun _ => false := funext hz
        constructor
        · intro ht
          exact ⟨hw, halts_unique _ h ht⟩
        · rintro ⟨-, hb⟩
          rw [← hb]
          exact h
      · constructor
        · intro ht
          exact absurd (halts_unique _ h ht) (by decide)
        · rintro ⟨rfl, -⟩
          simp at hi
    cases hfx : firstBit x
    · simp only [Bool.false_eq_true, false_iff]
      rw [Finset.card_eq_zero.mpr]
      · exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩
      · rw [Finset.filter_eq_empty_iff]
        intro w _ hw
        have := (acc w).mp hw
        rw [hfx] at this
        exact absurd this.2 (by decide)
    · simp only [true_iff]
      convert odd_one
      rw [Finset.card_eq_one]
      refine ⟨fun _ => false, ?_⟩
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (acc _).mpr ⟨rfl, hfx⟩⟩, ?_⟩
      intro w hw
      exact ((acc w).mp (Finset.mem_filter.mp hw).2).1

/-- **Guard, the shape of W2 and Lemma P.** With `a (n² + 1)` guess bits and time `b (n² + 1)` (plus the
input length), `ParDecidesFrom` admits the non-constant language `firstBit`, for every `a` and `b ≥ 1`. -/
theorem parDecides_shape_W2 (a b : ℕ) (hb : 1 ≤ b) :
    ∃ V : Machine, ParDecidesFrom V firstBit (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 :=
  ⟨_, parDecides_firstBit _ _ fun n => by
    have := Nat.mul_le_mul hb (Nat.le_add_left 1 (n ^ 2))
    simpa using this⟩

end P1Int
