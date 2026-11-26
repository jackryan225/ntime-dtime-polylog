import P1Case1.TraceGlue

/-!
# P1, Case 1, task G1': the guessing display machine

For a TRANS decider `M` (OpenAI's `FiniteMultiTapeMachine`) we build an OpenAI `Machine` `machine M`:
* tapes `Option M.K` (`none` = output tape, `some k` = tape `k` of `M`), symbols `Option M.Γ`
  (`none` = the separator OpenAI's model requires, `some g` = symbol `g`), states `Bool ⊕ M.Q`
  (`inl false` guess, `inl true` rewind, `inr q` = `M` in state `q`), coins `Bool`;
* layout: `x` on cells `[0,n)` and the placeholder `y` on cells `[n,2n)` of `M`'s input tape, input and
  output heads at cell `n`, everything else blank;
* guess (`n` steps): write the coin on the input tape and on the output tape, move both right, until the
  input head reads a blank (cell `2n`); rewind (`2n+1` steps) to cell `0`; then run `M` step by step.
Accepting runs write the guessed word `Y` on output cells `[n,2n)` and `M` accepts `(x, Y)`, so `Y = xᵀ`.
-/

namespace P1Case1.Display

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication
open OAI.Computability.MultitapeWeakETH (Word Machine InputLayout timely writes initial run)
open scoped Classical

noncomputable section

variable (M : FiniteMultiTapeMachine)

abbrev Sym := Option M.Γ
abbrev St := Bool ⊕ M.Q
abbrev Tp := Option M.K
abbrev Cf := TM.Config (Sym M) (St M) (Tp M)

def blankS : Sym M := some default
def bitS (b : Bool) : Sym M := some (M.inputSymbol b)

theorem bitS_ne_blankS (b : Bool) : bitS M b ≠ blankS M :=
  fun h => M.input_ne_blank b (Option.some.inj h)

theorem bitS_injective : Function.Injective (bitS M) :=
  fun _ _ h => M.input_injective (Option.some.inj h)

def moveTM : HeadMove → TM.Move
  | .left => .left
  | .stay => .stay
  | .right => .right

def rule (c : Bool) : TM.Rule (Sym M) (St M) (Tp M) := fun q r =>
  match q with
  | .inl false =>
    if r (some M.inputTape) = blankS M then
      some (.inl true, fun i => (r i, if i = some M.inputTape then .left else .stay))
    else
      some (.inl false, fun i =>
        if i = some M.inputTape ∨ i = none then (bitS M c, .right) else (r i, .stay))
  | .inl true =>
    if r (some M.inputTape) = blankS M then
      some (.inr M.initialState, fun i => (r i, if i = some M.inputTape then .right else .stay))
    else
      some (.inl true, fun i => (r i, if i = some M.inputTape then .left else .stay))
  | .inr q =>
    (M.code q (fun k => (r (some k)).getD default)).map fun out =>
      (.inr out.1, fun i => match i with
        | none => (r none, .stay)
        | some k => (some (out.2.1 k), moveTM (out.2.2 k)))

def bgTape (p : ℤ) : TM.Tape (Sym M) := ⟨p, fun _ => blankS M⟩

def layout : InputLayout (Sym M) (St M) (Tp M) where
  background n := ⟨.inl false, fun i =>
    bgTape M (if i = some M.inputTape ∨ i = none then (n : ℤ) else 0)⟩
  leftTape := some M.inputTape
  rightTape := some M.inputTape
  leftStart _ := 0
  rightStart n := n
  disjointInputs n i j := Or.inr (by have := i.isLt; omega)

def machine (M : FiniteMultiTapeMachine) : Machine where
  Alphabet := Sym M
  State := St M
  Tapes := Tp M
  Choice := Bool
  bit := bitS M
  bit_injective := bitS_injective M
  sep := none
  blank := blankS M
  markers := fun b => ⟨Option.some_ne_none _, bitS_ne_blankS M b⟩
  sep_ne_blank := by simp [blankS]
  input := some M.inputTape
  output := none
  offset := fun n => n
  start := .inl false
  rule := rule M
  accepts := fun q => match q with
    | .inr q => M.accept q
    | .inl _ => false
  layout := some (layout M)

/-! ## Tapes with absolute positions -/

theorem tape_ext {A : Type} {T U : TM.Tape A} (hp : T.pos = U.pos)
    (ha : ∀ z, T.absolute z = U.absolute z) : T = U := by
  cases T with
  | mk p v =>
  cases U with
  | mk q w =>
  simp only at hp
  subst hp
  congr 1
  funext i
  have h := ha (p + i)
  simpa [TM.Tape.absolute] using h

theorem pos_apply {A : Type} (T : TM.Tape A) (op : A × TM.Move) :
    (T.apply op).pos = T.pos + op.2.shift := rfl

theorem view_zero {A : Type} (T : TM.Tape A) : T.view 0 = T.absolute T.pos := by
  simp [TM.Tape.absolute]

theorem apply_stay_view {A : Type} (T : TM.Tape A) : T.apply (T.view 0, .stay) = T := by
  apply tape_ext
  · simp [pos_apply, TM.Move.shift]
  · intro z
    rw [TM.Tape.absolute_apply]
    split_ifs with h
    · subst h; exact view_zero T
    · rfl

theorem apply_same {A : Type} (T : TM.Tape A) (m : TM.Move) (z : ℤ) :
    (T.apply (T.view 0, m)).absolute z = T.absolute z := by
  rw [TM.Tape.absolute_apply]
  split_ifs with h
  · subst h; exact view_zero T
  · rfl

/-! ## The start configuration -/

section Start

variable {n : ℕ} (x y : Word n)

/-- Input tape before the run: `x` on `[0,n)`, `y` on `[n,2n)`, blank elsewhere. -/
def startCell (z : ℤ) : Sym M :=
  if hx : 0 ≤ z ∧ z.toNat < n then bitS M (x ⟨z.toNat, hx.2⟩)
  else if hy : 0 ≤ z - n ∧ (z - n).toNat < n then bitS M (y ⟨(z - n).toNat, hy.2⟩)
  else blankS M

theorem init_pc : (initial (machine M) x y).pc = .inl false := rfl

theorem init_pos (i : Tp M) : ((initial (machine M) x y).tape i).pos =
    if i = some M.inputTape ∨ i = none then (n : ℤ) else 0 := rfl

theorem init_abs_input (z : ℤ) :
    ((initial (machine M) x y).tape (some M.inputTape)).absolute z = startCell M x y z := by
  simp only [initial, machine, InputLayout.load, layout, TM.Tape.absolute, bgTape, startCell]
  simp

theorem init_abs_other (i : Tp M) (hi : i ≠ some M.inputTape) (z : ℤ) :
    ((initial (machine M) x y).tape i).absolute z = blankS M := by
  simp only [initial, machine, InputLayout.load, layout, TM.Tape.absolute, bgTape]
  simp [hi]

theorem startCell_mid (z : ℤ) (h1 : (n : ℤ) ≤ z) (h2 : z < 2 * n) : startCell M x y z ≠ blankS M := by
  unfold startCell
  have hx : ¬ (0 ≤ z ∧ z.toNat < n) := by omega
  have hy : 0 ≤ z - n ∧ (z - n).toNat < n := by omega
  rw [dif_neg hx, dif_pos hy]
  exact bitS_ne_blankS M _

theorem startCell_low (z : ℤ) (h1 : 0 ≤ z) (h2 : z < n) : startCell M x y z ≠ blankS M := by
  unfold startCell
  have hx : 0 ≤ z ∧ z.toNat < n := by omega
  rw [dif_pos hx]
  exact bitS_ne_blankS M _

theorem startCell_out (z : ℤ) (h : z < 0 ∨ 2 * (n : ℤ) ≤ z) : startCell M x y z = blankS M := by
  unfold startCell
  have hx : ¬ (0 ≤ z ∧ z.toNat < n) := by omega
  have hy : ¬ (0 ≤ z - n ∧ (z - n).toNat < n) := by omega
  rw [dif_neg hx, dif_neg hy]

end Start

/-! ## Guess phase -/

section Phases

variable {n : ℕ} (x y : Word n) (coins : ℕ → Bool)

def outCell (z : ℤ) : Sym M :=
  if (n : ℤ) ≤ z ∧ z < 2 * n then bitS M (coins (z - n).toNat) else blankS M

def finalCell (z : ℤ) : Sym M :=
  if (n : ℤ) ≤ z ∧ z < 2 * n then bitS M (coins (z - n).toNat) else startCell M x y z

def Inv1 (j : ℕ) (cfg : Cf M) : Prop :=
  cfg.pc = .inl false ∧
  (cfg.tape (some M.inputTape)).pos = n + j ∧
  (∀ z, (cfg.tape (some M.inputTape)).absolute z =
    if (n : ℤ) ≤ z ∧ z < n + j then bitS M (coins (z - n).toNat) else startCell M x y z) ∧
  (cfg.tape none).pos = n + j ∧
  (∀ z, (cfg.tape none).absolute z =
    if (n : ℤ) ≤ z ∧ z < n + j then bitS M (coins (z - n).toNat) else blankS M) ∧
  ∀ k, k ≠ M.inputTape → cfg.tape (some k) = bgTape M 0

theorem inv1_zero : Inv1 M x y coins 0 (initial (machine M) x y) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [init_pos]; simp
  · intro z
    have h := init_abs_input M x y z
    have : ¬ ((n : ℤ) ≤ z ∧ z < n + ((0 : ℕ) : ℤ)) := by omega
    rw [if_neg this]
    exact h
  · rw [init_pos]; simp
  · intro z
    have h := init_abs_other M x y none (by simp) z
    have : ¬ ((n : ℤ) ≤ z ∧ z < n + ((0 : ℕ) : ℤ)) := by omega
    rw [if_neg this]
    exact h
  · intro k hk
    apply tape_ext
    · rw [init_pos]; simp [bgTape, hk]
    · intro z
      have h := init_abs_other M x y (some k) (by simpa using hk) z
      exact h

theorem step1 (j : ℕ) (hj : j < n) (cfg : Cf M) (h : Inv1 M x y coins j cfg) :
    ∃ cfg', TM.advance (rule M (coins j)) cfg = some cfg' ∧ Inv1 M x y coins (j + 1) cfg' := by
  obtain ⟨hpc, hpos, habs, opos, oabs, hoth⟩ := h
  have hread : (cfg.tape (some M.inputTape)).view 0 ≠ blankS M := by
    rw [view_zero, hpos, habs]
    have : ¬ ((n : ℤ) ≤ (n : ℤ) + j ∧ (n : ℤ) + j < n + j) := by omega
    rw [if_neg this]
    exact startCell_mid M x y _ (by omega) (by omega)
  refine ⟨⟨.inl false, fun i => (cfg.tape i).apply
      (if i = some M.inputTape ∨ i = none then (bitS M (coins j), .right)
        else ((cfg.tape i).view 0, .stay))⟩, ?_, ?_⟩
  · simp only [TM.advance, hpc, rule, if_neg hread, Option.map_some]
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [true_or, if_true, pos_apply, hpos, TM.Move.shift]
      all_goals (try push_cast); all_goals (try ring)
    · intro z
      simp only [true_or, if_true]
      rw [TM.Tape.absolute_apply, hpos, habs]
      by_cases hz : z = (n : ℤ) + j
      · subst hz
        have hzn : (((n : ℤ) + j - n).toNat) = j := by omega
        rw [if_pos rfl, if_pos (by push_cast; omega), hzn]
      · rw [if_neg hz]
        by_cases hr : (n : ℤ) ≤ z ∧ z < n + j
        · rw [if_pos hr, if_pos (by push_cast; omega)]
        · rw [if_neg hr, if_neg (by push_cast; omega)]
    · simp only [or_true, if_true, pos_apply, opos, TM.Move.shift]
      all_goals (try push_cast); all_goals (try ring)
    · intro z
      simp only [or_true, if_true]
      rw [TM.Tape.absolute_apply, opos, oabs]
      by_cases hz : z = (n : ℤ) + j
      · subst hz
        have hzn : (((n : ℤ) + j - n).toNat) = j := by omega
        rw [if_pos rfl, if_pos (by push_cast; omega), hzn]
      · rw [if_neg hz]
        by_cases hr : (n : ℤ) ≤ z ∧ z < n + j
        · rw [if_pos hr, if_pos (by push_cast; omega)]
        · rw [if_neg hr, if_neg (by push_cast; omega)]
    · intro k hk
      have h1 : ¬ (some k = some M.inputTape ∨ some k = (none : Tp M)) := by simpa using hk
      simp only [if_neg h1]
      rw [apply_stay_view, hoth k hk]

theorem phase1 (j : ℕ) (hj : j ≤ n) :
    ∃ cfg, run (machine M) coins (initial (machine M) x y) j = some cfg ∧
      Inv1 M x y coins j cfg := by
  induction j with
  | zero => exact ⟨_, rfl, inv1_zero M x y coins⟩
  | succ j ih =>
    obtain ⟨cfg, hrun, hinv⟩ := ih (by omega)
    obtain ⟨cfg', hstep, hinv'⟩ := step1 M x y coins j (by omega) cfg hinv
    refine ⟨cfg', ?_, hinv'⟩
    simp only [run, hrun, Option.bind_some]
    exact hstep

/-! ## Rewind phase -/

def Inv2 (j : ℕ) (cfg : Cf M) : Prop :=
  cfg.pc = .inl true ∧
  (cfg.tape (some M.inputTape)).pos = 2 * n - 1 - j ∧
  (∀ z, (cfg.tape (some M.inputTape)).absolute z = finalCell M x y coins z) ∧
  (cfg.tape none).pos = 2 * n ∧
  (∀ z, (cfg.tape none).absolute z = outCell M (n := n) coins z) ∧
  ∀ k, k ≠ M.inputTape → cfg.tape (some k) = bgTape M 0

theorem switch1 (cfg : Cf M) (h : Inv1 M x y coins n cfg) :
    ∃ cfg', TM.advance (rule M (coins n)) cfg = some cfg' ∧ Inv2 M x y coins 0 cfg' := by
  obtain ⟨hpc, hpos, habs, opos, oabs, hoth⟩ := h
  have hread : (cfg.tape (some M.inputTape)).view 0 = blankS M := by
    rw [view_zero, hpos, habs]
    have : ¬ ((n : ℤ) ≤ (n : ℤ) + n ∧ (n : ℤ) + n < n + n) := by omega
    rw [if_neg this]
    exact startCell_out M x y _ (Or.inr (by omega))
  refine ⟨⟨.inl true, fun i => (cfg.tape i).apply
      ((cfg.tape i).view 0, if i = some M.inputTape then .left else .stay)⟩, ?_, ?_⟩
  · simp only [TM.advance, hpc, rule, if_pos hread, Option.map_some]
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [if_true, pos_apply, hpos, TM.Move.shift]
      all_goals (try push_cast); all_goals (try ring)
    · intro z
      rw [apply_same, habs]
      unfold finalCell
      by_cases hr : (n : ℤ) ≤ z ∧ z < 2 * n
      · rw [if_pos hr, if_pos (by push_cast; omega)]
      · rw [if_neg hr, if_neg (by push_cast; omega)]
    · simp only [reduceCtorEq, if_false, apply_stay_view, opos]
      all_goals (try push_cast); all_goals (try ring)
    · intro z
      simp only [reduceCtorEq, if_false, apply_stay_view, oabs]
      unfold outCell
      by_cases hr : (n : ℤ) ≤ z ∧ z < 2 * n
      · rw [if_pos hr, if_pos (by push_cast; omega)]
      · rw [if_neg hr, if_neg (by push_cast; omega)]
    · intro k hk
      have h1 : some k ≠ some M.inputTape := by simpa using hk
      simp only [if_neg h1, apply_stay_view, hoth k hk]

theorem finalCell_mid (z : ℤ) (h1 : 0 ≤ z) (h2 : z < 2 * n) :
    finalCell M x y coins z ≠ blankS M := by
  unfold finalCell
  split_ifs with h
  · exact bitS_ne_blankS M _
  · exact startCell_low M x y z h1 (by omega)

theorem finalCell_neg (z : ℤ) (h : z < 0) : finalCell M x y coins z = blankS M := by
  unfold finalCell
  rw [if_neg (by omega)]
  exact startCell_out M x y z (Or.inl h)

theorem step2 (j : ℕ) (hj : j < 2 * n) (c : Bool) (cfg : Cf M) (h : Inv2 M x y coins j cfg) :
    ∃ cfg', TM.advance (rule M c) cfg = some cfg' ∧ Inv2 M x y coins (j + 1) cfg' := by
  obtain ⟨hpc, hpos, habs, opos, oabs, hoth⟩ := h
  have hread : (cfg.tape (some M.inputTape)).view 0 ≠ blankS M := by
    rw [view_zero, hpos, habs]
    exact finalCell_mid M x y coins _ (by omega) (by omega)
  refine ⟨⟨.inl true, fun i => (cfg.tape i).apply
      ((cfg.tape i).view 0, if i = some M.inputTape then .left else .stay)⟩, ?_, ?_⟩
  · simp only [TM.advance, hpc, rule, if_neg hread, Option.map_some]
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [if_true, pos_apply, hpos, TM.Move.shift]
      all_goals (try push_cast); all_goals (try ring)
    · intro z; rw [apply_same, habs]
    · simp only [reduceCtorEq, if_false, apply_stay_view, opos]
    · intro z; simp only [reduceCtorEq, if_false, apply_stay_view, oabs]
    · intro k hk
      have h1 : some k ≠ some M.inputTape := by simpa using hk
      simp only [if_neg h1, apply_stay_view, hoth k hk]

theorem phase2 (j : ℕ) (hj : j ≤ 2 * n) :
    ∃ cfg, run (machine M) coins (initial (machine M) x y) (n + 1 + j) = some cfg ∧
      Inv2 M x y coins j cfg := by
  induction j with
  | zero =>
    obtain ⟨cfg, hrun, hinv⟩ := phase1 M x y coins n le_rfl
    obtain ⟨cfg', hstep, hinv'⟩ := switch1 M x y coins cfg hinv
    refine ⟨cfg', ?_, hinv'⟩
    simp only [Nat.add_zero, run, hrun, Option.bind_some]
    exact hstep
  | succ j ih =>
    obtain ⟨cfg, hrun, hinv⟩ := ih (by omega)
    obtain ⟨cfg', hstep, hinv'⟩ := step2 M x y coins j (by omega) (coins (n + 1 + j)) cfg hinv
    refine ⟨cfg', ?_, hinv'⟩
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega]
    simp only [run, hrun, Option.bind_some]
    exact hstep

/-! ## Simulation of the decider -/

def Agrees (cfg : Cf M) (c : M.Cfg) : Prop :=
  cfg.pc = .inr c.q ∧ (∀ k i, (cfg.tape (some k)).view i = some ((c.tapes k).nth i)) ∧
  (cfg.tape none).pos = 2 * n ∧ ∀ z, (cfg.tape none).absolute z = outCell M (n := n) coins z

theorem update_some {T : TM.Tape (Sym M)} {y : Turing.Tape M.Γ}
    (eq : ∀ i, T.view i = some (y.nth i)) (w : M.Γ) (m : HeadMove) (i : ℤ) :
    (T.apply (some w, moveTM m)).view i = some ((m.apply (y.write w)).nth i) := by
  cases m <;> simp [TM.Tape.apply, TM.Move.shift, moveTM, HeadMove.apply, eq, sub_eq_add_neg] <;>
    split_ifs <;> rfl

theorem step_agrees {cfg : Cf M} {c : M.Cfg} (h : Agrees M (n := n) coins cfg c) (coin : Bool) :
    Option.Rel (Agrees M (n := n) coins) (TM.advance (rule M coin) cfg) (M.step c) := by
  obtain ⟨hpc, hview, opos, oabs⟩ := h
  have reads : (fun k => ((cfg.tape (some k)).view 0).getD default) = fun k => (c.tapes k).head := by
    funext k; rw [hview k 0]; simp
  simp only [TM.advance, hpc, rule, reads, FiniteMultiTapeMachine.step, multiTapeStep]
  cases hcode : M.code c.q (fun k => (c.tapes k).head) with
  | none => exact Option.Rel.none
  | some out =>
    simp only [Option.map_some]
    refine Option.Rel.some ⟨rfl, ?_, ?_, ?_⟩
    · intro k i
      exact update_some M (hview k) _ _ i
    · simp only [apply_stay_view, opos]
    · intro z; simp only [apply_stay_view, oabs]

theorem run_agrees (t₀ : ℕ) {cfg₀ : Cf M} {c₀ : M.Cfg}
    (h₀ : run (machine M) coins (initial (machine M) x y) t₀ = some cfg₀)
    (ag : Agrees M (n := n) coins cfg₀ c₀) (t : ℕ) :
    Option.Rel (Agrees M (n := n) coins) (run (machine M) coins (initial (machine M) x y) (t₀ + t))
      (runSteps M.step t (some c₀)) := by
  induction t with
  | zero => rw [Nat.add_zero, h₀]; exact Option.Rel.some ag
  | succ t ih =>
    rw [← Nat.add_assoc]
    simp only [run]
    unfold runSteps
    rw [Function.iterate_succ_apply']
    unfold runSteps at ih
    generalize run (machine M) coins (initial (machine M) x y) (t₀ + t) = A at ih ⊢
    generalize (fun oc => Option.bind oc M.step)^[t] (some c₀) = B at ih ⊢
    cases ih with
    | none => exact Option.Rel.none
    | some hag => exact step_agrees M (n := n) coins hag (coins (t₀ + t))


/-! ## The start of the simulation -/

theorem view_eq_absolute {A : Type} (T : TM.Tape A) (i : ℤ) : T.view i = T.absolute (T.pos + i) := by
  simp [TM.Tape.absolute]

theorem mk₁_nth_ofNat {Γ : Type} [Inhabited Γ] (l : List Γ) (m : ℕ) :
    (Turing.Tape.mk₁ l).nth (m : ℤ) = l[m]?.getD default := by
  change (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk l)).nth (m : ℤ) = _
  simp [List.getI_eq_getElem?_getD]

theorem mk₁_nth_negSucc {Γ : Type} [Inhabited Γ] (l : List Γ) (m : ℕ) :
    (Turing.Tape.mk₁ l).nth (Int.negSucc m) = default := by
  change (Turing.ListBlank.mk ([] : List Γ)).nth m = default
  simp

theorem mk₁_nil_nth {Γ : Type} [Inhabited Γ] (i : ℤ) : (Turing.Tape.mk₁ ([] : List Γ)).nth i = default := by
  rcases i with m | m
  · exact (mk₁_nth_ofNat [] m).trans (by simp)
  · exact mk₁_nth_negSucc [] m

theorem finalCell_eq_nth (i : ℤ) :
    finalCell M x y coins i = some ((Turing.Tape.mk₁
      ((List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val)).map M.inputSymbol)).nth i) := by
  rcases i with m | m
  · rw [show Int.ofNat m = (m : ℤ) from rfl, mk₁_nth_ofNat]
    unfold finalCell startCell
    by_cases h1 : m < n
    · have hx : 0 ≤ (m : ℤ) ∧ (m : ℤ).toNat < n := by omega
      rw [if_neg (by omega), dif_pos hx, List.map_append,
        List.getElem?_append_left (by simpa using h1)]
      simp [List.getElem?_map, List.getElem?_ofFn, h1, bitS]
    · by_cases h2 : m < 2 * n
      · rw [if_pos (by omega)]
        have h3 : ((List.ofFn x).map M.inputSymbol).length ≤ m := by simp; omega
        rw [List.map_append, List.getElem?_append_right h3]
        have h5 : m - ((List.ofFn x).map M.inputSymbol).length = m - n := by simp
        rw [h5]
        have h4 : m - n < n := by omega
        have h6 : ((m : ℤ) - n).toNat = m - n := by omega
        simp [List.getElem?_map, List.getElem?_ofFn, h4, bitS, h6]
      · have hx : ¬ (0 ≤ (m : ℤ) ∧ (m : ℤ).toNat < n) := by omega
        have hy : ¬ (0 ≤ (m : ℤ) - n ∧ ((m : ℤ) - n).toNat < n) := by omega
        rw [if_neg (by omega), dif_neg hx, dif_neg hy]
        have h3 : ((List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val)).map
            M.inputSymbol).length ≤ m := by simp; omega
        rw [List.getElem?_eq_none h3]
        rfl
  · rw [mk₁_nth_negSucc]
    unfold finalCell startCell
    have hx : ¬ (0 ≤ Int.negSucc m ∧ (Int.negSucc m).toNat < n) := by omega
    have hy : ¬ (0 ≤ Int.negSucc m - n ∧ (Int.negSucc m - n).toNat < n) := by omega
    rw [if_neg (by omega), dif_neg hx, dif_neg hy]
    rfl

theorem switch2 (c : Bool) (cfg : Cf M) (h : Inv2 M x y coins (2 * n) cfg) :
    ∃ cfg', TM.advance (rule M c) cfg = some cfg' ∧
      Agrees M (n := n) coins cfg' (M.init (List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val))) := by
  obtain ⟨hpc, hpos, habs, opos, oabs, hoth⟩ := h
  have hread : (cfg.tape (some M.inputTape)).view 0 = blankS M := by
    rw [view_zero, hpos, habs]
    exact finalCell_neg M x y coins _ (by push_cast; omega)
  refine ⟨⟨.inr M.initialState, fun i => (cfg.tape i).apply
      ((cfg.tape i).view 0, if i = some M.inputTape then .right else .stay)⟩, ?_, ?_⟩
  · simp only [TM.advance, hpc, rule, if_pos hread, Option.map_some]
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro k i
      by_cases hk : k = M.inputTape
      · subst hk
        simp only [if_true]
        rw [view_eq_absolute, apply_same, habs, pos_apply, hpos]
        have hz : 2 * (n : ℤ) - 1 - ((2 * n : ℕ) : ℤ) + TM.Move.shift .right + i = i := by
          simp only [TM.Move.shift]; push_cast; ring
        rw [hz, finalCell_eq_nth]
        simp [FiniteMultiTapeMachine.init]
      · have h1 : some k ≠ some M.inputTape := by simpa using hk
        simp only [if_neg h1, apply_stay_view, hoth k hk]
        simp [FiniteMultiTapeMachine.init, hk, bgTape, blankS, mk₁_nil_nth]
    · simp only [reduceCtorEq, if_false, apply_stay_view, opos]
    · intro z; simp only [reduceCtorEq, if_false, apply_stay_view, oabs]

/-- The whole prefix: guess, switch, rewind, switch. -/
theorem prefix_run :
    ∃ cfg₀, run (machine M) coins (initial (machine M) x y) (3 * n + 2) = some cfg₀ ∧
      Agrees M (n := n) coins cfg₀ (M.init (List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val))) := by
  obtain ⟨cfg, hrun, hinv⟩ := phase2 M x y coins (2 * n) le_rfl
  obtain ⟨cfg', hstep, hag⟩ := switch2 M x y coins (coins (n + 1 + 2 * n)) cfg hinv
  refine ⟨cfg', ?_, hag⟩
  rw [show 3 * n + 2 = (n + 1 + 2 * n) + 1 by omega]
  simp only [run, hrun, Option.bind_some]
  exact hstep

/-- Before the simulation the machine is in a guess or rewind state. -/
theorem prefix_states (t : ℕ) (ht : t < 3 * n + 2) :
    ∃ cfg, run (machine M) coins (initial (machine M) x y) t = some cfg ∧ ∃ b, cfg.pc = .inl b := by
  by_cases h1 : t ≤ n
  · obtain ⟨cfg, hrun, hinv⟩ := phase1 M x y coins t h1
    exact ⟨cfg, hrun, false, hinv.1⟩
  · obtain ⟨cfg, hrun, hinv⟩ := phase2 M x y coins (t - (n + 1)) (by omega)
    refine ⟨cfg, ?_, true, hinv.1⟩
    rw [show t = n + 1 + (t - (n + 1)) by omega]
    exact hrun

/-- Every accepting halt of the display machine is an accepting halt of the decider on
`(x, guessed word)`, and the output tape holds the guessed word. -/
theorem accepting_halt {t : ℕ} {cfg : Cf M} (c : Bool)
    (hrun : run (machine M) coins (initial (machine M) x y) t = some cfg)
    (hstop : TM.advance (rule M c) cfg = none) (hacc : (machine M).accepts cfg.pc = true) :
    3 * n + 2 ≤ t ∧ (∃ c' : M.Cfg, runSteps M.step (t - (3 * n + 2))
        (some (M.init (List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val)))) = some c' ∧
      M.step c' = none ∧ M.accept c'.q = true) ∧
    ∀ z, (cfg.tape none).absolute z = outCell M (n := n) coins z := by
  have ht : 3 * n + 2 ≤ t := by
    by_contra hlt
    obtain ⟨cfg₁, hrun₁, b, hpc⟩ := prefix_states M x y coins t (by omega)
    rw [hrun] at hrun₁
    obtain rfl := Option.some.inj hrun₁
    rw [hpc] at hacc
    exact Bool.false_ne_true hacc
  obtain ⟨cfg₀, hrun₀, hag₀⟩ := prefix_run M x y coins
  have rel := run_agrees M x y coins (3 * n + 2) hrun₀ hag₀ (t - (3 * n + 2))
  rw [show 3 * n + 2 + (t - (3 * n + 2)) = t by omega, hrun] at rel
  generalize hB : runSteps M.step (t - (3 * n + 2))
    (some (M.init (List.ofFn x ++ List.ofFn (fun j : Fin n => coins j.val)))) = B at rel
  cases rel with
  | some hag =>
    rename_i c'
    refine ⟨ht, ⟨c', rfl, ?_, ?_⟩, hag.2.2.2⟩
    · have r2 := step_agrees M (n := n) coins hag c
      rw [hstop] at r2
      generalize M.step c' = D at r2 ⊢
      cases r2
      rfl
    · obtain ⟨hpc, -⟩ := hag
      rw [hpc] at hacc
      exact hacc

end Phases

/-! ## Halting is unique -/

theorem runSteps_none_le {S : Type*} (step : S → Option S) (s : Option S) {k k' : ℕ}
    (h : runSteps step k s = none) (hk : k ≤ k') : runSteps step k' s = none := by
  induction hk with
  | refl => exact h
  | step _ ih =>
    unfold runSteps at ih ⊢
    rw [Function.iterate_succ_apply', ih]
    rfl

theorem halt_unique {S : Type*} (step : S → Option S) (s : Option S) {k k' : ℕ} {c c' : S}
    (h : runSteps step k s = some c) (hc : step c = none)
    (h' : runSteps step k' s = some c') (hc' : step c' = none) : c = c' := by
  have next : ∀ {j : ℕ} {d : S}, runSteps step j s = some d → step d = none →
      runSteps step (j + 1) s = none := by
    intro j d hj hd
    unfold runSteps at hj ⊢
    rw [Function.iterate_succ_apply', hj]
    simpa using hd
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · have h2 := runSteps_none_le step s (next h hc) hlt
    rw [h'] at h2
    exact absurd h2 (by simp)
  · rw [h] at h'
    exact Option.some.inj h'
  · have h2 := runSteps_none_le step s (next h' hc') hgt
    rw [h] at h2
    exact absurd h2 (by simp)

/-! ## Matrices from words -/

/-- The matrix whose row-major word is `w`. -/
def matOf {N : ℕ} (w : Word (N * N)) : Fin N → Fin N → Bool := fun r s => w (finProdFinEquiv (r, s))

theorem rowMajor_matOf {N : ℕ} (w : Word (N * N)) : rowMajor (matOf w) = List.ofFn w := by
  unfold rowMajor matOf
  congr 1
  funext j
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem transAnswer_matOf {N : ℕ} (x w : Word (N * N)) :
    transAnswer (matOf x) (matOf w) = true ↔ w = transposeWord x := by
  unfold transAnswer matOf transposeWord
  rw [decide_eq_true_iff]
  constructor
  · intro h
    funext j
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
    simpa using h i k
  · intro h i k
    rw [h]
    simp

/-! ## The display bound -/

/-- **Task G1' (open piece 1a) PROVED.** -/
theorem transDisplayBound : TransDisplayBound := by
  intro M
  refine ⟨machine M, 3, ?_⟩
  intro N T hdec x
  let y0 : Word (N * N) := fun _ => false
  -- the coin function of a seed, and the guessed word
  have key : ∀ (s : Fin (T + 3 * (N * N + 1) + 1) → Bool),
      let coins : ℕ → Bool := fun j => s ⟨min j (T + 3 * (N * N + 1)), Nat.lt_succ_of_le (min_le_right ..)⟩
      let w : Word (N * N) := fun j => coins j.val
      transEncode (matOf x) (matOf w) = List.ofFn x ++ List.ofFn (fun j : Fin (N * N) => coins j.val) := by
    intro s coins w
    unfold transEncode
    rw [rowMajor_matOf, rowMajor_matOf]
  constructor
  · -- existence: guess the transpose
    let s : Fin (T + 3 * (N * N + 1) + 1) → Bool := fun i =>
      if h : i.val < N * N then transposeWord x ⟨i.val, h⟩ else false
    refine ⟨s, ?_⟩
    let coins : ℕ → Bool := fun j => s ⟨min j (T + 3 * (N * N + 1)), Nat.lt_succ_of_le (min_le_right ..)⟩
    let w : Word (N * N) := fun j => coins j.val
    have hw : w = transposeWord x := by
      funext j
      have hj : min j.val (T + 3 * (N * N + 1)) = j.val := min_eq_left (by have := j.isLt; omega)
      simp only [w, coins, s, hj, dif_pos j.isLt]
    obtain ⟨k, hk, c', hrunM, hstopM, haccM⟩ := hdec (matOf x) (matOf w)
    rw [key s] at hrunM
    have hans : transAnswer (matOf x) (matOf w) = true := (transAnswer_matOf x w).mpr hw
    obtain ⟨cfg₀, hrun₀, hag₀⟩ := prefix_run M x y0 coins
    have rel := run_agrees M x y0 coins (3 * (N * N) + 2) hrun₀ hag₀ k
    rw [hrunM] at rel
    generalize hA : run (machine M) coins (initial (machine M) x y0) (3 * (N * N) + 2 + k) = A at rel
    cases rel with
    | some hag =>
      rename_i cfg
      have hle : 3 * (N * N) + 2 + k ≤ T + 3 * (N * N + 1) := by omega
      refine ⟨3 * (N * N) + 2 + k, hle, cfg, hA, ?_, ?_, ?_⟩
      · have r2 := step_agrees M (n := N * N) coins hag (s ⟨3 * (N * N) + 2 + k, Nat.lt_succ_of_le hle⟩)
        rw [hstopM] at r2
        show TM.advance (rule M (s ⟨3 * (N * N) + 2 + k, Nat.lt_succ_of_le hle⟩)) cfg = none
        cases hD : TM.advance (rule M (s ⟨3 * (N * N) + 2 + k, Nat.lt_succ_of_le hle⟩)) cfg with
        | none => rfl
        | some d => rw [hD] at r2; cases r2
      · obtain ⟨hpc, -⟩ := hag
        show (machine M).accepts cfg.pc = true
        rw [hpc]
        exact haccM.trans hans
      · intro i
        obtain ⟨-, -, -, oabs⟩ := hag
        have hi' : ((i.val : ℕ) : ℤ) < ((N * N : ℕ) : ℤ) := by exact_mod_cast i.isLt
        have hi0 : (0 : ℤ) ≤ ((i.val : ℕ) : ℤ) := Nat.cast_nonneg _
        have h1 := oabs (((N * N : ℕ) : ℤ) + (i.val : ℤ))
        unfold outCell at h1
        rw [if_pos ⟨by linarith, by linarith⟩] at h1
        have hi : (((N * N : ℕ) : ℤ) + (i.val : ℤ) - ((N * N : ℕ) : ℤ)).toNat = i.val := by
          rw [add_sub_cancel_left]; simp
        rw [hi] at h1
        rw [← hw]
        exact h1
  · -- uniqueness
    intro s out hout
    let coins : ℕ → Bool := fun j => s ⟨min j (T + 3 * (N * N + 1)), Nat.lt_succ_of_le (min_le_right ..)⟩
    let w : Word (N * N) := fun j => coins j.val
    obtain ⟨t, ht, cfg, hrun, hstop, hacc, hwrites⟩ := hout
    obtain ⟨-, ⟨c', hrunM', hstopM', haccM'⟩, oabs⟩ :=
      accepting_halt M x y0 coins (s ⟨t, Nat.lt_succ_of_le ht⟩) hrun hstop hacc
    obtain ⟨k, -, c'', hrunM, hstopM, haccM⟩ := hdec (matOf x) (matOf w)
    rw [key s] at hrunM
    have same := halt_unique M.step _ hrunM hstopM hrunM' hstopM'
    subst same
    have hans : transAnswer (matOf x) (matOf w) = true := haccM.symm.trans haccM'
    have hw := (transAnswer_matOf x w).mp hans
    rw [← hw]
    funext i
    have hi' : ((i.val : ℕ) : ℤ) < ((N * N : ℕ) : ℤ) := by exact_mod_cast i.isLt
    have hi0 : (0 : ℤ) ≤ ((i.val : ℕ) : ℤ) := Nat.cast_nonneg _
    have h2 := oabs (((N * N : ℕ) : ℤ) + (i.val : ℤ))
    have h3 : bitS M (out i) = outCell M (n := N * N) coins (((N * N : ℕ) : ℤ) + (i.val : ℤ)) :=
      (hwrites i).symm.trans h2
    unfold outCell at h3
    rw [if_pos ⟨by linarith, by linarith⟩] at h3
    have hi : (((N * N : ℕ) : ℤ) + (i.val : ℤ) - ((N * N : ℕ) : ℤ)).toNat = i.val := by
      rw [add_sub_cancel_left]; simp
    rw [hi] at h3
    exact bitS_injective M h3

end

end P1Case1.Display
