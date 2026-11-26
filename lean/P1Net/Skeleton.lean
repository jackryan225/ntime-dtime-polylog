import OAI.Computability.DepthThree.Model

/-!
# P1 (lane P1-lean-net): the block-respecting skeleton of a deterministic multitape run

Task P1 of `research/g3/leanplan/PLAN.md` (paper `research/papers/ntime-dtime-polylog.tex`, subsection
"Normal form of M and skeletons" and `lem:own`; Astra's three-block tables, Lemma P proof section 2).

Model: OpenAI's `FiniteMultiTapeMachine` (two-way infinite tapes `Turing.Tape`). A `Turing.Tape` has no
absolute head position, so we follow the run in ABSOLUTE coordinates (`AbsCfg`: state, contents of every
tape indexed by `ℤ`, head positions), with the stationary continuation after halting (`absStep`).

Contents.
* `absRun_toAbs`, `haltsIn_iff`: the absolute run is the OpenAI run (`runSteps`), and
  `MultiTapeHaltsIn M input true τ ↔` the absolute run at time `τ` is halted and accepting.
* Blocks of `B` cells, small intervals of `B` steps: `beta` (small block of a head at the start of a small
  interval), `skeleton` (`Fin 3` = block change `+ 1`), `skeleton_val` (the change is in `{-1, 0, 1}`).
* `window_pos`: inside small interval `i` every head stays in the small blocks `β - 1, β, β + 1`.
* `own`: (paper `lem:own`) inside big interval `ι` (`N` small intervals) every window lies in the big blocks
  `q - 1, q, q + 1`, `q = ⌊β(ιN) / N⌋`.
* `evolve`: the `B`-step evolution of (state, in-block offsets, blocks `β - 1, β, β + 1` of every tape) is a
  function of these data: `evolve_localIn` holds for EVERY configuration; `cells_outside` says that cells
  outside the windows do not change.
-/

namespace P1Net

open OAI.DepthThreeLowerBound

/-! ## Small helpers -/

/-- Displacement of a head move. -/
def moveDelta : HeadMove → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem moveDelta_le (m : HeadMove) : moveDelta m ≤ 1 := by cases m <;> simp [moveDelta]

theorem neg_one_le_moveDelta (m : HeadMove) : -1 ≤ moveDelta m := by cases m <;> simp [moveDelta]

/-- `z` as an element of `Fin n` (exact when `0 ≤ z < n`). -/
def finOfInt (n : ℕ) [NeZero n] (z : ℤ) : Fin n :=
  ⟨z.toNat % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

theorem finOfInt_val (n : ℕ) [NeZero n] {z : ℤ} (h0 : 0 ≤ z) (h1 : z < n) :
    (((finOfInt n z : Fin n) : ℕ) : ℤ) = z := by
  have ht : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h0
  have hlt : z.toNat < n := by omega
  simp only [finOfInt, Nat.mod_eq_of_lt hlt, ht]

theorem finOfInt_coe (n : ℕ) [NeZero n] (a : Fin n) : finOfInt n (a : ℤ) = a := by
  apply Fin.ext
  have h := finOfInt_val n (z := ((a : ℕ) : ℤ)) (by omega) (by exact_mod_cast a.isLt)
  exact_mod_cast h

/-- Division by a positive block length: the quotient is determined by the bounds. -/
theorem ediv_eq_of_bounds {p q B : ℤ} (hB : 0 < B) (h1 : q * B ≤ p) (h2 : p < q * B + B) :
    p / B = q := by
  have h := (Int.ediv_emod_unique (a := p) (r := p - B * q) (q := q) hB).2
    ⟨by ring, by nlinarith, by nlinarith⟩
  exact h.1

theorem ediv_mul_le' (p : ℤ) {B : ℤ} (hB : 0 < B) : p / B * B ≤ p := Int.ediv_mul_le p (by omega)

theorem lt_ediv_mul_add' (p : ℤ) {B : ℤ} (hB : 0 < B) : p < p / B * B + B := by
  have := Int.lt_ediv_add_one_mul_self p hB
  linarith

/-- If two integers differ by at most `B`, their blocks differ by at most one. -/
theorem ediv_sub_bound {p p' B : ℤ} (hB : 0 < B) (h1 : p - B ≤ p') (h2 : p' ≤ p + B) :
    -1 ≤ p' / B - p / B ∧ p' / B - p / B ≤ 1 := by
  have a1 := ediv_mul_le' p hB
  have a2 := lt_ediv_mul_add' p hB
  have b1 := ediv_mul_le' p' hB
  have b2 := lt_ediv_mul_add' p' hB
  constructor
  · by_contra hc
    have : p' / B ≤ p / B - 2 := by omega
    have : p' / B * B ≤ (p / B - 2) * B := by nlinarith
    nlinarith
  · by_contra hc
    have : p / B + 2 ≤ p' / B := by omega
    have : (p / B + 2) * B ≤ p' / B * B := by nlinarith
    nlinarith

/-! ## Absolute configurations and the stationary run -/

/-- A configuration in absolute coordinates: control state, contents of every tape indexed by `ℤ`,
and the absolute head positions. -/
@[ext]
structure AbsCfg (M : FiniteMultiTapeMachine) where
  q : M.Q
  cells : M.K → ℤ → M.Γ
  pos : M.K → ℤ

namespace AbsCfg

variable {M : FiniteMultiTapeMachine}

/-- Symbols under the heads. -/
def heads (c : AbsCfg M) : M.K → M.Γ := fun k => c.cells k (c.pos k)

/-- Apply one transition output: write at the old head cells, then move the heads. -/
def update (c : AbsCfg M) (out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)) : AbsCfg M :=
  ⟨out.1, fun k j => if j = c.pos k then out.2.1 k else c.cells k j,
    fun k => c.pos k + moveDelta (out.2.2 k)⟩

end AbsCfg

variable (M : FiniteMultiTapeMachine)

/-- One step with stationary continuation: a halted configuration stays where it is. -/
def absStep (c : AbsCfg M) : AbsCfg M := ((M.code c.q c.heads).map c.update).getD c

/-- `c` is halted (the machine's code gives `none`). -/
def Halted (c : AbsCfg M) : Prop := M.code c.q c.heads = none

variable {M}

theorem absStep_of_none {c : AbsCfg M} (h : M.code c.q c.heads = none) : absStep M c = c := by
  simp [absStep, h]

theorem absStep_of_some {c : AbsCfg M} {out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)}
    (h : M.code c.q c.heads = some out) : absStep M c = c.update out := by
  simp [absStep, h]

theorem absStep_pos_le (c : AbsCfg M) (k : M.K) : (absStep M c).pos k ≤ c.pos k + 1 := by
  cases h : M.code c.q c.heads with
  | none => rw [absStep_of_none h]; omega
  | some out =>
    rw [absStep_of_some h]
    simp only [AbsCfg.update]
    have := moveDelta_le (out.2.2 k)
    omega

theorem absStep_pos_ge (c : AbsCfg M) (k : M.K) : c.pos k - 1 ≤ (absStep M c).pos k := by
  cases h : M.code c.q c.heads with
  | none => rw [absStep_of_none h]; omega
  | some out =>
    rw [absStep_of_some h]
    simp only [AbsCfg.update]
    have := neg_one_le_moveDelta (out.2.2 k)
    omega

/-- In `n` steps a head moves at most `n` cells. -/
theorem iterate_pos_bound (n : ℕ) (c : AbsCfg M) (k : M.K) :
    c.pos k - n ≤ ((absStep M)^[n] c).pos k ∧ ((absStep M)^[n] c).pos k ≤ c.pos k + n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih (absStep M c)
    have h2 := absStep_pos_le c k
    have h3 := absStep_pos_ge c k
    push_cast
    constructor <;> omega

/-- A halted configuration is a fixed point. -/
theorem iterate_halted {c : AbsCfg M} (h : Halted M c) (n : ℕ) : (absStep M)^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, absStep_of_none h]

/-! ## The absolute run is OpenAI's run -/

/-- The tape `T` with its head at the absolute cell `p`, read at the absolute cell `j`. -/
theorem nth_apply_write {Γ : Type} [Inhabited Γ] (m : HeadMove) (T : Turing.Tape Γ) (b : Γ)
    (p j : ℤ) :
    (m.apply (T.write b)).nth (j - (p + moveDelta m)) = if j = p then b else T.nth (j - p) := by
  have key : ∀ i : ℤ, i = j - p → (T.write b).nth i = if j = p then b else T.nth (j - p) := by
    intro i hi
    subst hi
    rw [Turing.Tape.write_nth]
    by_cases h : j = p
    · simp [h]
    · have h' : j - p ≠ 0 := sub_ne_zero.mpr h
      simp [h, h']
  cases m with
  | left =>
    show ((T.write b).move Turing.Dir.left).nth _ = _
    rw [Turing.Tape.move_left_nth]
    exact key _ (by simp only [moveDelta]; ring)
  | stay =>
    show (T.write b).nth _ = _
    exact key _ (by simp only [moveDelta]; ring)
  | right =>
    show ((T.write b).move Turing.Dir.right).nth _ = _
    rw [Turing.Tape.move_right_nth]
    exact key _ (by simp only [moveDelta]; ring)

variable (M)

/-- The absolute picture of an OpenAI configuration whose heads stand at the absolute cells `p`. -/
def toAbs (c : M.Cfg) (p : M.K → ℤ) : AbsCfg M :=
  ⟨c.q, fun k j => (c.tapes k).nth (j - p k), p⟩

/-- The absolute initial configuration (all heads at cell `0`). -/
def absInit (input : List Bool) : AbsCfg M := toAbs M (M.init input) (fun _ => 0)

/-- The absolute run with stationary continuation. -/
def absRun (input : List Bool) (n : ℕ) : AbsCfg M := (absStep M)^[n] (absInit M input)

variable {M}

theorem toAbs_heads (c : M.Cfg) (p : M.K → ℤ) :
    (toAbs M c p).heads = fun k => (c.tapes k).head := by
  funext k
  simp [toAbs, AbsCfg.heads]

theorem absStep_toAbs_some (c : M.Cfg) (p : M.K → ℤ) {out : M.Q × (M.K → M.Γ) × (M.K → HeadMove)}
    (h : M.code c.q (fun k => (c.tapes k).head) = some out) :
    absStep M (toAbs M c p) =
      toAbs M (multiTapeUpdate c out.1 out.2.1 out.2.2) (fun k => p k + moveDelta (out.2.2 k)) := by
  have h' : M.code (toAbs M c p).q (toAbs M c p).heads = some out := by
    rw [toAbs_heads]; exact h
  rw [absStep_of_some h']
  ext k j
  · rfl
  · simp only [AbsCfg.update, toAbs, multiTapeUpdate]
    exact (nth_apply_write (out.2.2 k) (c.tapes k) (out.2.1 k) (p k) j).symm
  · rfl

theorem step_eq_none_iff (c : M.Cfg) :
    M.step c = none ↔ M.code c.q (fun k => (c.tapes k).head) = none := by
  simp [FiniteMultiTapeMachine.step, multiTapeStep]

theorem halted_toAbs_iff (c : M.Cfg) (p : M.K → ℤ) : Halted M (toAbs M c p) ↔ M.step c = none := by
  rw [step_eq_none_iff, Halted, toAbs_heads]
  rfl

theorem runSteps_succ (input : List Bool) (n : ℕ) :
    runSteps M.step (n + 1) (some (M.init input)) =
      (runSteps M.step n (some (M.init input))).bind M.step := by
  simp only [runSteps]
  rw [Function.iterate_succ_apply']

/-- Where OpenAI's run is defined, the absolute run is its picture. -/
theorem absRun_toAbs (input : List Bool) :
    ∀ (n : ℕ) (c : M.Cfg), runSteps M.step n (some (M.init input)) = some c →
      ∃ p, absRun M input n = toAbs M c p := by
  intro n
  induction n with
  | zero =>
    intro c hc
    simp only [runSteps, Function.iterate_zero, id_eq, Option.some.injEq] at hc
    subst hc
    exact ⟨fun _ => 0, rfl⟩
  | succ n ih =>
    intro c' hc'
    rw [runSteps_succ] at hc'
    cases hr : runSteps M.step n (some (M.init input)) with
    | none => rw [hr] at hc'; simp at hc'
    | some c =>
      rw [hr] at hc'
      obtain ⟨p, hp⟩ := ih c hr
      simp only [Option.bind_some] at hc'
      cases hcode : M.code c.q (fun k => (c.tapes k).head) with
      | none =>
        have : M.step c = none := (step_eq_none_iff c).2 hcode
        rw [this] at hc'; simp at hc'
      | some out =>
        have hs : M.step c = some (multiTapeUpdate c out.1 out.2.1 out.2.2) := by
          simp [FiniteMultiTapeMachine.step, multiTapeStep, hcode]
        rw [hs, Option.some.injEq] at hc'
        subst hc'
        refine ⟨fun k => p k + moveDelta (out.2.2 k), ?_⟩
        simp only [absRun] at hp ⊢
        rw [Function.iterate_succ_apply', hp, absStep_toAbs_some c p hcode]

/-- Before the first halt, OpenAI's run is defined. -/
theorem runSteps_of_not_halted (input : List Bool) :
    ∀ n : ℕ, (∀ m < n, ¬ Halted M (absRun M input m)) →
      ∃ c, runSteps M.step n (some (M.init input)) = some c := by
  intro n
  induction n with
  | zero => intro _; exact ⟨M.init input, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc⟩ := ih (fun m hm => hn m (by omega))
    obtain ⟨p, hp⟩ := absRun_toAbs input n c hc
    have hnh : ¬ Halted M (absRun M input n) := hn n (by omega)
    rw [hp, halted_toAbs_iff] at hnh
    obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hnh
    refine ⟨c', ?_⟩
    rw [runSteps_succ, hc]
    simpa using hc'

/-- Once halted, the absolute run stays. -/
theorem absRun_stays {input : List Bool} {n : ℕ} (h : Halted M (absRun M input n)) (m : ℕ)
    (hm : n ≤ m) : absRun M input m = absRun M input n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [absRun]
  rw [add_comm, Function.iterate_add_apply]
  exact iterate_halted h d

/-- `V` halts within `τ` steps with answer `b` iff the absolute run at time `τ` is halted with answer
`b`. -/
theorem haltsIn_iff (input : List Bool) (b : Bool) (τ : ℕ) :
    MultiTapeHaltsIn M input b τ ↔
      Halted M (absRun M input τ) ∧ M.accept (absRun M input τ).q = b := by
  constructor
  · rintro ⟨k, hk, c, hc, hstep, hacc⟩
    obtain ⟨p, hp⟩ := absRun_toAbs input k c hc
    have hh : Halted M (absRun M input k) := by rw [hp, halted_toAbs_iff]; exact hstep
    rw [absRun_stays hh τ hk, hp]
    exact ⟨(halted_toAbs_iff c p).2 hstep, hacc⟩
  · rintro ⟨hh, hacc⟩
    classical
    have hex : ∃ n, Halted M (absRun M input n) := ⟨τ, hh⟩
    let k := Nat.find hex
    have hk : Halted M (absRun M input k) := Nat.find_spec hex
    have hkτ : k ≤ τ := Nat.find_min' hex hh
    obtain ⟨c, hc⟩ := runSteps_of_not_halted input k (fun m hm => Nat.find_min hex hm)
    obtain ⟨p, hp⟩ := absRun_toAbs input k c hc
    refine ⟨k, hkτ, c, hc, ?_, ?_⟩
    · rw [hp, halted_toAbs_iff] at hk; exact hk
    · rw [absRun_stays hk τ hkτ, hp] at hacc; exact hacc

/-! ## Blocks, small intervals and the skeleton -/

variable (M)

/-- Small block of the head of tape `k` at the start of small interval `i` (blocks of `B` cells,
small intervals of `B` steps). -/
def beta (input : List Bool) (B i : ℕ) (k : M.K) : ℤ := (absRun M input (i * B)).pos k / B

/-- The skeleton: entry `(i, k)` is the change of the small block of head `k` over small interval
`i`, plus one (an element of `Fin 3` = `{-1, 0, 1} + 1`). -/
def skeleton (input : List Bool) (B n : ℕ) : Fin n → M.K → Fin 3 :=
  fun i k => finOfInt 3 (beta M input B (i + 1) k - beta M input B i k + 1)

variable {M}

theorem absRun_add (input : List Bool) (n m : ℕ) :
    absRun M input (n + m) = (absStep M)^[m] (absRun M input n) := by
  simp only [absRun]
  rw [add_comm, Function.iterate_add_apply]

/-- Over one small interval the small block of a head changes by `-1`, `0` or `1`. -/
theorem beta_succ_bound (input : List Bool) {B : ℕ} (hB : 0 < B) (i : ℕ) (k : M.K) :
    -1 ≤ beta M input B (i + 1) k - beta M input B i k ∧
      beta M input B (i + 1) k - beta M input B i k ≤ 1 := by
  have hrun : absRun M input ((i + 1) * B) = (absStep M)^[B] (absRun M input (i * B)) := by
    rw [← absRun_add]; congr 1; ring
  have hb := iterate_pos_bound B (absRun M input (i * B)) k
  rw [← hrun] at hb
  exact ediv_sub_bound (by exact_mod_cast hB) hb.1 hb.2

/-- The skeleton entry is the block change plus one. -/
theorem skeleton_val (input : List Bool) {B n : ℕ} (hB : 0 < B) (i : Fin n) (k : M.K) :
    ((skeleton M input B n i k : ℕ) : ℤ) =
      beta M input B (i + 1) k - beta M input B i k + 1 := by
  have h := beta_succ_bound input hB i k
  exact finOfInt_val 3 (by omega) (by push_cast; omega)

/-- The small block of head `k` at the start of small interval `i`, computed from a skeleton candidate
`σ` (no move after the last small interval). -/
def betaOf {K : Type} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) : ℕ → ℤ
  | 0 => 0
  | i + 1 => betaOf σ k i + (if h : i < n then ((σ ⟨i, h⟩ k : ℕ) : ℤ) - 1 else 0)

/-- The block at the start of small interval `i` is computed from the skeleton. -/
theorem beta_eq_betaOf (input : List Bool) {B n : ℕ} (hB : 0 < B) (k : M.K) :
    ∀ i ≤ n, beta M input B i k = betaOf (skeleton M input B n) k i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [beta, absRun, absInit, toAbs, betaOf]
  | succ i ih =>
    intro hi
    have hv := skeleton_val (n := n) input hB ⟨i, by omega⟩ k
    simp only at hv
    simp only [betaOf, dif_pos (show i < n by omega)]
    rw [hv, ← ih (by omega)]
    ring

/-- Inside small interval `i` every head stays in the small blocks `β - 1, β, β + 1`. -/
theorem window_pos (input : List Bool) {B : ℕ} (hB : 0 < B) (i m : ℕ) (hm : m ≤ B) (k : M.K) :
    (beta M input B i k - 1) * B ≤ (absRun M input (i * B + m)).pos k ∧
      (absRun M input (i * B + m)).pos k < (beta M input B i k + 2) * B := by
  have hb := iterate_pos_bound m (absRun M input (i * B)) k
  rw [← absRun_add] at hb
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have a1 := ediv_mul_le' ((absRun M input (i * B)).pos k) hB'
  have a2 := lt_ediv_mul_add' ((absRun M input (i * B)).pos k) hB'
  have hm' : (m : ℤ) ≤ B := by exact_mod_cast hm
  simp only [beta]
  constructor <;> nlinarith

/-- Paper `lem:own`: inside big interval `ι` (small intervals `ιN, ..., ιN + N - 1`) the window of every
small interval lies in the big blocks `q - 1, q, q + 1`, `q = ⌊β(ιN) / N⌋`. -/
theorem own (input : List Bool) {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (ι g : ℕ) (hg : g < N)
    (k : M.K) :
    (beta M input B (ι * N) k / N - 1) * N ≤ beta M input B (ι * N + g) k - 1 ∧
      beta M input B (ι * N + g) k + 1 < (beta M input B (ι * N) k / N + 2) * N := by
  -- the block moves by at most one per small interval
  have hdrift : ∀ g' : ℕ, beta M input B (ι * N) k - g' ≤ beta M input B (ι * N + g') k ∧
      beta M input B (ι * N + g') k ≤ beta M input B (ι * N) k + g' := by
    intro g'
    induction g' with
    | zero => simp
    | succ g' ih =>
      have := beta_succ_bound input hB (ι * N + g') k
      rw [show ι * N + (g' + 1) = ι * N + g' + 1 by ring]
      push_cast
      constructor <;> omega
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  set b0 := beta M input B (ι * N) k
  have a1 := ediv_mul_le' b0 hN'
  have a2 := lt_ediv_mul_add' b0 hN'
  have hd := hdrift g
  have hg' : (g : ℤ) + 1 ≤ N := by exact_mod_cast hg
  constructor <;> nlinarith

/-! ## The `B`-step evolution is a function of the local data -/

variable (M)

/-- Local data at the start of a small interval: the state, the offsets of the heads inside their small
blocks, and for every tape the contents of the small blocks `β - 1, β, β + 1` (`Fin 3` index `δ + 1`). -/
@[ext]
structure LocalIn (B : ℕ) where
  q : M.Q
  off : M.K → Fin B
  blocks : M.K → Fin 3 → Fin B → M.Γ

/-- Local data at the end of a small interval: state, new offsets, the block change plus one of every
head, and the new contents of the same three small blocks of every tape. -/
@[ext]
structure LocalOut (B : ℕ) where
  q : M.Q
  off : M.K → Fin B
  move : M.K → Fin 3
  blocks : M.K → Fin 3 → Fin B → M.Γ

variable {M}

variable {B : ℕ} [NeZero B]

/-- The canonical configuration of local data: the window is the cells `[0, 3B)`, the heads stand at
`B + offset`, all other cells are blank. -/
def LocalIn.toAbs (d : LocalIn M B) : AbsCfg M :=
  ⟨d.q, fun k j => if 0 ≤ j ∧ j < 3 * B then d.blocks k (finOfInt 3 (j / B)) (finOfInt B (j % B))
    else default, fun k => B + (d.off k : ℤ)⟩

/-- The `B`-step evolution of local data (with the stationary continuation after halting). -/
def evolve (d : LocalIn M B) : LocalOut M B :=
  let c := (absStep M)^[B] d.toAbs
  ⟨c.q, fun k => finOfInt B (c.pos k % B), fun k => finOfInt 3 (c.pos k / B),
    fun k δ o => c.cells k ((δ : ℤ) * B + o)⟩

/-- The local data of a configuration (windows around the current small blocks of the heads). -/
def localIn (c : AbsCfg M) : LocalIn M B :=
  ⟨c.q, fun k => finOfInt B (c.pos k % B),
    fun k δ o => c.cells k ((c.pos k / B - 1) * B + (δ : ℤ) * B + o)⟩

/-- The local data of `c'`, read in the windows of `c`. -/
def localOut (c c' : AbsCfg M) : LocalOut M B :=
  ⟨c'.q, fun k => finOfInt B (c'.pos k % B), fun k => finOfInt 3 (c'.pos k / B - c.pos k / B + 1),
    fun k δ o => c'.cells k ((c.pos k / B - 1) * B + (δ : ℤ) * B + o)⟩

/-- `d` is the picture of `c` on the windows `[lo k, hi k)`, shifted by `s`. -/
structure WinAgree (c d : AbsCfg M) (s lo hi : M.K → ℤ) : Prop where
  q_eq : c.q = d.q
  pos_eq : ∀ k, c.pos k = d.pos k + s k
  cells_eq : ∀ k j, lo k ≤ j → j < hi k → c.cells k (j + s k) = d.cells k j

omit [NeZero B] in
theorem WinAgree.step {c d : AbsCfg M} {s lo hi : M.K → ℤ} (h : WinAgree c d s lo hi)
    (hin : ∀ k, lo k ≤ d.pos k ∧ d.pos k < hi k) :
    WinAgree (absStep M c) (absStep M d) s lo hi := by
  have hheads : c.heads = d.heads := by
    funext k
    simp only [AbsCfg.heads]
    rw [h.pos_eq k]
    exact h.cells_eq k _ (hin k).1 (hin k).2
  have hcode : M.code c.q c.heads = M.code d.q d.heads := by rw [h.q_eq, hheads]
  cases hd : M.code d.q d.heads with
  | none =>
    rw [absStep_of_none hd, absStep_of_none (hcode.trans hd)]
    exact h
  | some out =>
    rw [absStep_of_some hd, absStep_of_some (hcode.trans hd)]
    refine ⟨rfl, ?_, ?_⟩
    · intro k
      simp only [AbsCfg.update]
      rw [h.pos_eq k]
      ring
    · intro k j hlo hhi
      simp only [AbsCfg.update]
      have hiff : (j + s k = c.pos k) ↔ (j = d.pos k) := by
        rw [h.pos_eq k]; constructor <;> intro e <;> linarith
      by_cases hj : j = d.pos k
      · rw [if_pos (hiff.2 hj), if_pos hj]
      · rw [if_neg (fun e => hj (hiff.1 e)), if_neg hj]
        exact h.cells_eq k j hlo hhi

omit [NeZero B] in
theorem WinAgree.iterate (n : ℕ) {c d : AbsCfg M} {s lo hi : M.K → ℤ} (h : WinAgree c d s lo hi)
    (hslack : ∀ k, lo k + n ≤ d.pos k + 1 ∧ d.pos k + n ≤ hi k) :
    WinAgree ((absStep M)^[n] c) ((absStep M)^[n] d) s lo hi := by
  induction n generalizing c d with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih (h.step fun k => ?_)
    · intro k
      have h1 := absStep_pos_le d k
      have h2 := absStep_pos_ge d k
      have h3 := hslack k
      push_cast at h3
      constructor <;> omega
    · have h3 := hslack k
      push_cast at h3
      constructor <;> omega

omit [NeZero B] in
/-- Cells outside the windows do not change while the heads stay inside. -/
theorem cells_outside (n : ℕ) {c : AbsCfg M} {lo hi : M.K → ℤ}
    (hslack : ∀ k, lo k + n ≤ c.pos k + 1 ∧ c.pos k + n ≤ hi k) (k : M.K) (j : ℤ)
    (hj : j < lo k ∨ hi k ≤ j) : ((absStep M)^[n] c).cells k j = c.cells k j := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hstep : (absStep M c).cells k j = c.cells k j := by
      cases hc : M.code c.q c.heads with
      | none => rw [absStep_of_none hc]
      | some out =>
        rw [absStep_of_some hc]
        simp only [AbsCfg.update]
        have h3 := hslack k
        push_cast at h3
        rw [if_neg (by omega)]
    rw [ih, hstep]
    intro k'
    have h1 := absStep_pos_le c k'
    have h2 := absStep_pos_ge c k'
    have h3 := hslack k'
    push_cast at h3
    constructor <;> omega

/-- **P1, local evolution.** For EVERY configuration `c`, the local data after `B` steps (read in the
windows of `c`) are `evolve` of the local data of `c`. -/
theorem evolve_localIn (c : AbsCfg M) :
    evolve (localIn (B := B) c) = localOut c ((absStep M)^[B] c) := by
  have hB : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  set s : M.K → ℤ := fun k => (c.pos k / B - 1) * B with hs
  set d : AbsCfg M := (localIn (B := B) c).toAbs with hd
  -- offsets
  have hoff : ∀ k, (((finOfInt B (c.pos k % B) : Fin B) : ℕ) : ℤ) = c.pos k % B := fun k =>
    finOfInt_val B (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hB)
  have hdpos : ∀ k, d.pos k = B + c.pos k % B := by
    intro k; simp only [hd, LocalIn.toAbs, localIn]; rw [hoff k]
  have hagree : WinAgree c d s (fun _ => 0) (fun _ => 3 * B) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro k
      rw [hdpos k]
      have := Int.emod_add_ediv_mul (c.pos k) B
      simp only [hs]
      linarith
    · intro k j hlo hhi
      have hj3 : j / B < 3 := by
        rw [Int.ediv_lt_iff_lt_mul hB]; linarith
      have hj0 : 0 ≤ j / B := Int.ediv_nonneg hlo (by omega)
      have hq := finOfInt_val 3 hj0 (by exact_mod_cast hj3)
      have hr := finOfInt_val B (Int.emod_nonneg j (by omega)) (Int.emod_lt_of_pos j hB)
      simp only [hd, LocalIn.toAbs, localIn, if_pos (And.intro hlo hhi)]
      rw [hq, hr]
      congr 1
      have := Int.emod_add_ediv_mul j B
      simp only [hs]
      linarith
  have hslack : ∀ k, (fun _ => (0 : ℤ)) k + B ≤ d.pos k + 1 ∧ d.pos k + B ≤ (fun _ => 3 * (B : ℤ)) k := by
    intro k
    rw [hdpos k]
    have := Int.emod_nonneg (c.pos k) (by omega : (B : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos (c.pos k) hB
    constructor <;> simp only <;> omega
  have hfin := hagree.iterate B hslack
  set c' := (absStep M)^[B] c
  set d' := (absStep M)^[B] d
  -- the evolution reads `d'`
  show (⟨d'.q, fun k => finOfInt B (d'.pos k % B), fun k => finOfInt 3 (d'.pos k / B),
    fun k δ o => d'.cells k ((δ : ℤ) * B + o)⟩ : LocalOut M B) = localOut c c'
  have hBne : (B : ℤ) ≠ 0 := by omega
  ext k
  · exact hfin.q_eq.symm
  · simp only [localOut]
    rw [hfin.pos_eq k]
    simp only [hs]
    rw [Int.add_mul_emod_self_right]
  · simp only [localOut]
    rw [hfin.pos_eq k]
    simp only [hs]
    rw [Int.add_mul_ediv_right _ _ hBne]
    congr 1
    ring
  · rename_i δ o
    simp only [localOut]
    have hδ : ((δ : ℕ) : ℤ) < 3 := by exact_mod_cast δ.isLt
    have ho : ((o : ℕ) : ℤ) < B := by exact_mod_cast o.isLt
    have hlo : (0 : ℤ) ≤ (δ : ℤ) * B + o := by positivity
    have hhi : (δ : ℤ) * B + o < 3 * B := by nlinarith
    rw [← hfin.cells_eq k _ hlo hhi]
    congr 1
    simp only [hs]
    ring

omit [NeZero B] in
/-- Cells outside the three windows of a small interval do not change during it. -/
theorem cells_outside_interval (c : AbsCfg M) (hB : 0 < B) (k : M.K) (j : ℤ)
    (hj : j < (c.pos k / B - 1) * B ∨ (c.pos k / B + 2) * B ≤ j) :
    ((absStep M)^[B] c).cells k j = c.cells k j := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  apply cells_outside B (lo := fun k => (c.pos k / B - 1) * B) (hi := fun k => (c.pos k / B + 2) * B)
  · intro k'
    have a1 := ediv_mul_le' (c.pos k') hB'
    have a2 := lt_ediv_mul_add' (c.pos k') hB'
    exact ⟨by nlinarith, by nlinarith⟩
  · exact hj

/-- **P1 on the run.** The local data of small interval `i + 1` (in the windows of interval `i`) are
`evolve` of those of interval `i`; the block changes are the skeleton entries. -/
theorem evolve_run (input : List Bool) (i : ℕ) :
    evolve (localIn (B := B) (absRun M input (i * B))) =
      localOut (absRun M input (i * B)) (absRun M input ((i + 1) * B)) := by
  rw [evolve_localIn, ← absRun_add]
  congr 2
  ring

theorem evolve_run_move (input : List Bool) {n : ℕ} (i : Fin n) (k : M.K) :
    (evolve (localIn (B := B) (absRun M input (i * B)))).move k = skeleton M input B n i k := by
  rw [evolve_run]
  rfl

/-! ## Every run has exactly one skeleton -/

/-- Counting by skeletons: the accepting guesses are the disjoint union over skeletons `σ` of those
whose run has skeleton `σ`. -/
theorem sum_card_skeleton {W S : Type} [Fintype W] [Fintype S] [DecidableEq S] (P : W → Prop)
    [DecidablePred P] (sk : W → S) :
    ∑ σ : S, (Finset.univ.filter fun w => P w ∧ sk w = σ).card =
      (Finset.univ.filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := sk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.filter_filter]

end P1Net
