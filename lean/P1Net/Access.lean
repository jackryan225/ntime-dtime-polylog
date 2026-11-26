import P1Net.Skeleton

/-!
# P4 core (lane P1-lean-net): the content of a small block is the output of its previous access

For a skeleton candidate `σ` the windows of the small intervals are known (`betaOf`), hence for each tape and
small block `Z` the last earlier small interval whose window contains `Z` (`prevAccess`). This is the access
structure that the network `N_{x,σ}` (task P3) wires by routing.

* `block_eq_prev`: in the run, the content of block `Z` at the start of small interval `i` is the content
  right after its previous access, or the initial content if there was none.
* `Valid`: the constraints of the interval tables (`evolve`, skeleton entries), of the state chain, and of the
  content wiring by previous accesses, for one family of local data per small interval.
* `run_valid` and `valid_unique`: a family is valid for `σ` iff `σ` is the skeleton of the run and the family
  is the run's local data. So for each input there is exactly one valid family for its own skeleton and none
  for every other skeleton candidate (paper `lem:pathcount`, the step "the two maps are inverse").
-/

namespace P1Net

open OAI.DepthThreeLowerBound

variable {M : FiniteMultiTapeMachine}

/-- Contents of small block `Z` of tape `k` (cells `[Z B, Z B + B)`). -/
def blockOf (B : ℕ) (c : AbsCfg M) (k : M.K) (Z : ℤ) : Fin B → M.Γ := fun o => c.cells k (Z * B + o)

/-- Block `Z` lies in the window `β - 1, β, β + 1`. -/
def InWindow (β Z : ℤ) : Prop := β - 1 ≤ Z ∧ Z ≤ β + 1

instance (β Z : ℤ) : Decidable (InWindow β Z) := inferInstanceAs (Decidable (_ ∧ _))

/-- The last small interval `i' < i` whose window (for the skeleton candidate `σ`) contains block `Z`. -/
def prevAccess {K : Type} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (Z : ℤ) : ℕ → Option ℕ
  | 0 => none
  | i + 1 => if InWindow (betaOf σ k i) Z then some i else prevAccess σ k Z i

theorem prevAccess_lt {K : Type} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (Z : ℤ) :
    ∀ (i i' : ℕ), prevAccess σ k Z i = some i' → i' < i ∧ InWindow (betaOf σ k i') Z := by
  intro i
  induction i with
  | zero => intro i' h; simp [prevAccess] at h
  | succ i ih =>
    intro i' h
    simp only [prevAccess] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h; subst h; exact ⟨by omega, hw⟩
    · obtain ⟨h1, h2⟩ := ih i' h; exact ⟨by omega, h2⟩

/-- `betaOf σ k i` only depends on the entries of `σ` before `i`. -/
theorem betaOf_congr {K : Type} {n : ℕ} {σ σ' : Fin n → K → Fin 3} (k : K) :
    ∀ i : ℕ, (∀ j : Fin n, (j : ℕ) < i → σ j = σ' j) → betaOf σ k i = betaOf σ' k i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    simp only [betaOf]
    rw [ih (fun j hj => h j (by omega))]
    split_ifs with hi
    · rw [h ⟨i, hi⟩ (by simp)]
    · rfl

theorem prevAccess_congr {K : Type} {n : ℕ} {σ σ' : Fin n → K → Fin 3} (k : K) (Z : ℤ) :
    ∀ i : ℕ, (∀ j : Fin n, (j : ℕ) < i → σ j = σ' j) → prevAccess σ k Z i = prevAccess σ' k Z i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    simp only [prevAccess]
    rw [betaOf_congr k i (fun j hj => h j (by omega)), ih (fun j hj => h j (by omega))]

variable {B : ℕ} [NeZero B]

theorem B_pos : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)

/-- **Previous access.** In the run, the content of block `Z` at the start of small interval `i` is its
content right after its previous access, or its initial content. -/
theorem block_eq_prev (input : List Bool) {n : ℕ} (k : M.K) (Z : ℤ) :
    ∀ i ≤ n, blockOf B (absRun M input (i * B)) k Z =
      match prevAccess (skeleton M input B n) k Z i with
      | some i' => blockOf B (absRun M input ((i' + 1) * B)) k Z
      | none => blockOf B (absRun M input 0) k Z := by
  have hB : 0 < B := B_pos
  intro i
  induction i with
  | zero => intro _; simp [prevAccess]
  | succ i ih =>
    intro hi
    simp only [prevAccess]
    split_ifs with hw
    · rfl
    · rw [← ih (by omega)]
      have hrun : absRun M input ((i + 1) * B) = (absStep M)^[B] (absRun M input (i * B)) := by
        rw [← absRun_add]; congr 1; ring
      funext o
      simp only [blockOf]
      rw [hrun]
      apply cells_outside_interval _ hB
      have hβ : (absRun M input (i * B)).pos k / B = betaOf (skeleton M input B n) k i :=
        beta_eq_betaOf input hB k i (by omega)
      rw [hβ]
      have ho : ((o : ℕ) : ℤ) < B := by exact_mod_cast o.isLt
      have ho0 : (0 : ℤ) ≤ ((o : ℕ) : ℤ) := by positivity
      have hB' : (0 : ℤ) < B := by exact_mod_cast hB
      simp only [InWindow, not_and_or, not_le] at hw
      rcases hw with hw | hw
      · left
        have : Z ≤ betaOf (skeleton M input B n) k i - 2 := by omega
        nlinarith
      · right
        have : betaOf (skeleton M input B n) k i + 2 ≤ Z := by omega
        nlinarith

/-! ## Local data of the run and valid families -/

/-- The run's local data at the start of small interval `i`. -/
def runIn (input : List Bool) (i : ℕ) : LocalIn M B := localIn (absRun M input (i * B))

/-- The run's local data at the end of small interval `i`, read in the windows of interval `i`. -/
def runOut (input : List Bool) (i : ℕ) : LocalOut M B :=
  localOut (absRun M input (i * B)) (absRun M input ((i + 1) * B))

theorem evolve_runIn (input : List Bool) (i : ℕ) :
    evolve (runIn (M := M) (B := B) input i) = runOut input i := evolve_run input i

/-- The block of window slot `δ` at the start of small interval `i` (for the skeleton candidate `σ`). -/
def slotBlock {K : Type} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) (δ : Fin 3) : ℤ :=
  betaOf σ k i - 1 + (δ : ℤ)

/-- The window slot of block `Z` in small interval `i'`. -/
def slotOf {K : Type} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i' : ℕ) (Z : ℤ) : Fin 3 :=
  finOfInt 3 (Z - betaOf σ k i' + 1)

/-- Initial contents of block `Z` of tape `k`. -/
def initBlock (input : List Bool) (k : M.K) (Z : ℤ) : Fin B → M.Γ := blockOf B (absRun M input 0) k Z

/-- The input of window slot `δ` of small interval `i` prescribed by the wiring: the output of the previous
access of its block, or the initial contents. -/
def wired {n : ℕ} (σ : Fin n → M.K → Fin 3) (input : List Bool) (out : ℕ → LocalOut M B) (i : ℕ)
    (k : M.K) (δ : Fin 3) : Fin B → M.Γ :=
  match prevAccess σ k (slotBlock σ k i δ) i with
  | some i' => (out i').blocks k (slotOf σ k i' (slotBlock σ k i δ))
  | none => initBlock input k (slotBlock σ k i δ)

/-- The constraints of all interval tables, of the state chain and of the content wiring, for local data
`inp i`, `out i` of the small intervals `i < n` (values at `i ≥ n` are ignored). -/
structure Valid {n : ℕ} (σ : Fin n → M.K → Fin 3) (input : List Bool) (inp : ℕ → LocalIn M B)
    (out : ℕ → LocalOut M B) : Prop where
  table : ∀ i, i < n → out i = evolve (inp i)
  move : ∀ i (h : i < n), (out i).move = σ ⟨i, h⟩
  start_q : 0 < n → (inp 0).q = M.initialState
  start_off : 0 < n → (inp 0).off = fun _ => finOfInt B 0
  chain_q : ∀ i, i + 1 < n → (inp (i + 1)).q = (out i).q
  chain_off : ∀ i, i + 1 < n → (inp (i + 1)).off = (out i).off
  content : ∀ i, i < n → ∀ k δ, (inp i).blocks k δ = wired σ input out i k δ

theorem localIn_blocks (c : AbsCfg M) (k : M.K) (δ : Fin 3) :
    (localIn (B := B) c).blocks k δ = blockOf B c k (c.pos k / B - 1 + δ) := by
  funext o
  simp only [localIn, blockOf]
  congr 1
  ring

theorem localOut_blocks (c c' : AbsCfg M) (k : M.K) (δ : Fin 3) :
    (localOut (B := B) c c').blocks k δ = blockOf B c' k (c.pos k / B - 1 + δ) := by
  funext o
  simp only [localOut, blockOf]
  congr 1
  ring

/-- The run's local data satisfy the wiring constraints of its own skeleton. -/
theorem run_wired (input : List Bool) {n : ℕ} (i : ℕ) (hi : i ≤ n) (k : M.K) (δ : Fin 3) :
    (runIn (M := M) (B := B) input i).blocks k δ =
      wired (skeleton M input B n) input (runOut input) i k δ := by
  have hB : 0 < B := B_pos
  set σ := skeleton M input B n
  have hβ : ∀ j ≤ n, (absRun M input (j * B)).pos k / B = betaOf σ k j :=
    fun j hj => beta_eq_betaOf input hB k j hj
  rw [runIn, localIn_blocks, hβ i hi]
  have hZ : betaOf σ k i - 1 + (δ : ℤ) = slotBlock σ k i δ := rfl
  rw [hZ, block_eq_prev input k _ i hi]
  unfold wired
  cases hp : prevAccess σ k (slotBlock σ k i δ) i with
  | none => rfl
  | some i' =>
    simp only
    obtain ⟨hlt, hw⟩ := prevAccess_lt σ k _ i i' hp
    rw [runOut, localOut_blocks, hβ i' (by omega)]
    congr 1
    simp only [slotOf, InWindow] at hw ⊢
    rw [finOfInt_val 3 (by omega) (by push_cast; omega)]
    ring

/-- **Existence.** The run's local data form a valid family for the run's skeleton. -/
theorem run_valid (input : List Bool) (n : ℕ) :
    Valid (skeleton M input B n) input (runIn (M := M) (B := B) input) (runOut input) where
  table i _ := (evolve_runIn input i).symm
  move i h := by
    funext k
    rw [← evolve_runIn]
    exact evolve_run_move input ⟨i, h⟩ k
  start_q _ := by simp [runIn, localIn, absRun, absInit, toAbs, FiniteMultiTapeMachine.init]
  start_off _ := by
    funext k
    simp [runIn, localIn, absRun, absInit, toAbs]
  chain_q _ _ := rfl
  chain_off _ _ := rfl
  content i hi k δ := run_wired input i (by omega) k δ

/-- **Uniqueness.** A valid family for `σ` is the run's local data, and `σ` is the run's skeleton. -/
theorem valid_unique (input : List Bool) {n : ℕ} {σ : Fin n → M.K → Fin 3}
    {inp : ℕ → LocalIn M B} {out : ℕ → LocalOut M B} (hv : Valid σ input inp out) :
    σ = skeleton M input B n ∧ (∀ i, i < n → inp i = runIn input i ∧ out i = runOut input i) := by
  -- induction over small intervals in time order
  have key : ∀ i : ℕ, i ≤ n → ∀ j (hj : j < n), j < i →
      inp j = runIn input j ∧ out j = runOut input j ∧
        σ ⟨j, hj⟩ = skeleton M input B n ⟨j, hj⟩ := by
    intro i
    induction i with
    | zero => intro _ j _ hj; omega
    | succ i ih =>
      intro hi j hjn hj
      by_cases hji : j < i
      · exact ih (by omega) j hjn hji
      have hj' : j = i := by omega
      have hagree : ∀ j' : Fin n, (j' : ℕ) < j → σ j' = skeleton M input B n j' :=
        fun j' hj'' => (ih (by omega) j' j'.isLt (by omega)).2.2
      have hinp : inp j = runIn input j := by
        apply LocalIn.ext
        · -- state
          by_cases h0 : j = 0
          · rw [h0, hv.start_q (by omega)]
            simp [runIn, localIn, absRun, absInit, toAbs, FiniteMultiTapeMachine.init]
          · rw [show j = (j - 1) + 1 by omega, hv.chain_q (j - 1) (by omega),
              (ih (by omega) (j - 1) (by omega) (by omega)).2.1]
            rfl
        · -- offsets
          by_cases h0 : j = 0
          · rw [h0, hv.start_off (by omega)]
            funext k
            simp [runIn, localIn, absRun, absInit, toAbs]
          · rw [show j = (j - 1) + 1 by omega, hv.chain_off (j - 1) (by omega),
              (ih (by omega) (j - 1) (by omega) (by omega)).2.1]
            rfl
        · -- contents
          funext k δ
          rw [hv.content j hjn k δ, run_wired (B := B) (n := n) input j (by omega) k δ]
          unfold wired
          have hsl : slotBlock σ k j δ = slotBlock (skeleton M input B n) k j δ := by
            simp only [slotBlock]; rw [betaOf_congr k j hagree]
          rw [hsl, prevAccess_congr k _ j hagree]
          cases hp : prevAccess (skeleton M input B n) k (slotBlock (skeleton M input B n) k j δ) j with
          | none => rfl
          | some i' =>
            simp only
            obtain ⟨hlt, _⟩ := prevAccess_lt _ k _ j i' hp
            rw [(ih (by omega) i' (by omega) (by omega)).2.1]
            simp only [slotOf]
            rw [betaOf_congr k i' (fun j' hj'' => hagree j' (by omega))]
      have hout : out j = runOut input j := by rw [hv.table j hjn, hinp, evolve_runIn]
      refine ⟨hinp, hout, ?_⟩
      funext k
      rw [← hv.move j hjn, hout, ← evolve_runIn]
      exact evolve_run_move input ⟨j, hjn⟩ k
  refine ⟨funext fun j => (key n le_rfl j j.isLt j.isLt).2.2, fun j hj => ?_⟩
  exact ⟨(key n le_rfl j hj hj).1, (key n le_rfl j hj hj).2.1⟩

/-- **P4 core.** For every input, the valid families for `σ` are exactly the run's local data when `σ` is the
run's skeleton, and there are none otherwise. -/
theorem valid_iff (input : List Bool) {n : ℕ} (σ : Fin n → M.K → Fin 3) (inp : ℕ → LocalIn M B)
    (out : ℕ → LocalOut M B) :
    Valid σ input inp out ↔ σ = skeleton M input B n ∧
      ∀ i, i < n → inp i = runIn input i ∧ out i = runOut input i := by
  constructor
  · exact valid_unique input
  · rintro ⟨rfl, h⟩
    have hv := run_valid (M := M) (B := B) input n
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun hn => ?_, fun hn => ?_, fun i hi => ?_, fun i hi => ?_,
      fun i hi k δ => ?_⟩
    · rw [(h i hi).1, (h i hi).2]; exact hv.table i hi
    · rw [(h i hi).2]; exact hv.move i hi
    · rw [(h 0 hn).1]; exact hv.start_q hn
    · rw [(h 0 hn).1]; exact hv.start_off hn
    · rw [(h (i + 1) hi).1, (h i (by omega)).2]; exact hv.chain_q i hi
    · rw [(h (i + 1) hi).1, (h i (by omega)).2]; exact hv.chain_off i hi
    · rw [(h i hi).1, hv.content i hi k δ]
      unfold wired
      cases hp : prevAccess (skeleton M input B n) k (slotBlock (skeleton M input B n) k i δ) i with
      | none => rfl
      | some i' =>
        simp only
        obtain ⟨hlt, _⟩ := prevAccess_lt _ k _ i i' hp
        rw [(h i' (by omega)).2]

end P1Net
