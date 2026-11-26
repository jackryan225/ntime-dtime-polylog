import P1Net.Network

/-!
# P4 (lane P1-lean-net): `contract_eq_count`

For every skeleton candidate `σ`, the contraction of the access network `net B σ` with the factors
`fac B σ L R` equals the number of guesses `w` such that the verifier accepts `input w` within `n B` steps
and the run has skeleton `σ` (paper `lem:pathcount`, verifier version).

Proof: an equivalence `{w good} ≃ {labellings with all factors one} × (unseen guess cells → Bool)`.
Forward: the run's local data (`run_valid`). Backward: a labelling with all factors one gives a `Valid`
family, hence (`valid_unique`) the run's own data; the guess is read off the initial-contents wires.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP NetworkKernel WireTensor
open scoped Classical

variable {M : FiniteMultiTapeMachine} {n : ℕ}

/-! ## Facts about windows and first accesses -/

theorem prevAccess_eq_none_iff {K : Type} (σ : Fin n → K → Fin 3) (k : K) (Z : ℤ) :
    ∀ i, prevAccess σ k Z i = none ↔ ∀ i' < i, ¬ InWindow (betaOf σ k i') Z := by
  intro i
  induction i with
  | zero => simp [prevAccess]
  | succ i ih =>
    simp only [prevAccess]
    split_ifs with hw
    · simp only [false_iff, not_forall, not_not]
      exact ⟨i, by omega, hw⟩
    · rw [ih]
      constructor
      · intro h i' hi'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | h'
        · exact h i' h'
        · subst h'; exact hw
      · intro h i' hi'; exact h i' (by omega)

theorem slot_inWindow {K : Type} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) (δ : Fin 3) :
    InWindow (betaOf σ k i) (slotBlock σ k i δ) := by
  have := δ.isLt
  simp only [InWindow, slotBlock]
  constructor <;> omega

theorem slotOf_slotBlock {K : Type} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) (δ : Fin 3) :
    slotOf σ k i (slotBlock σ k i δ) = δ := by
  simp only [slotOf, slotBlock]
  rw [show betaOf σ k i - 1 + (δ : ℤ) - betaOf σ k i + 1 = ((δ : ℕ) : ℤ) by ring]
  exact finOfInt_coe 3 δ

theorem slotBlock_slotOf {K : Type} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) (Z : ℤ)
    (h : InWindow (betaOf σ k i) Z) : slotBlock σ k i (slotOf σ k i Z) = Z := by
  simp only [InWindow] at h
  simp only [slotBlock, slotOf]
  rw [finOfInt_val 3 (by omega) (by push_cast; omega)]
  ring

variable {B : ℕ} [NeZero B]

/-- The run's final local data are accepting iff the run is halted and accepting at the end of the
interval. -/
theorem accepts_runOut (input : List Bool) (i : ℕ) :
    Accepts B (runOut (M := M) (B := B) input i) ↔
      Halted M (absRun M input ((i + 1) * B)) ∧ M.accept (absRun M input ((i + 1) * B)).q = true := by
  have hB : 0 < B := B_pos
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hb0 := beta_succ_bound (M := M) input hB i
  simp only [beta] at hb0
  set c := absRun M input (i * B)
  set c' := absRun M input ((i + 1) * B)
  have hheads : (fun k => (runOut (M := M) (B := B) input i).blocks k
      ((runOut (M := M) (B := B) input i).move k) ((runOut (M := M) (B := B) input i).off k)) =
      c'.heads := by
    funext k
    have hb := hb0 k
    have hmv : (((finOfInt 3 (c'.pos k / B - c.pos k / B + 1) : Fin 3) : ℕ) : ℤ) =
        c'.pos k / B - c.pos k / B + 1 := finOfInt_val 3 (by omega) (by push_cast; omega)
    have hof : (((finOfInt B (c'.pos k % B) : Fin B) : ℕ) : ℤ) = c'.pos k % B :=
      finOfInt_val B (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hB')
    simp only [runOut, localOut, AbsCfg.heads]
    rw [hmv, hof]
    congr 1
    have := Int.emod_add_ediv_mul (c'.pos k) B
    linarith
  simp only [Accepts, Halted, hheads]
  rfl

/-! ## Guesses and labellings -/

variable {g : ℕ} (L : GuessLayout M g) (σ : Fin n → M.K → Fin 3)

/-- The labelling of the network by the run on `input w`. -/
noncomputable def zOf (w : Fin g → Bool) : (e : CEdge M n ⊕ SEdge n) → netPayload M B n e
  | .inl c => (runIn (B := B) (L.input w) c.1).blocks c.2.1 c.2.2
  | .inr s => ((runOut (B := B) (L.input w) s.1).q, (runOut (B := B) (L.input w) s.1).off)

/-- A guess is good: the verifier accepts within `n B` steps and the run has skeleton `σ`. -/
def GoodW (w : Fin g → Bool) : Prop :=
  MultiTapeHaltsIn M (L.input w) true (n * B) ∧ skeleton M (L.input w) B n = σ

/-- A labelling is good: every site predicate holds. -/
def GoodZ (z : (e : (net B σ).Edge) → (net B σ).Payload e) : Prop :=
  ∀ u, siteOK B L u (edgeAssignment (net B σ).src (net B σ).dst z u)

/-- Inverse of the input symbol (only used on input symbols). -/
noncomputable def symInv (γ : M.Γ) : Bool := decide (γ = M.inputSymbol true)

theorem symInv_sym (b : Bool) : symInv (M := M) (M.inputSymbol b) = b := by
  cases b
  · simp only [symInv, decide_eq_false_iff_not]
    intro h
    exact Bool.false_ne_true (M.input_injective h)
  · simp [symInv]

/-- The first small interval whose window contains block `Z` of tape `k` (or `n`). -/
noncomputable def firstIdx (k : M.K) (Z : ℤ) : ℕ :=
  if h : ∃ i, i < n ∧ InWindow (betaOf σ k i) Z then Nat.find h else n

/-- Read guess bit `j` off the initial-contents wire of its block. -/
noncomputable def decode (z : (e : (net B σ).Edge) → (net B σ).Payload e) (j : Fin g) : Bool :=
  if h : firstIdx σ (L.cellOf j).1 ((L.cellOf j).2 / B) < n then
    symInv ((z (.inl (⟨_, h⟩, (L.cellOf j).1,
      slotOf σ (L.cellOf j).1 (firstIdx σ (L.cellOf j).1 ((L.cellOf j).2 / B)) ((L.cellOf j).2 / B))) :
        Fin B → M.Γ) (finOfInt B ((L.cellOf j).2 % B)))
  else false

/-- The guess of a labelling `z`, with the unseen guess cells given by `b`. -/
noncomputable def wOf (z : (e : (net B σ).Edge) → (net B σ).Payload e)
    (b : {j : Fin g // ¬ Seen B σ L j} → Bool) : Fin g → Bool :=
  fun j => if hs : Seen B σ L j then decode L σ z j else b ⟨j, hs⟩

/-! ## Forward: the run gives a labelling with all factors one -/

theorem ivIn_zOf (w : Fin g → Bool) (i : Fin n) :
    ivIn B i (edgeAssignment (net B σ).src (net B σ).dst (zOf (B := B) L w) (.inl i)) =
      runIn (L.input w) i := by
  obtain ⟨_ | j, hj⟩ := i
  · apply LocalIn.ext
    · simp [ivIn, stateIn, runIn, localIn, absRun, absInit, toAbs, FiniteMultiTapeMachine.init]
    · funext k
      simp [ivIn, stateIn, runIn, localIn, absRun, absInit, toAbs]
    · rfl
  · rfl

theorem goodZ_zOf {w : Fin g → Bool} (hw : GoodW (B := B) L σ w) : GoodZ L σ (zOf (B := B) L w) := by
  obtain ⟨hh, hs⟩ := hw
  subst hs
  have hv := run_valid (M := M) (B := B) (L.input w) n
  intro u
  rcases u with i | ⟨i, k, δ⟩
  · show ivOK B i _
    have hin := ivIn_zOf (B := B) L (skeleton M (L.input w) B n) w i
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hin, evolve_runIn]; exact hv.move i i.isLt
    · intro hi
      rw [hin, evolve_runIn]; rfl
    · rintro ⟨i2, k, δ⟩ he
      change (runIn (B := B) (L.input w) (i2 : ℕ)).blocks k δ = _
      rw [hin, evolve_runIn, run_wired (n := n) (L.input w) i2 (by omega) k δ]
      unfold wired
      simp only [netSrc] at he
      cases hp : prevAccess (skeleton M (L.input w) B n) k
          (slotBlock (skeleton M (L.input w) B n) k i2 δ) i2 with
      | none => rw [hp] at he; simp at he
      | some i' =>
        rw [hp] at he
        simp only [Sum.inl.injEq] at he
        obtain ⟨hlt, _⟩ := prevAccess_lt _ k _ i2 i' hp
        have : (i : ℕ) = i' := by rw [he, toFinLt_val _ hlt.le]
        simp only
        rw [this]
    · intro hlast
      rw [hin, evolve_runIn, accepts_runOut, show ((i : ℕ) + 1) * B = n * B by rw [hlast]]
      exact (haltsIn_iff _ _ _).1 hh
  · show initOK B L (i, k, δ) _
    intro he
    change PinOK B L k (slotBlock _ k i δ) ((runIn (B := B) (L.input w) (i : ℕ)).blocks k δ)
    simp only [netSrc] at he
    have hp : prevAccess (skeleton M (L.input w) B n) k
        (slotBlock (skeleton M (L.input w) B n) k i δ) i = none := by
      cases hp : prevAccess (skeleton M (L.input w) B n) k
          (slotBlock (skeleton M (L.input w) B n) k i δ) i with
      | none => rfl
      | some i' => rw [hp] at he; simp at he
    rw [run_wired (n := n) (L.input w) i (by omega) k δ]
    unfold wired
    rw [hp]
    intro o
    refine ⟨fun j hj => ⟨w j, L.init_some w k _ j hj⟩, fun hj => L.init_none w k _ hj⟩

/-! ## Backward: a labelling with all factors one is the run of a unique guess -/

theorem goodZ_iv {z : (e : (net B σ).Edge) → (net B σ).Payload e} (hz : GoodZ L σ z) (i : Fin n) :
    ivOK B i (edgeAssignment (net B σ).src (net B σ).dst z (.inl i)) := hz (.inl i)

theorem goodZ_init {z : (e : (net B σ).Edge) → (net B σ).Payload e} (hz : GoodZ L σ z) (c : CEdge M n) :
    initOK B L c (edgeAssignment (net B σ).src (net B σ).dst z (.inr c)) := hz (.inr c)

theorem ivIn_q_succ (j : ℕ) (hj : j + 1 < n) (h : (net B σ).Half (.inl ⟨j + 1, hj⟩)) :
    (ivIn B ⟨j + 1, hj⟩ h).q = (h.2 (.inr ⟨⟨j, by omega⟩, hj⟩) rfl).1 := rfl

theorem ivIn_off_succ (j : ℕ) (hj : j + 1 < n) (h : (net B σ).Half (.inl ⟨j + 1, hj⟩)) :
    (ivIn B ⟨j + 1, hj⟩ h).off = (h.2 (.inr ⟨⟨j, by omega⟩, hj⟩) rfl).2 := rfl

theorem ivIn_q_zero (hn : 0 < n) (h : (net B σ).Half (.inl ⟨0, hn⟩)) :
    (ivIn B ⟨0, hn⟩ h).q = M.initialState := rfl

theorem ivIn_off_zero (hn : 0 < n) (h : (net B σ).Half (.inl ⟨0, hn⟩)) :
    (ivIn B ⟨0, hn⟩ h).off = fun _ => finOfInt B 0 := rfl

variable [NeZero n]

/-- The last small interval. -/
def lastIdx : Fin n := ⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩

/-- The local data read from a labelling (small interval `min i (n - 1)`). -/
noncomputable def inpZ (z : (e : (net B σ).Edge) → (net B σ).Payload e) (i : ℕ) : LocalIn M B :=
  ivIn B (toFinLt lastIdx i) (edgeAssignment (net B σ).src (net B σ).dst z (.inl (toFinLt lastIdx i)))

theorem inpZ_eq (z : (e : (net B σ).Edge) → (net B σ).Payload e) (i : ℕ) (hi : i < n) :
    inpZ σ z i = ivIn B ⟨i, hi⟩ (edgeAssignment (net B σ).src (net B σ).dst z (.inl ⟨i, hi⟩)) := by
  have : toFinLt (lastIdx (n := n)) i = ⟨i, hi⟩ :=
    Fin.ext (toFinLt_val _ (by simp only [lastIdx]; omega))
  simp only [inpZ]
  rw [this]

theorem valid_of_goodZ {z : (e : (net B σ).Edge) → (net B σ).Payload e} (hz : GoodZ L σ z)
    (b : {j : Fin g // ¬ Seen B σ L j} → Bool) :
    Valid σ (L.input (wOf L σ z b)) (inpZ σ z) (fun i => evolve (inpZ σ z i)) where
  table _ _ := rfl
  move i hi := by
    rw [inpZ_eq σ z i hi]
    exact (goodZ_iv L σ hz ⟨i, hi⟩).1
  start_q hn := by rw [inpZ_eq σ z 0 hn]; rfl
  start_off hn := by rw [inpZ_eq σ z 0 hn]; rfl
  chain_q i hi := by
    rw [inpZ_eq σ z (i + 1) hi, inpZ_eq σ z i (by omega),
      ivIn_q_succ]
    exact congrArg Prod.fst ((goodZ_iv L σ hz ⟨i, by omega⟩).2.1 hi)
  chain_off i hi := by
    rw [inpZ_eq σ z (i + 1) hi, inpZ_eq σ z i (by omega),
      ivIn_off_succ]
    exact congrArg Prod.snd ((goodZ_iv L σ hz ⟨i, by omega⟩).2.1 hi)
  content i hi k δ := by
    have hB : 0 < B := B_pos
    rw [inpZ_eq σ z i hi]
    change (z (.inl (⟨i, hi⟩, k, δ)) : Fin B → M.Γ) = _
    unfold wired
    cases hp : prevAccess σ k (slotBlock σ k i δ) i with
    | some i' =>
      obtain ⟨hlt, _⟩ := prevAccess_lt σ k _ i i' hp
      simp only
      rw [inpZ_eq σ z i' (by omega)]
      have he : (Sum.inl ⟨i', by omega⟩ : Fin n ⊕ CEdge M n) = netSrc σ (.inl (⟨i, hi⟩, k, δ)) := by
        simp only [netSrc, hp, Sum.inl.injEq]
        exact Fin.ext (toFinLt_val _ hlt.le).symm
      exact (goodZ_iv L σ hz ⟨i', by omega⟩).2.2.1 (⟨i, hi⟩, k, δ) he
    | none =>
      simp only
      have he : (Sum.inr (⟨i, hi⟩, k, δ) : Fin n ⊕ CEdge M n) = netSrc σ (.inl (⟨i, hi⟩, k, δ)) := by
        simp only [netSrc, hp]
      have pin := goodZ_init L σ hz (⟨i, hi⟩, k, δ) he
      funext o
      have po := pin o
      change _ = (absRun M (L.input (wOf L σ z b)) 0).cells k (slotBlock σ k i δ * B + o)
      cases hg : L.guessAt k (slotBlock σ k i δ * B + o) with
      | none => rw [L.init_none _ _ _ hg]; exact po.2 hg
      | some j =>
        rw [L.init_some _ _ _ j hg]
        obtain ⟨bb, hbb0⟩ := po.1 j hg
        have hbb : (z (.inl (⟨i, hi⟩, k, δ)) : Fin B → M.Γ) o = M.inputSymbol bb := hbb0
        change (z (.inl (⟨i, hi⟩, k, δ)) : Fin B → M.Γ) o = _
        rw [hbb]
        congr 1
        set Z := slotBlock σ k i δ with hZdef
        have hB' : (0 : ℤ) < B := by exact_mod_cast hB
        have ho : ((o : ℕ) : ℤ) < B := by exact_mod_cast o.isLt
        have hc : L.cellOf j = (k, Z * B + o) := by
          obtain ⟨h1, h2⟩ := L.guessAt_inj _ _ _ _ j (L.guessAt_cellOf j) hg
          exact Prod.ext h1 h2
        have hdiv : (Z * B + o) / B = Z := ediv_eq_of_bounds hB' (by linarith) (by linarith)
        have hmod : (Z * B + o) % B = o := by
          rw [add_comm, Int.add_mul_emod_self_right]
          exact Int.emod_eq_of_lt (by positivity) ho
        have hwin : InWindow (betaOf σ k i) Z := slot_inWindow σ k i δ
        have hseen : Seen B σ L j := ⟨⟨i, hi⟩, δ, by rw [hc]; simp only; rw [hdiv]⟩
        have hfirst : firstIdx σ k Z = i := by
          have hex : ∃ i, i < n ∧ InWindow (betaOf σ k i) Z := ⟨i, hi, hwin⟩
          simp only [firstIdx, dif_pos hex]
          rw [Nat.find_eq_iff]
          exact ⟨⟨hi, hwin⟩, fun m hm hmw => (prevAccess_eq_none_iff σ k Z i).1 hp m hm hmw.2⟩
        simp only [wOf, dif_pos hseen, decode]
        rw [hc]
        simp only
        rw [hdiv, hmod, finOfInt_coe]
        rw [hfirst, dif_pos hi, hZdef, slotOf_slotBlock]
        change _ = symInv ((z (.inl (⟨i, hi⟩, k, δ)) : Fin B → M.Γ) o)
        rw [hbb, symInv_sym]

theorem back_goodW {z : (e : (net B σ).Edge) → (net B σ).Payload e} (hz : GoodZ L σ z)
    (b : {j : Fin g // ¬ Seen B σ L j} → Bool) :
    GoodW (B := B) L σ (wOf L σ z b) ∧ zOf (B := B) (n := n) L (wOf L σ z b) = z := by
  have hv := valid_of_goodZ L σ hz b
  obtain ⟨hs, hrun⟩ := valid_unique _ hv
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨⟨?_, hs.symm⟩, ?_⟩
  · have acc := (goodZ_iv L σ hz ⟨n - 1, by omega⟩).2.2.2 (by simp only; omega)
    rw [← inpZ_eq σ z (n - 1) (by omega)] at acc
    have hout := (hrun (n - 1) (by omega)).2
    try simp only at hout
    rw [hout, accepts_runOut, show n - 1 + 1 = n by omega] at acc
    exact (haltsIn_iff _ _ _).2 acc
  · funext e
    rcases e with ⟨i, k, δ⟩ | s
    · change (runIn (B := B) (L.input (wOf L σ z b)) (i : ℕ)).blocks k δ =
        (z (.inl (i, k, δ)) : Fin B → M.Γ)
      rw [← (hrun i i.isLt).1, inpZ_eq σ z i i.isLt]
      rfl
    · have key := (goodZ_iv L σ hz s.1).2.1 s.2
      have hout := (hrun s.1 s.1.isLt).2
      try simp only at hout
      rw [inpZ_eq σ z s.1 s.1.isLt] at hout
      change ((runOut (B := B) (L.input (wOf L σ z b)) (s.1 : ℕ)).q,
        (runOut (B := B) (L.input (wOf L σ z b)) (s.1 : ℕ)).off) = (z (.inr s) : M.Q × (M.K → Fin B))
      rw [← hout]
      exact key.symm

theorem wOf_zOf {w : Fin g → Bool} (hw : GoodW (B := B) L σ w) :
    wOf L σ (zOf (B := B) (n := n) L w) (fun j => w j) = w := by
  have hB : 0 < B := B_pos
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  obtain ⟨_, hs⟩ := hw
  funext j
  by_cases hseen : Seen B σ L j
  · simp only [wOf, dif_pos hseen]
    obtain ⟨i, δ, hZ⟩ := hseen
    have hwin : InWindow (betaOf σ (L.cellOf j).1 i) ((L.cellOf j).2 / B) := by
      rw [hZ]; exact slot_inWindow σ _ i δ
    have hex : ∃ i, i < n ∧ InWindow (betaOf σ (L.cellOf j).1 i) ((L.cellOf j).2 / B) :=
      ⟨i, i.isLt, hwin⟩
    have hi0 : Nat.find hex < n := (Nat.find_spec hex).1
    have hw0 : InWindow (betaOf σ (L.cellOf j).1 (Nat.find hex)) ((L.cellOf j).2 / B) :=
      (Nat.find_spec hex).2
    have hp0 : prevAccess σ (L.cellOf j).1 ((L.cellOf j).2 / B) (Nat.find hex) = none :=
      (prevAccess_eq_none_iff σ _ _ _).2 fun m hm hmw => Nat.find_min hex hm ⟨by omega, hmw⟩
    have hfirst : firstIdx σ (L.cellOf j).1 ((L.cellOf j).2 / B) = Nat.find hex := by
      simp only [firstIdx, dif_pos hex]
    have hcell : (L.cellOf j).2 / B * B + ((finOfInt B ((L.cellOf j).2 % B) : Fin B) : ℕ) =
        (L.cellOf j).2 := by
      rw [finOfInt_val B (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hB')]
      exact Int.ediv_mul_add_emod _ _
    unfold decode
    rw [hfirst, dif_pos hi0]
    change symInv ((runIn (B := B) (L.input w) (Nat.find hex)).blocks (L.cellOf j).1
      (slotOf σ (L.cellOf j).1 (Nat.find hex) ((L.cellOf j).2 / B))
      (finOfInt B ((L.cellOf j).2 % B))) = w j
    rw [run_wired (n := n) (L.input w) _ hi0.le, hs]
    unfold wired
    rw [slotBlock_slotOf σ _ _ _ hw0, hp0]
    change symInv ((absRun M (L.input w) 0).cells (L.cellOf j).1
      ((L.cellOf j).2 / B * B + ((finOfInt B ((L.cellOf j).2 % B) : Fin B) : ℕ))) = w j
    rw [hcell, L.init_some w _ _ j (L.guessAt_cellOf j), symInv_sym]
  · simp only [wOf, dif_neg hseen]

/-- The good guesses are the good labellings times free values on the unseen guess cells. -/
noncomputable def goodEquiv :
    {w : Fin g → Bool // GoodW (B := B) L σ w} ≃
      {z : (e : (net B σ).Edge) → (net B σ).Payload e // GoodZ L σ z} ×
        ({j : Fin g // ¬ Seen B σ L j} → Bool) where
  toFun w := (⟨zOf (B := B) (n := n) L w.1, goodZ_zOf L σ w.2⟩, fun j => w.1 j)
  invFun p := ⟨wOf L σ p.1.1 p.2, (back_goodW L σ p.1.2 p.2).1⟩
  left_inv w := Subtype.ext (wOf_zOf L σ w.2)
  right_inv p := by
    obtain ⟨⟨z, hz⟩, b⟩ := p
    refine Prod.ext (Subtype.ext (back_goodW L σ hz b).2) ?_
    funext j
    simp only [wOf, dif_neg j.2]

/-- **P4, `contract_eq_count`.** For every skeleton candidate `σ` (with `n > 0` small intervals of `B`
steps), the contraction of the access network with its factors is the number of guesses `w` such that the
verifier accepts `input w` within `n B` steps and the run on `input w` has skeleton `σ`. -/
theorem contract_eq_count (R : Type*) [CommRing R] :
    contract (net B σ) (fac B σ L R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
        MultiTapeHaltsIn M (L.input w) true (n * B) ∧ skeleton M (L.input w) B n = σ).card : R) := by
  rw [contract_net B σ L R]
  have hcard := Fintype.card_congr (goodEquiv (B := B) L σ)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype,
    Fintype.card_subtype] at hcard
  have hc : (Finset.univ.filter fun w : Fin g → Bool =>
      MultiTapeHaltsIn M (L.input w) true (n * B) ∧ skeleton M (L.input w) B n = σ).card =
      (Finset.univ.filter fun z : (e : (net B σ).Edge) → (net B σ).Payload e =>
        ∀ u, siteOK B L u (edgeAssignment (net B σ).src (net B σ).dst z u)).card *
        2 ^ unseenCount B σ L := by
    convert hcard using 3
    all_goals first | exact Iff.rfl | rfl | (ext z; simp [GoodZ]) | (simp [GoodW, GoodZ])
  rw [hc]
  push_cast
  ring

/-- Every run has exactly one skeleton: summing the counts over all skeleton candidates gives the number of
accepting guesses. -/
theorem sum_contract_eq_count (R : Type*) [CommRing R] :
    ∑ σ' : Fin n → M.K → Fin 3, contract (net B σ') (fac B σ' L R) =
      ((Finset.univ.filter fun w : Fin g → Bool => MultiTapeHaltsIn M (L.input w) true (n * B)).card :
        R) := by
  simp only [contract_eq_count]
  rw [← Nat.cast_sum]
  congr 1
  exact sum_card_skeleton _ _

/-! ## Ownership (for the routed network and the P8 check C14) -/

/-- In `g` small intervals the small block of a head (computed from `σ`) moves by at most `g`. -/
theorem betaOf_drift_dir {K : Type} (σ : Fin n → K → Fin 3) (k : K) (a : ℕ) :
    ∀ d : ℕ, betaOf σ k a - d ≤ betaOf σ k (a + d) ∧ betaOf σ k (a + d) ≤ betaOf σ k a + d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : betaOf σ k (a + d) - 1 ≤ betaOf σ k (a + d + 1) ∧
        betaOf σ k (a + d + 1) ≤ betaOf σ k (a + d) + 1 := by
      simp only [betaOf]
      split_ifs with h
      · have := (σ ⟨a + d, h⟩ k).isLt
        constructor <;> omega
      · constructor <;> omega
    rw [show a + (d + 1) = a + d + 1 by ring]
    push_cast
    constructor <;> omega

/-- Big interval `ι` (of `N` small intervals) owns the big blocks `q - 1, q, q + 1` of tape `k`, where `q` is the
big block of the head at its start: the directory entry `betaOf σ k (ι N) / N`. -/
def OwnsDir {K : Type} (τ : Fin n → K → Fin 3) (N ι : ℕ) (k : K) (Q : ℤ) : Prop :=
  ∃ δ : Fin 3, Q = betaOf τ k (ι * N) / N + δ - 1

/-- Guess cell `j` lies in a big block (of `N` small blocks) owned by one of the `I` big intervals. -/
def OwnedGuess (N I : ℕ) (j : Fin g) : Prop :=
  ∃ ι < I, OwnsDir σ N ι (L.cellOf j).1 ((L.cellOf j).2 / B / N)

/-- The number of guess cells in big blocks owned by no big interval: the exponent of the scalar of the
routed (ported) network. -/
noncomputable def unownedCount (N I : ℕ) : ℕ :=
  Fintype.card {j : Fin g // ¬ OwnedGuess (B := B) L σ N I j}

/-- **For P8 (check C14).** `unownedCount = 0` iff every guess cell lies in a big block `q - 1, q, q + 1`
around the directory entry `q = betaOf σ k (ι N) / N` of some big interval `ι < I`. -/
theorem unownedCount_eq_zero_iff (N I : ℕ) :
    unownedCount (B := B) L σ N I = 0 ↔
      ∀ j : Fin g, ∃ ι < I, ∃ δ : Fin 3,
        (L.cellOf j).2 / B / N = betaOf σ (L.cellOf j).1 (ι * N) / N + δ - 1 := by
  rw [unownedCount, Fintype.card_eq_zero_iff, isEmpty_subtype]
  simp only [not_not, OwnedGuess, OwnsDir]

/-- A guess cell in an accessed small block lies in an owned big block (paper `lem:own`, for `σ`). -/
theorem ownedGuess_of_seen {N I : ℕ} (hN : 0 < N) (hn : n = I * N) {j : Fin g} (hs : Seen B σ L j) :
    OwnedGuess (B := B) L σ N I j := by
  obtain ⟨i, δ, hZ⟩ := hs
  set k := (L.cellOf j).1
  set Z := (L.cellOf j).2 / B
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hi : (i : ℕ) = (i : ℕ) / N * N + (i : ℕ) % N := (Nat.div_add_mod' _ _).symm
  have hgN : (i : ℕ) % N < N := Nat.mod_lt _ hN
  have hιI : (i : ℕ) / N < I := by
    have h1 : (i : ℕ) < n := i.isLt
    have h2 : (i : ℕ) < N * I := by rw [Nat.mul_comm]; omega
    exact Nat.div_lt_of_lt_mul h2
  refine ⟨(i : ℕ) / N, hιI, ?_⟩
  set b0 := betaOf σ k ((i : ℕ) / N * N)
  have hd := betaOf_drift_dir σ k ((i : ℕ) / N * N) ((i : ℕ) % N)
  rw [← hi] at hd
  have hδ := δ.isLt
  have hZ' : Z = betaOf σ k i - 1 + (δ : ℤ) := hZ
  have a1 := ediv_mul_le' b0 hN'
  have a2 := lt_ediv_mul_add' b0 hN'
  have hg' : (((i : ℕ) % N : ℕ) : ℤ) + 1 ≤ N := by exact_mod_cast hgN
  have hlo : (b0 / N - 1) * N ≤ Z := by nlinarith
  have hhi : Z < (b0 / N + 2) * N := by nlinarith
  have q1 := ediv_mul_le' Z hN'
  have q2 := lt_ediv_mul_add' Z hN'
  have hq1 : b0 / N - 1 ≤ Z / N := by
    by_contra hc
    have : Z / N + 1 ≤ b0 / N - 1 := by omega
    nlinarith
  have hq2 : Z / N ≤ b0 / N + 1 := by
    by_contra hc
    have : b0 / N + 2 ≤ Z / N := by omega
    nlinarith
  refine ⟨finOfInt 3 (Z / N - b0 / N + 1), ?_⟩
  rw [finOfInt_val 3 (by omega) (by push_cast; omega)]
  ring

/-- `unownedCount ≤ unseenCount`: the routed network sums over more guess cells than the access network. -/
theorem unownedCount_le {N I : ℕ} (hN : 0 < N) (hn : n = I * N) :
    unownedCount (B := B) L σ N I ≤ unseenCount B σ L :=
  Fintype.card_subtype_mono _ _ fun _ h hs => h (ownedGuess_of_seen L σ hN hn hs)

/-! ## The verifier input `withGuess` as a `GuessLayout` -/

/-- The verifier's input (the text of `C1Challenge.withGuess`): each guess bit `b` as `true, b`, then
`false`, then `x`. -/
def guessWord (u x : List Bool) : List Bool := (u.flatMap fun b => [true, b]) ++ false :: x

theorem pair_length (u : List Bool) : (u.flatMap fun b => [true, b]).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [ih]; ring

theorem pair_getElem? (u : List Bool) (c : ℕ) :
    (u.flatMap fun b => [true, b])[c]? =
      if c < 2 * u.length then some (if c % 2 = 0 then true else u[c / 2]?.getD false) else none := by
  induction u generalizing c with
  | nil => simp
  | cons b u ih =>
    rcases c with _ | _ | c
    · simp
    · simp <;> omega
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem?_cons_succ, ih,
        List.length_cons]
      have h1 : (c + 1 + 1) % 2 = c % 2 := by omega
      have h2 : (c + 1 + 1) / 2 = c / 2 + 1 := by omega
      have h3 : (c + 1 + 1 < 2 * (u.length + 1)) ↔ c < 2 * u.length := by omega
      simp only [h1, h2, h3, List.getElem?_cons_succ]

theorem guessWord_getElem? (u x : List Bool) (c : ℕ) :
    (guessWord u x)[c]? =
      if c < 2 * u.length then some (if c % 2 = 0 then true else u[c / 2]?.getD false)
      else (false :: x)[c - 2 * u.length]? := by
  unfold guessWord
  by_cases hc : c < 2 * u.length
  · rw [List.getElem?_append_left (by rw [pair_length]; exact hc), pair_getElem?, if_pos hc, if_pos hc]
  · rw [List.getElem?_append_right (by rw [pair_length]; omega), pair_length, if_neg hc]

/-- The initial absolute configuration of input `l`: input symbols on cells `0, ..., |l| - 1` of the input
tape, blanks elsewhere. -/
theorem absInit_cells (l : List Bool) (k : M.K) (c : ℤ) :
    (absRun M l 0).cells k c =
      if k = M.inputTape ∧ 0 ≤ c then ((l[c.toNat]?).map M.inputSymbol).getD default else default := by
  simp only [absRun, Function.iterate_zero, id_eq, absInit, toAbs, FiniteMultiTapeMachine.init, sub_zero]
  by_cases hk : k = M.inputTape
  · simp only [if_pos hk, hk, true_and]
    rcases c with m | m
    · simp [Turing.Tape.mk₁, Turing.Tape.mk₂, List.getI_eq_getElem?_getD]
    · simp only [show ¬ (0 : ℤ) ≤ Int.negSucc m from by omega, if_false]
      rfl
  · have hc : ¬ (k = M.inputTape ∧ 0 ≤ c) := fun h => hk h.1
    rw [if_neg hc]
    simp only [if_neg hk]
    rcases c with m | m
    · simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
    · rfl

/-- Guess cells of `withGuess`: the cells `2 j + 1`, `j < g`, of the input tape. -/
def withGuessAt (g : ℕ) (k : M.K) (c : ℤ) : Option (Fin g) :=
  if h : k = M.inputTape ∧ 0 ≤ c ∧ c < 2 * g ∧ c % 2 = 1 then
    some ⟨(c / 2).toNat, by have := Int.toNat_of_nonneg (show 0 ≤ c / 2 by omega); omega⟩
  else none

theorem withGuessAt_eq_some {g : ℕ} {k : M.K} {c : ℤ} {j : Fin g} (h : withGuessAt g k c = some j) :
    k = M.inputTape ∧ c = 2 * (j : ℕ) + 1 := by
  unfold withGuessAt at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    subst h
    have := Int.toNat_of_nonneg (show 0 ≤ c / 2 by omega)
    exact ⟨hc.1, by simp only; omega⟩

/-- The input of a verifier on `withGuess (List.ofFn w) x`, as a `GuessLayout`. -/
noncomputable def withGuessLayout (x : List Bool) (g : ℕ) : GuessLayout M g where
  input w := guessWord (List.ofFn w) x
  guessAt := withGuessAt g
  base k c := (absRun M (guessWord (List.ofFn fun _ : Fin g => false) x) 0).cells k c
  init_some w k c j h := by
    obtain ⟨hk, hc⟩ := withGuessAt_eq_some h
    rw [absInit_cells, if_pos ⟨hk, by omega⟩, hc]
    have ht : (2 * ((j : ℕ) : ℤ) + 1).toNat = 2 * (j : ℕ) + 1 := by omega
    rw [ht, guessWord_getElem?, List.length_ofFn, if_pos (by omega)]
    have h1 : (2 * (j : ℕ) + 1) % 2 = 1 := by omega
    have h2 : (2 * (j : ℕ) + 1) / 2 = j := by omega
    simp [h1, h2, List.getElem?_ofFn]
  init_none w k c h := by
    rw [absInit_cells, absInit_cells]
    by_cases hkc : k = M.inputTape ∧ 0 ≤ c
    · rw [if_pos hkc, if_pos hkc]
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hkc.2
      simp only [Int.toNat_natCast]
      rw [guessWord_getElem?, guessWord_getElem?, List.length_ofFn, List.length_ofFn]
      by_cases hm : m < 2 * g
      · rw [if_pos hm, if_pos hm]
        have hev : m % 2 = 0 := by
          by_contra hodd
          have : withGuessAt g k (m : ℤ) ≠ none := by
            unfold withGuessAt
            rw [dif_pos ⟨hkc.1, by omega, by omega, by omega⟩]
            simp
          exact this h
        simp [hev]
      · rw [if_neg hm, if_neg hm]
    · rw [if_neg hkc, if_neg hkc]
  guessAt_inj k c k' c' j h h' := by
    obtain ⟨hk, hc⟩ := withGuessAt_eq_some h
    obtain ⟨hk', hc'⟩ := withGuessAt_eq_some h'
    exact ⟨hk.trans hk'.symm, hc.trans hc'.symm⟩
  cellOf j := (M.inputTape, 2 * (j : ℕ) + 1)
  guessAt_cellOf j := by
    show withGuessAt g M.inputTape (2 * ((j : ℕ) : ℤ) + 1) = some j
    unfold withGuessAt
    rw [dif_pos ⟨rfl, by omega, by omega, by omega⟩]
    congr 1
    apply Fin.ext
    simp only
    omega

/-- **P4 for the Challenge input.** With `input w = withGuess (List.ofFn w) x`. -/
theorem contract_eq_count_withGuess (x : List Bool) (g : ℕ) (σ : Fin n → M.K → Fin 3)
    (R : Type*) [CommRing R] :
    contract (net B σ) (fac B σ (withGuessLayout (M := M) x g) R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
        MultiTapeHaltsIn M (guessWord (List.ofFn w) x) true (n * B) ∧
          skeleton M (guessWord (List.ofFn w) x) B n = σ).card : R) :=
  contract_eq_count (withGuessLayout x g) σ R

end P1Net
