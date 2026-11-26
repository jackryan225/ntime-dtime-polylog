import P1Int.Records

/-!
Every execution node lies on a complete branch, so the branch shape and wire
bounds give a fitted panel at each level. The global position and payload
estimates bound the remaining record fields uniformly in the skeleton.
-/

namespace P1Int.SolRecfit

open Filter P1Wrap P1Wit P1Wit.SolSpace P1Wit.SolWitfill
open P1Int.P11
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel

noncomputable section

/-- A nonzero coefficient on the wire diagonal forces at least one summand. -/
private theorem stateStep_nonempty {R : Type*} [CommSemiring R] [Nontrivial R]
    {a g : ℕ} {X : State a g} (s : Step R X.network) : Nonempty s.Choice := by
  classical
  by_contra h
  let z : (e : X.network.Edge) → X.network.Payload e := fun _ _ => false
  have he := s.exact_eq (WireTensor.edgeAssignment X.network.src X.network.dst z)
  have hc : X.network.coeff (k := R) (WireTensor.edgeAssignment X.network.src X.network.dst z) = 1 := by
    change (∏ e : X.network.Edge, if z e = z e then (1 : R) else 0) = 1
    simp only [ite_true, Finset.prod_const_one]
  have hu : (Finset.univ : Finset s.Choice) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun i _ => h ⟨i⟩)
  rw [hu, Finset.sum_empty] at he
  exact one_ne_zero (hc.symm.trans he)

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
variable {R : Type*} [CommRing R] (κ : A.Entry → R) (hκ : A.IsSolution κ)

private theorem shrinkChoice_nonempty (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    Nonempty (A.shrinkPassAt κ hκ i h X).step.Choice := by
  subst n
  -- The selector type depends on widths and the template, so use the solution in the base field.
  obtain ⟨f, hf⟩ := A.exists_solution
  change Nonempty (X.ShrinkSelection A.shrink)
  have hn := stateStep_nonempty (A.shrinkPassAt f hf i rfl X).step
  change Nonempty (X.ShrinkSelection A.shrink) at hn
  exact hn

/-- Every reached nonterminal state has an admitted next choice. -/
private def LiveTree {R : Type*} [CommSemiring R] {b n : ℕ} :
    {a g : ℕ} → {X : State a g} → StateExecution R b n X → Prop
  | _, _, _, .done _ => True
  | _, _, _, .more p tail => Nonempty p.step.Choice ∧ ∀ i, LiveTree (tail i)

private theorem live_choices {R : Type*} [CommSemiring R] {a g b n : ℕ} {X : State a g}
    (E : StateExecution R b n X) (h : LiveTree E) : Nonempty E.Choices := by
  induction E with
  | done => exact ⟨()⟩
  | more p tail ih =>
    obtain ⟨⟨i⟩, htail⟩ := h
    obtain ⟨j⟩ := ih i (htail i)
    exact ⟨⟨i, j⟩⟩

private theorem live_bind {R : Type*} [CommSemiring R] {a g b n b' n' : ℕ} {X : State a g}
    (E : StateExecution R b n X) (next : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (h : LiveTree E) (hn : ∀ z, LiveTree (next z)) : LiveTree (E.bind next) := by
  induction E with
  | done => exact hn ()
  | more p tail ih =>
    exact ⟨h.1, fun i => ih i (fun z => next ⟨i, z⟩) (h.2 i) (fun z => hn ⟨i, z⟩)⟩

private def LiveProcedure {R : Type*} [CommSemiring R] {a b l d : ℕ} {μ : ℝ}
    (P : Procedure R a b l d μ) : Prop :=
  ∀ g n h X, LiveTree (P.run g n h X)

private theorem live_id (R : Type*) [CommSemiring R] (a : ℕ) : LiveProcedure (Procedure.id R a) := by
  intro g n h X
  have he : n = g := h.trans (Nat.zero_add g)
  subst g
  exact True.intro

private theorem live_seq {R : Type*} [CommSemiring R] {a b c l d l' d' : ℕ} {μ ν : ℝ}
    {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    (hP : LiveProcedure P) (hQ : LiveProcedure Q) : LiveProcedure (P.seq Q) := by
  intro g n h X
  exact live_bind _ _ (hP _ _ _ X) (fun z => hQ _ _ _ _)

private theorem live_reindex {R : Type*} [CommSemiring R] {a b l d a' b' l' d' : ℕ} {μ ν : ℝ}
    {P : Procedure R a b l d μ} (hP : LiveProcedure P) {ha : a = a'} {hb : b = b'}
    {hl : l = l'} {hd : d = d'} {hμ : μ = ν} : LiveProcedure (P.reindex ha hb hl hd hμ) := by
  subst a' b' l' d' ν
  exact hP

private theorem live_shrink (i : Fin S.steps) : LiveProcedure (A.shrinkProcedure κ hκ i) := by
  intro g n h X
  subst n
  exact ⟨shrinkChoice_nonempty A κ hκ i _ X, fun _ => True.intro⟩

private theorem live_refresh : LiveProcedure (A.refreshProcedure κ hκ) := by
  intro g n h X
  subst n
  obtain ⟨f, hf⟩ := A.exists_solution
  refine ⟨?_, fun _ => True.intro⟩
  exact stateStep_nonempty (Refresh.dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 A.refresh S.port_order S.degree_bounds.2
    (f ∘ Sum.inr) ((A.solution_iff f).mp hf).2).step

private theorem live_prefix (j : ℕ) (hj : j ≤ S.steps) :
    LiveProcedure (S.shrinkPrefix (A.shrinkProcedure κ hκ) j hj) := by
  induction j with
  | zero =>
    rw [BlockSchedule.shrinkPrefix]
    exact live_reindex (live_id R _)
  | succ j ih =>
    rw [BlockSchedule.shrinkPrefix]
    exact live_reindex (live_seq (ih _) (live_reindex (live_shrink A κ hκ ⟨j, hj⟩)))

private theorem live_block : LiveProcedure (A.procedure κ hκ) := by
  unfold BlockSchedule.Templates.procedure BlockSchedule.assembleBlock
  exact live_reindex (live_seq (live_reindex (live_prefix A κ hκ S.steps le_rfl)) (live_refresh A κ hκ))

private theorem live_repeat (g T n : ℕ) (h : n = T * S.laneBits + g) (X : State (S.degreeExponent 0) n) :
    LiveTree ((A.procedure κ hκ).repeatExecution g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa only [Nat.zero_mul, Nat.zero_add] using h
    subst g
    exact True.intro
  | succ T ih =>
    let E := (A.procedure κ hκ).run (T * S.laneBits + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact live_bind E _ (live_block A κ hκ _ _ _ X) (fun z => ih _ rfl (E.finalState z))

private theorem live_execute {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    LiveTree (A.execute κ hκ T hn X) :=
  live_repeat A κ hκ _ _ _ (Nat.add_sub_of_le hn).symm X

private def PathWidth {R : Type*} [CommSemiring R] {b n : ℕ} (M : ℕ) :
    {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) → E.Choices → Prop
  | _, _, _, .done X, _ => ∀ e, X.width e ≤ M
  | _, _, X, .more _ tail, z => (∀ e, X.width e ≤ M) ∧ PathWidth M (tail z.1) z.2

private theorem widths_of_payload {a g M : ℕ} (X : State a g)
    (h : ∀ e : X.network.Edge, Fintype.card (X.network.Payload e) ≤ 2 ^ M) :
    ∀ e, X.width e ≤ M := by
  intro e
  let e' : X.network.Edge := ((e.1.1, e.2), e.1.2)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
  exact (P1P5.card_payload X e').symm.trans_le (h e')

private theorem payloadLe_cast {R : Type*} {N N' Y : Network} (h : N = N')
    (C : TermChain R N' Y) (M : ℕ) :
    P1P5.ChainPayloadLe (h.symm ▸ C : TermChain R N Y) M ↔ P1P5.ChainPayloadLe C M := by
  cases h
  rfl

private theorem pathWidth_of_payload {R : Type*} [CommSemiring R] {a g b n M : ℕ}
    {X : State a g} (E : StateExecution R b n X) (rec : E.Records) (z : E.Choices)
    (h : P1P5.ChainPayloadLe (E.termChain rec z) M) : PathWidth M E z := by
  induction E with
  | done X => exact widths_of_payload X h
  | @more a g a' g' X p tail ih =>
    rw [StateExecution.termChain, P1P5.ChainPayloadLe] at h
    exact ⟨widths_of_payload X h.1, ih z.1 (rec.2 z.1) z.2
      ((payloadLe_cast (p.output_eq z.1) _ M).mp h.2)⟩

private def shapeRows (D : Dims) : List (ℕ × ℕ × ℕ) :=
  List.ofFn (fun l : Fin (D.top + 1) => ((D.lv l).bases, (D.lv l).slots, (D.lv l).lanes))

private theorem shapeRows_head {D : Dims} {start : ℕ} (hs : start ≤ D.top) :
    ((shapeRows D).drop start).head? =
      some ((D.lv start).bases, (D.lv start).slots, (D.lv start).lanes) := by
  simp only [shapeRows, List.head?_drop, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hs)]

private theorem shapeRows_length (D : Dims) (start : ℕ) :
    ((shapeRows D).drop start).length = D.top + 1 - start := by
  rw [List.length_drop, shapeRows, List.length_ofFn]

private theorem panel_of_shape (D : Dims)
    (hrows : ∀ l ≤ D.top, (D.lv l).bases ≤ 2 ^ D.bigW ∧
      (D.lv l).lanes ≤ 2 ^ (D.lv l).laneW ∧ (D.lv l).slots ≤ 2 ^ (D.lv l).slotW)
    {a g start M : ℕ} (X : State a g) (hs : start ≤ D.top) (hM : M < 2 ^ D.wW)
    (he : ((D.lv start).bases, (D.lv start).slots, (D.lv start).lanes) =
      (Fintype.card X.Base, 2 ^ a, 2 ^ g))
    (hw : ∀ e, X.width e ≤ M) : PanelFits D (D.lv start) X :=
  ⟨congrArg Prod.fst he, congrArg (fun x => x.2.2) he, congrArg (fun x => x.2.1) he,
    (hrows _ hs).1, (hrows _ hs).2.1, (hrows _ hs).2.2, fun e => (hw e).trans_lt hM⟩

private theorem stateShapes_length_pos {R : Type*} [CommRing R] {a g b n : ℕ} {X : State a g}
    (E : StateExecution R b n X) (z : E.Choices) : 0 < (stateShapes E z).length := by
  cases E <;> exact Nat.zero_lt_succ _

/-- Check the current row from a complete path and recurse with the suffix for each child. -/
private theorem execFits_of_paths {R : Type*} [CommRing R] {a g b n M : ℕ} {X : State a g}
    (D : Dims) (E : StateExecution R b n X) (hM : M < 2 ^ D.wW)
    (hrows : ∀ l ≤ D.top, (D.lv l).bases ≤ 2 ^ D.bigW ∧
      (D.lv l).lanes ≤ 2 ^ (D.lv l).laneW ∧ (D.lv l).slots ≤ 2 ^ (D.lv l).slotW)
    (live : LiveTree E) (start : ℕ)
    (hshape : ∀ z, (shapeRows D).drop start = stateShapes E z)
    (hwidth : ∀ z, PathWidth M E z) : ExecFits D E start := by
  induction E generalizing start with
  | done X =>
    have he : (shapeRows D).drop start = [(Fintype.card X.Base, 2 ^ b, 2 ^ n)] := hshape ()
    have hlen := congrArg List.length he
    rw [shapeRows_length, List.length_singleton] at hlen
    have hs : start = D.top := by omega
    have hh := (shapeRows_head hs.le).symm.trans (congrArg List.head? he)
    exact ⟨hs, panel_of_shape D hrows X hs.le hM (Option.some.inj hh) (hwidth ())⟩
  | @more a g a' g' X p tail ih =>
    obtain ⟨z⟩ := live_choices (.more p tail) live
    let head := (Fintype.card X.Base, 2 ^ a, 2 ^ g)
    have he (i : p.step.Choice) (j : (tail i).Choices) :
        (shapeRows D).drop start = head :: stateShapes (tail i) j := hshape ⟨i, j⟩
    have hlen := congrArg List.length (he z.1 z.2)
    rw [shapeRows_length, List.length_cons] at hlen
    have hpos := stateShapes_length_pos (tail z.1) z.2
    have hs : start < D.top := by omega
    have hh := (shapeRows_head hs.le).symm.trans (congrArg List.head? (he z.1 z.2))
    refine ⟨hs, panel_of_shape D hrows X hs.le hM (Option.some.inj hh) (hwidth z).1, ?_⟩
    intro i
    refine ih i (live.2 i) (start + 1) (fun j => ?_) (fun j => (hwidth ⟨i, j⟩).2)
    simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using congrArg (List.drop 1) (he i j)

private theorem panelPrefix_le {a g : ℕ} {D : Dims} {L : LevelDims} {X : State a g}
    (h : PanelFits D L X) {j : ℕ} (hj : j ≤ L.bases * L.lanes * L.slots) :
    widthPrefix (finValue h.wireWidth) j ≤ X.totalWidth := by
  let m := L.bases * L.lanes * L.slots
  have hmono : widthPrefix (finValue h.wireWidth) j ≤ widthPrefix (finValue h.wireWidth) m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj) (fun _ _ _ => Nat.zero_le _)
  refine hmono.trans_eq ?_
  rw [widthPrefix, ← Fin.sum_univ_eq_sum_range]
  simp only [finValue_fin]
  let arcCoords : X.network.Edge ≃ (X.Base × Fin (2 ^ a)) × BitWord g :=
    { toFun := fun e => ((e.1.1, e.2), e.1.2)
      invFun := fun e => ((e.1.1, e.2), e.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.sum_comp (h.arc.trans arcCoords) X.width)

open private layoutRows runPhases layoutRows_form from P1Wit.SpaceFacts in
private theorem rowPowers {V : FiniteMultiTapeMachine} {K : Consts}
    (aM t g d bigBias termBias ℓ : ℕ) :
    let L := (genuineDims A K V aM t g d bigBias termBias).lv ℓ
    L.lanes = 2 ^ L.laneW ∧ L.slots = 2 ^ L.slotW := by
  unfold genuineDims
  dsimp only
  cases he : (layoutRows S
      (initialPositions V aM t) (Params.h t)
      (runPhases S (Params.T K t)))[ℓ]? with
  | none => exact ⟨rfl, rfl⟩
  | some L =>
    obtain ⟨a, lane, P, shrink, rfl⟩ := layoutRows_form
      S _ _ _ L (List.mem_of_getElem? he)
    exact ⟨rfl, rfl⟩

/-- The position and payload bounds fit even at zero big-field bias. -/
private theorem eventually_big (c : ℕ) :
    ∀ᶠ t in atTop, c * t * (Params.p t + 1) < 2 ^ (6 * Params.lam t) := by
  filter_upwards [Params.eventually_of_p (Params.eventually_mul_pow_lt_two_pow (2 * c) 1),
    Params.eventually_of_p (eventually_ge_atTop 1), eventually_ge_atTop 2] with t hc hp ht
  rw [pow_one] at hc
  have hlin : c * (Params.p t + 1) ≤ 2 * c * Params.p t := by
    calc
      _ ≤ c * (2 * Params.p t) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  calc
    c * t * (Params.p t + 1) = (c * (Params.p t + 1)) * t := by ring
    _ < 2 ^ Params.p t * t := Nat.mul_lt_mul_of_pos_right (hlin.trans_lt hc) (by omega)
    _ ≤ 2 ^ Params.lam t * 2 ^ Params.lam t :=
      Nat.mul_le_mul ((Params.two_pow_p_le ht).trans (Params.lt_two_pow' _).le)
        (Params.t_le_two_pow_lam t)
    _ = 2 ^ (Params.lam t + Params.lam t) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

private theorem zigzag_beta_le {J : Type} [Fintype J] [DecidableEq J] {m : ℕ} (σ : Fin m → J → Fin 3) (j : J) (r : ℕ) :
    zigzag (P1Net.betaOf σ j r) ≤ 2 * r := by
  have h := P1Net.betaOf_drift σ j 0 r
  simp only [P1Net.betaOf, zero_add, zero_sub] at h
  generalize P1Net.betaOf σ j r = z at h ⊢
  cases z with
  | ofNat z =>
    have hz : (z : ℤ) ≤ (r : ℤ) := h.2
    change 2 * z ≤ 2 * r
    exact Nat.mul_le_mul_left _ (by exact_mod_cast hz)
  | negSucc z =>
    have hz : -(r : ℤ) ≤ -((z + 1 : ℕ) : ℤ) := h.1
    have hn : z + 1 ≤ r := by exact_mod_cast (neg_le_neg_iff.mp hz)
    change 2 * z + 1 ≤ 2 * r
    omega

private theorem smallWidth_pos (termBias T W : ℕ) : 0 < smallWidth A termBias T W := by
  have hC : 0 < A.growthConstant := (by decide : 0 < 2).trans_le A.growthConstant_ge_two
  have hm : 0 < A.growthConstant ^ T * (W + 1) := Nat.mul_pos (pow_pos hC T) (Nat.succ_pos W)
  have hl := Nat.clog_pos (by decide : 1 < 2) (Nat.succ_le_succ hm)
  exact hl.trans_le (Nat.le_add_left _ _)

private theorem fixedFits {F : Type} [CommRing F] [Algebra (ZMod 2) F]
    (κ : A.Entry → F) (hκ : A.IsSolution κ) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) :
    ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → RecordsFitStmt A κ hκ V a b x d bigBias termBias := by
  classical
  let K := portConsts A
  let ha := four_le_baseDegree S
  obtain ⟨C, hC⟩ := genuine_spaceIn A κ hκ K (toOAI V) 1 le_rfl (portConsts_b0 A)
    (portConsts_C2 A) ha d bigBias termBias
  filter_upwards [(tendsto_lpTime a b).eventually hC,
    (tendsto_lpTime a b).eventually (Params.eventually_Ib 1 le_rfl),
    (tendsto_lpTime a b).eventually (eventually_big (8 + 4 * C))] with n hn hIb hbig
  intro x hx
  subst n
  let t := lpTime a b x.length
  let g := a * (x.length ^ 2 + 1)
  let D := fixedDims A V a b x d bigBias termBias
  let hnLane := lane_bound K S.laneBits (portConsts_b0 A) t
  have hg : 2 * g ≤ t := by dsimp [t, g, lpTime]; omega
  have hI : D.I = Params.I 1 t := rfl
  have hN : D.N = 2 ^ Params.h t := rfl
  have hIN : D.I * D.N ≤ 4 * t := by
    have h := hIb.2
    change Params.I 1 t * Params.bb t ≤ 4 * 1 * t at h
    calc
      D.I * D.N ≤ D.I * D.N * Params.B t := Nat.le_mul_of_pos_right _ (Params.B_pos _)
      _ = Params.I 1 t * Params.bb t := by rw [hI, hN, Params.bb, Params.N]; ring
      _ ≤ 4 * t := by simpa only [Nat.mul_one] using h
  have hcapacity : (8 + 4 * C) * t * (Params.p t + 1) < 2 ^ D.bigW :=
    hbig.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have hs (σ : RoutedSkeleton V (Params.I 1 t) (Params.h t)) (ι : (fixedExec A κ hκ V a b x σ).Choices) :
      SpaceIn K 1 C t D ((fixedExec A κ hκ V a b x σ).finalState ι).totalWidth :=
    hn g hg σ ι
  have hrows (σ : RoutedSkeleton V (Params.I 1 t) (Params.h t)) (ι : (fixedExec A κ hκ V a b x σ).Choices)
      (l : ℕ) (hl : l ≤ D.top) :
      (D.lv l).bases ≤ 2 ^ D.bigW ∧ (D.lv l).lanes ≤ 2 ^ (D.lv l).laneW ∧
        (D.lv l).slots ≤ 2 ^ (D.lv l).slotW := by
    obtain ⟨hlane, hslot⟩ := rowPowers (V := toOAI V) (K := K) A 1 t g d bigBias termBias l
    have hle := Finset.single_le_sum (f := fun l => (D.lv l).bases * (D.lv l).lanes)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    have hpos : 0 < (D.lv l).lanes := hlane ▸ Nat.two_pow_pos _
    refine ⟨?_, hlane.le, hslot.le⟩
    calc
      (D.lv l).bases ≤ (D.lv l).bases * (D.lv l).lanes := Nat.le_mul_of_pos_right _ hpos
      _ ≤ _ := hle
      _ ≤ C * D.I * D.N * (Params.p t + 1) := (hs σ ι).pos_le
      _ = C * (D.I * D.N) * (Params.p t + 1) := by ring
      _ ≤ C * (4 * t) * (Params.p t + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hIN)
      _ = (4 * C) * t * (Params.p t + 1) := by ring
      _ ≤ (8 + 4 * C) * t * (Params.p t + 1) := by gcongr; omega
      _ ≤ _ := hcapacity.le
  have hsmallCap : 8 * t ≤ (8 + 4 * C) * t * (Params.p t + 1) :=
    (Nat.mul_le_mul_right _ (Nat.le_add_right 8 (4 * C))).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  refine ⟨hI, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ i j
    exact (zigzag_beta_le _ j (i.val * D.N)).trans_lt
      ((show 2 * (i.val * D.N) ≤ 8 * t from
        (Nat.mul_le_mul_left 2 ((Nat.mul_le_mul_right _ i.isLt.le).trans hIN)).trans_eq (by ring)).trans_lt
          (hsmallCap.trans_lt hcapacity))
  · intro σ
    let E := fixedExec A κ hκ V a b x σ
    let X := P1Net.rnState (toOAI V) (Params.B t) (Params.I 1 t) σ ha
    let M := A.growthConstant ^ Params.T K t * (X.maxWireWidth + 1)
    have hlive : LiveTree E := live_execute A κ hκ _ hnLane X
    obtain ⟨z⟩ := live_choices E hlive
    have hcap : M < 2 ^ D.wW :=
      (pushed_width_fits A κ hκ K (toOAI V) 1 t termBias ha hnLane σ z).2
    apply execFits_of_paths D E hcap (hrows σ z) hlive 0
    · intro ι
      simpa only [List.drop_zero, shapeRows] using
        genuineDims_shapes A κ hκ K (toOAI V) 1 t g d bigBias termBias ha hnLane σ ι
    · intro ι
      exact pathWidth_of_payload E (A.records κ hκ _ hnLane X) ι
        (pushed_width_fits A κ hκ K (toOAI V) 1 t termBias ha hnLane σ ι).1
  · exact (Nat.le_mul_of_pos_right D.I (Nat.two_pow_pos (Params.h t))).trans_lt
      (hIN.trans_lt ((by omega : 4 * t ≤ 8 * t).trans_lt (hsmallCap.trans_lt hcapacity)))
  · exact smallWidth_pos A _ _ _
  · intro σ ι
    exact (genuineDims_chainLen A κ hκ K (toOAI V) 1 t g d bigBias termBias ha hnLane σ ι).symm.le
  · exact Nat.le_pow_clog (by decide) d
  · intro σ hf sv ι y
    have hpref := panelPrefix_le ((mkPanels D _ 0 hf sv).final (fixedExec A κ hκ V a b x σ) ι).fits
      (show y.val * ((D.lv D.top).lanes * (D.lv D.top).slots) ≤ _ from by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ y.isLt.le)
    have hfinal := (hs σ ι).z_le
    exact hpref.trans_lt ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (Params.T K t))).trans_lt
      (hfinal.trans_lt ((show C * t * (Params.p t + 1) ≤ (8 + 4 * C) * t * (Params.p t + 1) by
        gcongr; omega).trans_lt hcapacity)))

end
end P1Int.SolRecfit

open Filter in
theorem P1Int.P11.recordsFit : P1Int.P11.RecordsFitTarget := by
  intro k instK S A R instR instAlg κ hκ V a b d bigBias termBias _
  obtain ⟨n, hn⟩ := eventually_atTop.1 (P1Int.SolRecfit.fixedFits A κ hκ V a b d bigBias termBias)
  exact ⟨n, fun x hx => hn x.length hx x rfl⟩

example : P1Int.P11.RecordsFitTarget := @P1Int.P11.recordsFit

#print axioms P1Int.P11.recordsFit
