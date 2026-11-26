import P1Wit.SpaceEstimates

/-! The sizes of the actual routed and compressed witness. -/

namespace P1Wit.SolSpace

open Filter P1Wrap
open scoped Classical
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
variable {R : Type*} [CommRing R] (κ : A.Entry → R) (hκ : A.IsSolution κ)
variable (K : Consts) (V : FiniteMultiTapeMachine) (aM : ℕ)

/-- The fixed geometric data of a single substep. -/
structure Phase where
  exponent : ℕ
  laneLoss : ℕ
  divisor : ℕ
  shrink : Bool

private def shrinkPhase (S : BlockSchedule k) (i : Fin S.steps) : Phase :=
  let a := S.degreeExponent i.castSucc
  ⟨a, packingLaneBits a 0, packingFactor a, true⟩

private def refreshPhase (S : BlockSchedule k) : Phase :=
  ⟨S.portExponent, S.portExponent, 1, false⟩

private def prefixPhases (S : BlockSchedule k) : (j : ℕ) → j ≤ S.steps → List Phase
  | 0, _ => []
  | j + 1, hj => prefixPhases S j (by omega) ++ [shrinkPhase S ⟨j, hj⟩]

private def blockPhases (S : BlockSchedule k) : List Phase :=
  prefixPhases S S.steps le_rfl ++ [refreshPhase S]

private def runPhases (S : BlockSchedule k) : ℕ → List Phase
  | 0 => []
  | T + 1 => blockPhases S ++ runPhases S T

/-- An execution has the scheduled phase at every node and the scheduled geometric change on every edge. -/
private def Follows {b n : ℕ} : {a g : ℕ} → {X : State a g} → StateExecution R b n X → List Phase → Prop
  | _, _, _, .done _, xs => xs = []
  | _, _, _, .more _ _, [] => False
  | a, g, X, @StateExecution.more _ _ _ _ _ _ _ g' _ q next, ph :: xs =>
    a = ph.exponent ∧ g = ph.laneLoss + g' ∧
      ∀ c, X.positions = ph.divisor * (q.next c).positions ∧ Follows (next c) xs

private theorem follows_bind {a g b n b' n' : ℕ} {X : State a g} (E : StateExecution R b n X)
    (next : (z : E.Choices) → StateExecution R b' n' (E.finalState z)) {xs ys : List Phase}
    (hx : Follows E xs) (hy : ∀ z, Follows (next z) ys) : Follows (E.bind next) (xs ++ ys) := by
  induction E generalizing xs with
  | done =>
    change xs = [] at hx
    subst xs
    exact hy ()
  | more q tail ih =>
    cases xs with
    | nil => exact hx.elim
    | cons ph xs =>
      exact ⟨hx.1, hx.2.1, fun c => ⟨(hx.2.2 c).1,
        ih c _ (hx.2.2 c).2 (fun z => hy ⟨c, z⟩)⟩⟩

private def ProcedureFollows {a b l d : ℕ} {μ : ℝ} (P : Procedure R a b l d μ) (xs : List Phase) : Prop :=
  ∀ g n h X, Follows (P.run g n h X) xs

private theorem follows_id (a : ℕ) : ProcedureFollows (Procedure.id R a) [] := by
  intro g n h X
  have hn : n = g := h.trans (Nat.zero_add g)
  subst g
  rfl

private theorem follows_ofPass {a b l d : ℕ} {μ C : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (q : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (c : (q g X).step.Choice), X.positions = d * ((q g X).next c).positions)
    (he : ∀ g X (c : (q g X).step.Choice),
      ((q g X).next c).energy ≤ μ * X.energy + C * (X.positions : ℝ) ^ 2)
    (shrinking : Bool) : ProcedureFollows (Procedure.ofPass hd hμ hC q hc he) [⟨a, l, d, shrinking⟩] := by
  intro g n h X
  subst n
  exact ⟨rfl, rfl, fun c => ⟨hc g X c, rfl⟩⟩

private theorem follows_seq {a b c l d l' d' : ℕ} {μ ν : ℝ} {P : Procedure R a b l d μ}
    {Q : Procedure R b c l' d' ν} {xs ys : List Phase}
    (hx : ProcedureFollows P xs) (hy : ProcedureFollows Q ys) : ProcedureFollows (P.seq Q) (xs ++ ys) := by
  intro g n h X
  exact follows_bind _ _ (hx _ _ _ X) (fun z => hy _ _ _ _)

private theorem follows_reindex {a b l d a' b' l' d' : ℕ} {μ ν : ℝ} {P : Procedure R a b l d μ}
    {xs : List Phase} (hp : ProcedureFollows P xs) {ha : a = a'} {hb : b = b'} {hl : l = l'}
    {hd : d = d'} {hμ : μ = ν} : ProcedureFollows (P.reindex ha hb hl hd hμ) xs := by
  subst a' b' l' d' ν
  exact hp

private theorem follows_shrink (i : Fin S.steps) :
    ProcedureFollows (A.shrinkProcedure κ hκ i) [shrinkPhase S i] :=
  follows_ofPass _ _ _ _ _ _ true

private theorem follows_refresh : ProcedureFollows (A.refreshProcedure κ hκ) [refreshPhase S] := by
  intro g n h X
  subst n
  exact ⟨rfl, rfl, fun c => ⟨(A.refreshProcedure κ hκ).positions g _ rfl X ⟨c, ()⟩, rfl⟩⟩

private theorem follows_prefix (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureFollows (S.shrinkPrefix (A.shrinkProcedure κ hκ) j hj) (prefixPhases S j hj) := by
  induction j with
  | zero =>
    rw [BlockSchedule.shrinkPrefix, prefixPhases]
    exact follows_reindex (follows_id _)
  | succ j ih =>
    rw [BlockSchedule.shrinkPrefix, prefixPhases]
    exact follows_reindex (follows_seq (ih _) (follows_reindex (follows_shrink A κ hκ ⟨j, hj⟩)))

private theorem follows_block : ProcedureFollows (A.procedure κ hκ) (blockPhases S) := by
  unfold BlockSchedule.Templates.procedure BlockSchedule.assembleBlock blockPhases
  exact follows_reindex (follows_seq (follows_reindex (follows_prefix A κ hκ S.steps le_rfl))
    (follows_refresh A κ hκ))

private theorem follows_repeat (g T n : ℕ) (h : n = T * S.laneBits + g) (X : State (S.degreeExponent 0) n) :
    Follows ((A.procedure κ hκ).repeatExecution g T n h X) (runPhases S T) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa only [Nat.zero_mul, Nat.zero_add] using h
    subst g
    rfl
  | succ T ih =>
    let E := (A.procedure κ hκ).run (T * S.laneBits + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact follows_bind E _ (follows_block A κ hκ _ _ _ X) (fun z => ih _ rfl (E.finalState z))

private theorem follows_execute {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    Follows (A.execute κ hκ T hn X) (runPhases S T) :=
  follows_repeat A κ hκ _ _ _ (Nat.add_sub_of_le hn).symm X


/-- The row layout for one graph state. The arc keys for shrinking are `lane * slots + slot`,
while the refresh keys index the residual lanes after removing the port bits. -/
private def levelDims (expanderExponent degree laneCount positions : ℕ) (shrink : Option Bool) : LevelDims where
  bases := positions / 2 ^ laneCount
  slots := 2 ^ degree
  slotW := degree
  lanes := 2 ^ laneCount
  laneW := laneCount
  shrink := shrink == some true
  colW := if shrink = some true then Nat.clog 2 (2 * 2 ^ degree + 1) else 0
  tagW := if shrink = some true then packingTagBits (2 ^ degree) else 0
  termKeys := match shrink with
    | some true => 2 ^ laneCount * 2 ^ degree
    | some false => 2 ^ (laneCount - degree)
    | none => 0
  termArity := match shrink with
    | some true => 8
    | some false => 2 ^ degree * 2 ^ expanderExponent
    | none => 0

/-- The full chronological directory, with one final row after the elementary substeps. -/
private def layoutRows (S : BlockSchedule k) : (positions laneCount : ℕ) → List Phase → List LevelDims
  | P, g, [] => [levelDims S.expanderExponent (S.degreeExponent 0) g P none]
  | P, g, ph :: xs =>
    levelDims S.expanderExponent ph.exponent g P (some ph.shrink) ::
      layoutRows S (P / ph.divisor) (g - ph.laneLoss) xs

private theorem layoutRows_length (S : BlockSchedule k) (positions laneCount : ℕ) (xs : List Phase) :
    (layoutRows S positions laneCount xs).length = xs.length + 1 := by
  induction xs generalizing positions laneCount with
  | nil => rfl
  | cons ph xs ih => simp only [layoutRows, List.length_cons, ih]

/-- `P₀` is independent of the routed skeleton. -/
def initialPositions (t : ℕ) : ℕ :=
  2 * (Params.I aM t * P1Net.locCount V.K (Params.h t)) * Params.N t

/-- The dimensions are computed from the fixed schedule and the routed size. The skeleton and
selected terms determine field values, and the final state determines the separate payload length. -/
def genuineDims (t g d bigBias termBias : ℕ) : Dims :=
  let phases := runPhases S (Params.T K t)
  let positions := initialPositions V aM t
  let rows := layoutRows S positions (Params.h t) phases
  { r := Fintype.card V.K
    I := Params.I aM t
    N := Params.N t
    nGB := guessBlocks g (Params.bb t)
    top := phases.length
    lv := fun ℓ => (rows[ℓ]?).getD (levelDims S.expanderExponent 0 0 0 none)
    bigW := bigBias + 6 * Params.lam t
    wW := smallWidth A termBias (Params.T K t) (P1Net.tupWidth V (Params.B t))
    chainLen := positions / S.positionFactor ^ Params.T K t + 1
    chainW := Nat.clog 2 d }

private theorem positions_eq {a g : ℕ} (X : State a g) :
    X.positions = Fintype.card X.Base * 2 ^ g := by
  rw [State.positions, Fintype.card_prod, Fintype.card_congr (P1Net.laneEquiv g), Fintype.card_fin]

private theorem levelDims_bases {a g : ℕ} (X : State a g) (e : ℕ) (shrinking : Option Bool) :
    (levelDims e a g X.positions shrinking).bases = Fintype.card X.Base := by
  change X.positions / 2 ^ g = _
  rw [positions_eq]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos g)

/-- The graph state dimensions of a selected execution in chronological order. -/
def stateShapes {b n : ℕ} : {a g : ℕ} → {X : State a g} →
    (E : StateExecution R b n X) → E.Choices → List (ℕ × ℕ × ℕ)
  | _, _, _, .done X, _ => [(Fintype.card X.Base, 2 ^ b, 2 ^ n)]
  | _, _, _, @StateExecution.more _ _ _ _ a g _ _ X _ next, c =>
    (Fintype.card X.Base, 2 ^ a, 2 ^ g) :: stateShapes (next c.1) c.2

private theorem layoutRows_shapes {a g n : ℕ} {X : State a g}
    (E : StateExecution R (S.degreeExponent 0) n X) (c : E.Choices) (xs : List Phase) (h : Follows E xs) :
    (layoutRows S X.positions g xs).map (fun L => (L.bases, L.slots, L.lanes)) = stateShapes E c := by
  induction E generalizing xs with
  | done X =>
    change xs = [] at h
    subst xs
    rw [layoutRows, stateShapes, List.map_singleton, levelDims_bases]
    rfl
  | @more a0 g0 a' g' X0 q next ih =>
    cases xs with
    | nil => exact h.elim
    | cons ph xs =>
      obtain ⟨ha, hg, h⟩ := h
      obtain ⟨hp, ht⟩ := h c.1
      have hdiv : 0 < ph.divisor := by
        by_contra! hz
        have hpos := X0.positions_pos
        rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hp
        omega
      have hP : X0.positions / ph.divisor = (q.next c.1).positions := by
        rw [hp, Nat.mul_comm]
        exact Nat.mul_div_cancel _ hdiv
      have hg' : g0 - ph.laneLoss = g' := by omega
      simp only [layoutRows, stateShapes, List.map_cons, ← ha, levelDims_bases, hP, hg']
      exact congrArg (List.cons (Fintype.card X0.Base, 2 ^ a0, 2 ^ g0)) (ih c.1 c.2 xs ht)

/-- Every dimension row has the base, slot and lane counts of its actual state. -/
theorem genuineDims_shapes (t g d bigBias termBias : ℕ) [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (hn : Params.T K t * S.laneBits ≤ Params.h t)
    (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
    (ι : (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices) :
    let D := genuineDims A K V aM t g d bigBias termBias
    List.ofFn (fun ℓ : Fin (D.top + 1) => ((D.lv ℓ).bases, (D.lv ℓ).slots, (D.lv ℓ).lanes)) =
      stateShapes (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)) ι := by
  let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
  let xs := runPhases S (Params.T K t)
  let rows := layoutRows S X.positions (Params.h t) xs
  have hp := P1Net.rn_positions V (Params.B t) (Params.I aM t) σ ha
  have hlen : rows.length = xs.length + 1 := layoutRows_length S _ _ _
  change List.ofFn (fun ℓ : Fin (xs.length + 1) =>
    let L := ((layoutRows S _ (Params.h t) xs)[ℓ.val]?).getD _
    (L.bases, L.slots, L.lanes)) = _
  rw [← show X.positions = initialPositions V aM t from hp]
  apply Eq.trans _ (layoutRows_shapes _ ι xs (follows_execute A κ hκ _ hn X))
  apply List.ext_getElem
  · simpa only [List.length_ofFn, List.length_map] using hlen.symm
  · intro j h1 h2
    rw [List.getElem_ofFn, List.getElem_map]
    have hj : j < rows.length := by simpa only [List.length_map] using h2
    rw [List.getElem?_eq_getElem hj]
    rfl


private def slotCap (S : BlockSchedule k) : ℕ :=
  Finset.univ.sup fun j : Fin (S.steps + 1) => 2 ^ S.degreeExponent j

private theorem slotCap_ge (S : BlockSchedule k) (j : Fin (S.steps + 1)) : 2 ^ S.degreeExponent j ≤ slotCap S :=
  Finset.le_sup (f := fun j => 2 ^ S.degreeExponent j) (Finset.mem_univ j)

/-- The inequalities needed for the sum of the rows, with the Boolean allowing a refresh. -/
private def CalendarOK (S : BlockSchedule k) : Bool → List Phase → Prop
  | _, [] => True
  | ready, ph :: xs => 2 ^ ph.exponent ≤ slotCap S ∧
    if ph.shrink then 2 ≤ ph.divisor ∧ CalendarOK S true xs
    else ready = true ∧ ph.divisor = 1 ∧ CalendarOK S false xs

private theorem prefixPhases_properties (S : BlockSchedule k) (j : ℕ) (hj : j ≤ S.steps) :
    (prefixPhases S j hj).length = j ∧ ∀ ph ∈ prefixPhases S j hj,
      ph.shrink = true ∧ 2 ^ ph.exponent ≤ slotCap S ∧ 2 ≤ ph.divisor := by
  induction j with
  | zero => simp only [prefixPhases, List.length_nil, List.not_mem_nil, false_implies, implies_true, and_self]
  | succ j ih =>
    obtain ⟨hlen, hph⟩ := ih (Nat.le_of_succ_le hj)
    refine ⟨by simp only [prefixPhases, List.length_append, List.length_singleton, hlen], ?_⟩
    intro ph h
    rw [prefixPhases, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact hph ph h
    · exact ⟨rfl, slotCap_ge S _, (two_lt_packingFactor _).le⟩

private theorem calendar_prepend (S : BlockSchedule k) (xs ys : List Phase)
    (hx : ∀ ph ∈ xs, ph.shrink = true ∧ 2 ^ ph.exponent ≤ slotCap S ∧ 2 ≤ ph.divisor)
    (hy : CalendarOK S true ys) (ready : Bool) (hr : xs = [] → ready = true) :
    CalendarOK S ready (xs ++ ys) := by
  induction xs generalizing ready with
  | nil => rw [hr rfl]; exact hy
  | cons ph xs ih =>
    obtain ⟨hs, hd, hdiv⟩ := hx ph List.mem_cons_self
    have ht := ih (fun p hp => hx p (List.mem_cons_of_mem _ hp)) true (fun _ => rfl)
    change 2 ^ ph.exponent ≤ slotCap S ∧ (if ph.shrink then _ else _)
    rw [ite_eq_left hs]
    exact ⟨hd, hdiv, ht⟩

private theorem runPhases_OK (S : BlockSchedule k) (T : ℕ) (ready : Bool) : CalendarOK S ready (runPhases S T) := by
  induction T generalizing ready with
  | zero => exact True.intro
  | succ T ih =>
    obtain ⟨hlen, hph⟩ := prefixPhases_properties S S.steps le_rfl
    have href : CalendarOK S true (refreshPhase S :: runPhases S T) :=
      ⟨slotCap_ge S (Fin.last S.steps), rfl, rfl, ih false⟩
    rw [runPhases, blockPhases, List.append_assoc, List.singleton_append]
    apply calendar_prepend S _ _ hph href ready
    intro he
    rw [he, List.length_nil] at hlen
    have hpos := S.steps_pos
    omega

private theorem runPhases_length (S : BlockSchedule k) (T : ℕ) :
    (runPhases S T).length = (S.steps + 1) * T := by
  have ht := (prefixPhases_properties S S.steps le_rfl).1
  induction T with
  | zero => simp only [runPhases, List.length_nil, Nat.mul_zero]
  | succ T ih =>
    simp only [runPhases, blockPhases, List.length_append, List.length_singleton, ht, ih, Nat.mul_succ]
    omega

private def posBound (ready : Bool) : ℕ := if ready then 4 else 3

private theorem layoutRows_bounds {a g n : ℕ} {X : State a g}
    (E : StateExecution R (S.degreeExponent 0) n X) (c : E.Choices) (xs : List Phase) (h : Follows E xs)
    (ready : Bool) (good : CalendarOK S ready xs) :
    n ≤ g ∧ (∀ L ∈ layoutRows S X.positions g xs, n ≤ L.laneW ∧ L.laneW ≤ g ∧ L.slots ≤ slotCap S) ∧
      ((layoutRows S X.positions g xs).map (fun L => L.bases * L.lanes)).sum ≤ posBound ready * X.positions := by
  induction E generalizing xs ready with
  | done X =>
    change xs = [] at h
    subst xs
    refine ⟨le_rfl, ?_, ?_⟩
    · intro L hL
      have hL' : L = levelDims S.expanderExponent (S.degreeExponent 0) n X.positions none :=
        List.mem_singleton.mp hL
      subst L
      exact ⟨le_rfl, le_rfl, slotCap_ge S 0⟩
    · have hp : X.positions / 2 ^ n * 2 ^ n ≤ X.positions := Nat.div_mul_le_self _ _
      change X.positions / 2 ^ n * 2 ^ n + 0 ≤ _
      cases ready <;> simp only [posBound, Bool.false_eq_true, ite_false, ite_true] <;> omega
  | @more a0 g0 a' g' X0 q next ih =>
    cases xs with
    | nil => exact h.elim
    | cons ph xs =>
      obtain ⟨_, hg, he⟩ := h
      obtain ⟨hp, ht⟩ := he c.1
      have hdiv : 0 < ph.divisor := by
        by_contra! hz
        have hp0 := X0.positions_pos
        rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hp
        omega
      have hP : X0.positions / ph.divisor = (q.next c.1).positions := by
        rw [hp, Nat.mul_comm]
        exact Nat.mul_div_cancel _ hdiv
      obtain ⟨hslots, hgood⟩ := good
      have htail : ∃ nextReady : Bool, CalendarOK S nextReady xs ∧
          X0.positions + posBound nextReady * (q.next c.1).positions ≤ posBound ready * X0.positions := by
        by_cases hs : ph.shrink = true
        · rw [ite_eq_left hs] at hgood
          have hhalf := (Nat.mul_le_mul_right (q.next c.1).positions hgood.1).trans_eq hp.symm
          refine ⟨true, hgood.2, ?_⟩
          cases ready <;> simp only [posBound, Bool.false_eq_true, ite_false, ite_true] <;> omega
        · rw [ite_eq_right hs] at hgood
          obtain ⟨rfl, hd, hrest⟩ := hgood
          rw [hd, Nat.one_mul] at hp
          refine ⟨false, hrest, ?_⟩
          change _ + 3 * (q.next c.1).positions ≤ 4 * X0.positions
          omega
      obtain ⟨nextReady, hcal, hsum⟩ := htail
      obtain ⟨hgmin, hrows, hcost⟩ := ih c.1 c.2 xs ht nextReady hcal
      have hnext : g' ≤ g0 := by omega
      have hLane : g0 - ph.laneLoss = g' := by omega
      refine ⟨hgmin.trans hnext, ?_, ?_⟩
      · intro L hL
        change L ∈ levelDims _ _ _ _ _ :: layoutRows S (X0.positions / ph.divisor) (g0 - ph.laneLoss) xs at hL
        rcases List.mem_cons.mp hL with rfl | hL
        · exact ⟨hgmin.trans hnext, le_rfl, hslots⟩
        · rw [hP, hLane] at hL
          obtain ⟨hlo, hhi, hsl⟩ := hrows L hL
          exact ⟨hlo, hhi.trans hnext, hsl⟩
      · simp only [layoutRows, List.map_cons, List.sum_cons, hP, hLane]
        refine (Nat.add_le_add (Nat.div_mul_le_self X0.positions _) hcost).trans ?_
        exact hsum

private theorem sum_rows (rows : List LevelDims) (default : LevelDims) (f : LevelDims → ℕ) :
    ∑ j ∈ Finset.range rows.length, f ((rows[j]?).getD default) = (rows.map f).sum := by
  induction rows with
  | nil => simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, List.map_nil, List.sum_nil]
  | cons row rows ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.sum_cons, ih,
      Nat.add_comm]


private theorem layoutRows_form (S : BlockSchedule k) (P g : ℕ) (xs : List Phase) :
    ∀ L ∈ layoutRows S P g xs, ∃ a l Q shrinking, L = levelDims S.expanderExponent a l Q shrinking := by
  induction xs generalizing P g with
  | nil =>
    intro L hL
    exact ⟨_, _, _, _, List.mem_singleton.mp hL⟩
  | cons ph xs ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hhead | htail
    · exact ⟨_, _, _, _, hhead⟩
    · exact ih _ _ L htail

private def levelConstant (S : BlockSchedule k) : ℕ :=
  slotCap S + (2 * slotCap S + 1) + packingTagBits (slotCap S) + 8 + slotCap S * 2 ^ S.expanderExponent + 1

private theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.clog_mono_right 2 (Params.lt_two_pow' n).le).trans_eq (Nat.clog_pow 2 n (by decide))

private theorem levelDims_bounds (S : BlockSchedule k) {a g P : ℕ} (shrinking : Option Bool)
    (hslots : 2 ^ a ≤ slotCap S) :
    let L := levelDims S.expanderExponent a g P shrinking
    L.lanes = 2 ^ L.laneW ∧ L.slotW ≤ levelConstant S ∧ L.colW ≤ levelConstant S ∧
      L.tagW ≤ levelConstant S ∧ L.termKeys ≤ slotCap S * L.lanes ∧ L.termArity ≤ levelConstant S := by
  have hslotW : a ≤ levelConstant S := by
    have h := (Params.lt_two_pow' a).le.trans hslots
    unfold levelConstant
    omega
  have hcolW : Nat.clog 2 (2 * 2 ^ a + 1) ≤ levelConstant S := by
    have h : Nat.clog 2 (2 * 2 ^ a + 1) ≤ 2 * slotCap S + 1 := (clog_le_self _).trans (by omega)
    unfold levelConstant
    omega
  have htagW : packingTagBits (2 ^ a) ≤ levelConstant S := by
    have h : packingTagBits (2 ^ a) ≤ packingTagBits (slotCap S) := by
      unfold packingTagBits
      apply Nat.add_le_add_right (Nat.log_mono_right ?_)
      gcongr
    unfold levelConstant
    omega
  have hshrinkArity : 8 ≤ levelConstant S := by unfold levelConstant; omega
  have hrefreshArity : 2 ^ a * 2 ^ S.expanderExponent ≤ levelConstant S := by
    have h := Nat.mul_le_mul_right (2 ^ S.expanderExponent) hslots
    unfold levelConstant
    omega
  have hshrinkKeys : 2 ^ g * 2 ^ a ≤ slotCap S * 2 ^ g := by
    rw [Nat.mul_comm (2 ^ g) (2 ^ a)]
    exact Nat.mul_le_mul_right _ hslots
  have hrefreshKeys : 2 ^ (g - a) ≤ slotCap S * 2 ^ g :=
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans
      (Nat.le_mul_of_pos_left _ ((Nat.two_pow_pos a).trans_le hslots))
  cases shrinking with
  | none => exact ⟨rfl, hslotW, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  | some s =>
    cases s
    · exact ⟨rfl, hslotW, Nat.zero_le _, Nat.zero_le _, hrefreshKeys, hrefreshArity⟩
    · exact ⟨rfl, hslotW, hcolW, htagW, hshrinkKeys, hshrinkArity⟩

/-- The length of the lambda chain is exactly one more than the actual number of final positions. -/
theorem genuineDims_chainLen (t g d bigBias termBias : ℕ) [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (hn : Params.T K t * S.laneBits ≤ Params.h t)
    (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
    (ι : (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices) :
    (genuineDims A K V aM t g d bigBias termBias).chainLen =
      ((A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).finalState ι).positions + 1 := by
  let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
  let Y := (A.execute κ hκ (Params.T K t) hn X).finalState ι
  let F := S.positionFactor ^ Params.T K t
  change initialPositions V aM t / F + 1 = Y.positions + 1
  have hpos : X.positions = initialPositions V aM t := P1Net.rn_positions V _ _ σ ha
  have hb : X.positions = F * Y.positions := (A.branch_bounds κ hκ (Params.T K t) hn X ι).1
  have hF : 0 < F := Nat.pow_pos ((by decide : 0 < 2).trans S.positionFactor_gt_two)
  rw [← hpos, hb, Nat.mul_comm F, Nat.mul_div_cancel _ hF]

/-- The final payload assignments are exactly as numerous as the bit strings of the chosen payload length. -/
theorem genuine_payload_card (t : ℕ) [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (hn : Params.T K t * S.laneBits ≤ Params.h t)
    (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
    (ι : (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices) :
    let Y := (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).finalState ι
    Fintype.card ((e : Y.network.Edge) → Y.network.Payload e) = 2 ^ Y.totalWidth :=
  P1P5.card_final_payloads _

/-- All twenty fields of `SpaceIn` hold for the actual dimensions, with a common constant
independent of time, the routed skeleton and the selected compression branch. -/
theorem genuine_spaceIn (haM : 1 ≤ aM) (hb0 : S.laneBits ≤ K.b0) (hC2 : A.growthConstant ≤ K.C2)
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (d bigBias termBias : ℕ) :
    ∃ C : ℕ, ∀ᶠ t in atTop, ∀ [NeZero (Params.B t)] [NeZero (Params.I aM t)],
      ∀ g, 2 * g ≤ t → ∀ (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
        (ι : (A.execute κ hκ (Params.T K t) (laneBudget K hb0 t)
          (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices),
        SpaceIn K aM C t (genuineDims A K V aM t g d bigBias termBias)
          ((A.execute κ hκ (Params.T K t) (laneBudget K hb0 t)
            (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).finalState ι).totalWidth := by
  obtain ⟨M, hM⟩ := exists_nat_ge A.widthAllowance
  let Cz := 4 * aM * (20 * locCoeff V) * (2 ^ S.degreeExponent 0 * tupleCoeff V + M)
  let Cs := termBias + tupleCoeff V + 4
  let Cp := 80 * locCoeff V
  let C := 1 + Fintype.card V.K + (bigBias + 6) + Cs + (Cp + 1) + Nat.clog 2 d + (S.steps + 1) + levelConstant S + Cz
  refine ⟨C, ?_⟩
  filter_upwards [Params.eventually_Ib aM haM, eventually_ge_atTop 2] with t hI ht
  intro instB instI g hg σ ι
  let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
  let E := A.execute κ hκ (Params.T K t) (laneBudget K hb0 t) X
  let Y := E.finalState ι
  let D := genuineDims A K V aM t g d bigBias termBias
  let xs := runPhases S (Params.T K t)
  let rows := layoutRows S X.positions (Params.h t) xs
  let U := Params.I aM t * Params.N t * (Params.p t + 1)
  have hp : X.positions = initialPositions V aM t := P1Net.rn_positions V _ _ σ ha
  have h0 := initial_positions_le V aM ha σ
  have hlen : rows.length = D.top + 1 := layoutRows_length S _ _ _
  have hLv (ℓ : ℕ) : D.lv ℓ = (rows[ℓ]?).getD (levelDims S.expanderExponent 0 0 0 none) := by
    change ((layoutRows S (initialPositions V aM t) (Params.h t) xs)[ℓ]?).getD _ = _
    rw [← hp]
  obtain ⟨_, hrows, hsum⟩ := layoutRows_bounds E ι xs
    (follows_execute A κ hκ _ (laneBudget K hb0 t) X) true (runPhases_OK S _ true)
  have hbudget : Params.h t - K.b0 * Params.T K t ≤ Params.h t - Params.T K t * S.laneBits := by
    apply Nat.sub_le_sub_left
    rw [Nat.mul_comm (Params.T K t)]
    exact Nat.mul_le_mul_right _ hb0
  have hsum' : ∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes ≤ Cp * U := by
    calc
      _ = (rows.map fun L => L.bases * L.lanes).sum := by
        rw [← hlen]
        simp only [hLv]
        exact sum_rows rows _ (fun L => L.bases * L.lanes)
      _ ≤ 4 * X.positions := hsum
      _ ≤ 4 * ((20 * locCoeff V) * U) := Nat.mul_le_mul_left _ h0
      _ = _ := by dsimp [Cp]; ring
  have hfields (ℓ : ℕ) (hℓ : ℓ ≤ D.top) :
      let L := D.lv ℓ
      L.lanes = 2 ^ L.laneW ∧ Params.h t - K.b0 * Params.T K t ≤ L.laneW ∧ L.laneW ≤ Params.h t ∧
        L.slots ≤ C ∧ L.slotW ≤ C ∧ L.colW ≤ C ∧ L.tagW ≤ C ∧ L.termKeys ≤ C * L.lanes ∧ L.termArity ≤ C := by
    have hi : ℓ < rows.length := by omega
    have hmem : D.lv ℓ ∈ rows := by
      rw [hLv, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    obtain ⟨hlo, hhi, hs⟩ := hrows (D.lv ℓ) hmem
    obtain ⟨a, l, P, shrinking, he⟩ := layoutRows_form S _ _ xs _ hmem
    have hs' : 2 ^ a ≤ slotCap S := by rw [he] at hs; exact hs
    obtain ⟨hLan, hSW, hCol, hTag, hKey, hArity⟩ := levelDims_bounds S shrinking hs'
    have hCl : levelConstant S ≤ C := by dsimp [C]; omega
    have hCs : slotCap S ≤ C := by unfold levelConstant at hCl; omega
    rw [he] at hlo hhi ⊢
    exact ⟨hLan, hbudget.trans hlo, hhi, hs'.trans hCs, hSW.trans hCl, hCol.trans hCl, hTag.trans hCl,
      hKey.trans (Nat.mul_le_mul_right _ hCs), hArity.trans hCl⟩
  refine
    { I_eq := rfl
      N_eq := rfl
      r_le := ?_
      nGB_le := ?_
      bigW_le := ?_
      wW_le := ?_
      chainLen_le := ?_
      chainW_le := ?_
      top_le := ?_
      pos_le := ?_
      lanes_eq := fun l hl => (hfields l hl).1
      laneW_ge := fun l hl => (hfields l hl).2.1
      laneW_le := fun l hl => (hfields l hl).2.2.1
      slots_le := fun l hl => (hfields l hl).2.2.2.1
      slotW_le := fun l hl => (hfields l hl).2.2.2.2.1
      colW_le := fun l hl => (hfields l hl).2.2.2.2.2.1
      tagW_le := fun l hl => (hfields l hl).2.2.2.2.2.2.1
      keys_le := fun l hl => (hfields l hl).2.2.2.2.2.2.2.1
      arity_le := fun l hl => (hfields l hl).2.2.2.2.2.2.2.2
      z_le := ?_ }
  · change Fintype.card V.K ≤ C
    dsimp [C]; omega
  · exact (guessBlocks_le aM haM hg).trans (Nat.le_mul_of_pos_left _ (by dsimp [C]; omega))
  · change bigBias + 6 * Params.lam t ≤ C * Params.lam t
    have hm : bigBias ≤ bigBias * Params.lam t := Nat.le_mul_of_pos_right _ (Params.lam_pos ht)
    calc
      _ ≤ bigBias * Params.lam t + 6 * Params.lam t := Nat.add_le_add_right hm _
      _ = (bigBias + 6) * Params.lam t := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  · exact (smallWidth_le A K V hC2 termBias t).trans (Nat.mul_le_mul_right _ (by dsimp [C]; omega))
  · have hchain := genuineDims_chainLen A κ hκ K V aM t g d bigBias termBias ha (laneBudget K hb0 t) σ ι
    have hb : X.positions = S.positionFactor ^ Params.T K t * Y.positions :=
      (A.branch_bounds κ hκ (Params.T K t) (laneBudget K hb0 t) X ι).1
    have hY : Y.positions ≤ X.positions :=
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos ((by decide : 0 < 2).trans S.positionFactor_gt_two))).trans_eq hb.symm
    have hCp : X.positions ≤ Cp * U := h0.trans (Nat.mul_le_mul_right _ (by dsimp [Cp]; omega))
    have hIpos : 0 < Params.I aM t := Nat.pos_of_ne_zero (NeZero.ne _)
    have hU : 1 ≤ U := Nat.mul_pos (Nat.mul_pos hIpos (Nat.two_pow_pos _)) (Nat.succ_pos _)
    change D.chainLen ≤ C * D.I * D.N * (Params.p t + 1)
    rw [hchain, show C * D.I * D.N * (Params.p t + 1) = C * U by dsimp [D, genuineDims, U]; ring]
    calc
      Y.positions + 1 ≤ Cp * U + 1 := Nat.add_le_add_right (hY.trans hCp) _
      _ ≤ (Cp + 1) * U := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ C * U := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  · change Nat.clog 2 d ≤ C
    dsimp [C]; omega
  · have hT := Params.T_le_p K t
    have hst : 1 ≤ S.steps + 1 := by omega
    change xs.length + 1 ≤ C * (Params.p t + 1)
    dsimp [xs]
    rw [runPhases_length]
    calc
      _ ≤ (S.steps + 1) * Params.p t + (S.steps + 1) := Nat.add_le_add (Nat.mul_le_mul_left _ hT) hst
      _ = (S.steps + 1) * (Params.p t + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  · change (∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes) ≤ C * D.I * D.N * (Params.p t + 1)
    rw [show C * D.I * D.N * (Params.p t + 1) = C * U by dsimp [D, genuineDims, U]; ring]
    exact hsum'.trans (Nat.mul_le_mul_right _ (by dsimp [C]; omega))
  · exact (final_width_le A κ hκ K V aM t M hM hI.2 ha (laneBudget K hb0 t) σ ι).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by dsimp [C]; omega)))

/-- The fixed layout and actual payload fit the witness budget for every sufficiently large time bound. -/
theorem genuine_enc_length_le (haM : 1 ≤ aM) (hb0 : S.laneBits ≤ K.b0) (hC2 : A.growthConstant ≤ K.C2)
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (d bigBias termBias : ℕ) :
    ∀ᶠ t in atTop, ∀ [NeZero (Params.B t)] [NeZero (Params.I aM t)],
      ∀ g, 2 * g ≤ t → ∀ (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
        (ι : (A.execute κ hκ (Params.T K t) (laneBudget K hb0 t)
          (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices),
        (genuineDims A K V aM t g d bigBias termBias).fixedLen +
          ((A.execute κ hκ (Params.T K t) (laneBudget K hb0 t)
            (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).finalState ι).totalWidth ≤ Params.m K t := by
  obtain ⟨C, hC⟩ := genuine_spaceIn A κ hκ K V aM haM hb0 hC2 ha d bigBias termBias
  filter_upwards [hC, enc_length_le K haM C] with t hsize hfit
  intro instB instI g hg σ ι
  exact hfit _ _ (@hsize instB instI g hg σ ι)

#print axioms genuine_spaceIn
#print axioms genuine_enc_length_le

end
end P1Wit.SolSpace
