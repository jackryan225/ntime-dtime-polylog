import P1C10.Field
import OAI.Computability.VPVNP.CompressorExecutionCalendar

namespace P1SolC10K.Sol

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Wit.SolSpace
open P1Int P1Int.P11 P1Wrap
open private levelDims layoutRows prefixPhases blockPhases runPhases shrinkPhase
  from P1Wit.SpaceFacts
open private rowPowers from P1Int.RecordsFitProof

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
variable {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

def RootIsFirstShrink {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X)
    (o : PassOrigins Bt κ hκ E) : Prop :=
  match E, o with
  | .done _, _ => False
  | .more _ _, o => ExecutionCalendar.kind o.1 = .shrink 0

private theorem rootOfCalendar {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X)
    (o : PassOrigins Bt κ hκ E) (rest : List ExecutionCalendar.Phase)
    (h : ExecutionCalendar.Follows E o (.shrink 0 :: rest)) : RootIsFirstShrink Bt κ hκ E o := by
  cases E with
  | done =>
    change (ExecutionCalendar.Phase.shrink 0 :: rest) = [] at h
    cases h
  | more => exact h.1

private theorem rangeStartsZero (n : ℕ) : ∃ t, List.range (n + 1) = 0 :: t := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t ++ [n + 1], by rw [List.range_succ, ht, List.cons_append]⟩

private theorem calendarStarts (s t : ℕ) (hs : 0 < s) :
    ∃ rest, ExecutionCalendar.blocks s (t + 1) = .shrink 0 :: rest := by
  cases s with
  | zero => omega
  | succ s =>
    obtain ⟨r, hr⟩ := rangeStartsZero s
    simp only [ExecutionCalendar.blocks, List.replicate_succ, List.flatten_cons,
      ExecutionCalendar.oneBlock, hr, List.map_cons, List.cons_append]
    exact ⟨_, rfl⟩

theorem executeRoot {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (hT : 0 < T) :
    RootIsFirstShrink Bt κ hκ (Bt.execute κ hκ T hn X) (executeOrigins Bt κ hκ T hn X) := by
  cases T with
  | zero => omega
  | succ T =>
    obtain ⟨rest, he⟩ := calendarStarts S.steps T S.steps_pos
    apply rootOfCalendar Bt κ hκ _ _ rest
    rw [← he]
    exact ExecutionCalendar.execute_follows _ hn X

theorem panelAtStart {D : Dims} {a g b n start : ℕ} {X : State a g} (E : StateExecution F b n X)
    (P : ExecutionPanels D E start) (z : E.Choices) (hs : start ≤ D.top) :
    ∃ v : PanelData D start X,
      P.atLevel E z ⟨start, Nat.lt_succ_of_le hs⟩ le_rfl = ⟨a, g, X, v⟩ := by
  cases E with
  | done => exact ⟨P.val, rfl⟩
  | more =>
    refine ⟨P.1.val z.1, ?_⟩
    simp only [ExecutionPanels.atLevel, Nat.lt_irrefl, dite_false]

theorem adjacentPanels {D : Dims} {a g b n a' g' start : ℕ} {X : State a g}
    (p : StatePass F X a' g') (tail : ∀ c, StateExecution F b n (p.next c))
    (P : ExecutionPanels D (.more p tail) start) (z : (StateExecution.more p tail).Choices) :
    P.atLevel (.more p tail) z ⟨start, Nat.lt_succ_of_lt P.1.property⟩ le_rfl =
        ⟨a, g, X, P.1.val z.1⟩ ∧
    ∃ v : PanelData D (start + 1) (p.next z.1),
      P.atLevel (.more p tail) z ⟨start + 1, Nat.succ_lt_succ P.1.property⟩ (Nat.le_succ _) =
        ⟨a', g', p.next z.1, v⟩ := by
  obtain ⟨v, hv⟩ := panelAtStart (tail z.1) (P.2 z.1) z.2 (Nat.succ_le_of_lt P.1.property)
  refine ⟨?_, v, ?_⟩
  · simp only [ExecutionPanels.atLevel, Nat.lt_irrefl, dite_false]
  · rw [ExecutionPanels.atLevel, dite_eq_left (Nat.lt_succ_self start)]
    exact hv

private theorem firstExponents {a g b n : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) (h : ExecutionCalendar.kind o = .shrink 0) :
    let i : Fin S.steps := ⟨0, S.steps_pos⟩
    a = S.degreeExponent i.castSucc ∧ b = S.degreeExponent i.succ := by
  cases o with
  | refresh X => cases h
  | shrink i hL X =>
    have hi : i = (⟨0, S.steps_pos⟩ : Fin S.steps) :=
      Fin.ext (ExecutionCalendar.Phase.shrink.inj h)
    subst i
    exact ⟨rfl, rfl⟩

theorem firstSlotBits {D : Dims} {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X)
    (o : PassOrigins Bt κ hκ E) (P : ExecutionPanels D E 0) (z : E.Choices)
    (h : RootIsFirstShrink Bt κ hκ E o) :
    let i : Fin S.steps := ⟨0, S.steps_pos⟩
    P1C10.slotBits D 0 = S.degreeExponent i.castSucc ∧ P1C10.slotBits D 1 = S.degreeExponent i.succ := by
  cases E with
  | done => exact False.elim h
  | more p tail =>
    obtain ⟨v, _⟩ := panelAtStart (tail z.1) (P.2 z.1) z.2 (Nat.succ_le_of_lt P.1.property)
    obtain ⟨ha, hb⟩ := firstExponents Bt κ hκ o.1 h
    exact ⟨(P1C10.slotBits_eq (P.1.val z.1).fits.slots).trans ha,
      (P1C10.slotBits_eq v.fits.slots).trans hb⟩

private theorem prefixFirst (S : BlockSchedule k) (j : ℕ) (hj : j ≤ S.steps) (hp : 0 < j) :
    ∃ tail, prefixPhases S j hj = shrinkPhase S ⟨0, S.steps_pos⟩ :: tail := by
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero => exact ⟨[], rfl⟩
    | succ j =>
      obtain ⟨tail, he⟩ := ih (by omega) (Nat.succ_pos _)
      rw [prefixPhases, he, List.cons_append]
      exact ⟨_, rfl⟩

theorem fixedRowZero (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (ht : 0 < (fixedDims Bt V a b x d bigBias termBias).top) :
    let t := lpTime a b x.length
    (fixedDims Bt V a b x d bigBias termBias).lv 0 =
      levelDims S.expanderExponent (S.degreeExponent 0) (Params.h t)
        (initialPositions (toOAI V) 1 t) (some true) := by
  let t := lpTime a b x.length
  let T := Params.T (portConsts Bt) t
  change 0 < (runPhases S T).length at ht
  change ((layoutRows S _ _ (runPhases S T))[0]?).getD _ = _
  cases h : T with
  | zero =>
    rw [h] at ht
    exact False.elim (Nat.not_lt_zero _ ht)
  | succ T' =>
    obtain ⟨tail, he⟩ := prefixFirst S S.steps le_rfl S.steps_pos
    rw [runPhases, blockPhases, he, List.cons_append, List.cons_append]
    rfl

theorem fixedLaneWidth (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias ℓ : ℕ)
    {a' g : ℕ} {X : State a' g}
    (fit : PanelFits (fixedDims Bt V a b x d bigBias termBias) ((fixedDims Bt V a b x d bigBias termBias).lv ℓ) X) :
    ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).laneW = g := by
  have hp := (rowPowers Bt (K := portConsts Bt) (V := toOAI V) 1 (lpTime a b x.length)
    (a * (x.length ^ 2 + 1)) d bigBias termBias ℓ).1
  have he := congrArg (Nat.log 2) (hp.symm.trans fit.lanes)
  simpa only [Nat.log_pow (by decide : 1 < (2 : ℕ))] using he

variable [Algebra (ZMod 2) F]

theorem fixedFirstSlotBits (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) (t : (fixedCD Bt κ hκ V a b x).Tup d)
    (ht : 0 < (fixedDims Bt V a b x d bigBias termBias).top) :
    let D := fixedDims Bt V a b x d bigBias termBias
    let i : Fin S.steps := ⟨0, S.steps_pos⟩
    P1C10.slotBits D 0 = S.degreeExponent i.castSucc ∧ P1C10.slotBits D 1 = S.degreeExponent i.succ := by
  let T := Params.T (portConsts Bt) (lpTime a b x.length)
  have hT : 0 < T := by
    change 0 < (runPhases S T).length at ht
    cases he : T with
    | zero =>
      rw [he] at ht
      exact False.elim (Nat.not_lt_zero _ ht)
    | succ => exact Nat.succ_pos _
  apply firstSlotBits Bt κ hκ (fixedExec Bt κ hκ V a b x t.1) (executeOrigins Bt κ hκ T _ _)
    (H.panels t.1) t.2.1
  exact executeRoot Bt κ hκ T _ _ hT

end
end P1SolC10K.Sol
