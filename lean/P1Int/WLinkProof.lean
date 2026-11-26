import P1Int.WLinkDefs
import P1Int.FormLev
import P1ChkFinal.Bridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

namespace P1Int.P11.SolWLink

open CompressorRecords Compression.Refresh Compression.DegreeRefresh
open P1Wit P1Wit.SolWitfill P1Wit.SolSpace P1P7 P1ChkFinal
open P1Int.SolTrueRecords

private def Reads (D : Dims) (u : List Bool) (ℓ : ℕ) (r : LevelRecords D (D.lv ℓ)) : Prop :=
  ∀ k i, i < (D.lv ℓ).count k → readField D u (secLev ℓ k) i = r.code k i

private theorem reads_terms {D : Dims} {u : List Bool} {ℓ : ℕ} {r : LevelRecords D (D.lv ℓ)}
    (hr : Reads D u ℓ r) {y key c : ℕ} (hy : y < (D.lv ℓ).bases) (hk : key < (D.lv ℓ).termKeys)
    (hc : c < (D.lv ℓ).termArity + 1) :
    rdTerms D u ℓ y key c = termValue (r.terms ⟨y * (D.lv ℓ).termKeys + key, idx_lt hy hk⟩) c := by
  unfold rdTerms
  rw [hr .terms _ (idx_lt (idx_lt hy hk) hc)]
  simp only [LevelRecords.code, idx_div hc, idx_mod hc]
  exact atIndex_fin _ ⟨_, idx_lt hy hk⟩

private theorem reads_numbered {D : Dims} {u : List Bool} {ℓ : ℕ} {r : LevelRecords D (D.lv ℓ)}
    (hr : Reads D u ℓ r) {A I : Type} {address : A → ℕ} {entry : I → ℕ}
    (ha : Function.Injective address) (he : Function.Injective entry)
    {terms : A → Option (I → ℕ)} (ht : r.terms = numberedTerms D ℓ address entry terms)
    (s : A) {y key : ℕ} (hs : address s = y * (D.lv ℓ).termKeys + key)
    (hy : y < (D.lv ℓ).bases) (hk : key < (D.lv ℓ).termKeys)
    (hei : ∀ i, entry i < (D.lv ℓ).termArity)
    (hv : ∀ v, terms s = some v → ∀ i, v i < 2 ^ D.wW) :
    (rdTerms D u ℓ y key 0, fun i => rdTerms D u ℓ y key (1 + entry i)) =
      P1ChkGreedy.termCode (terms s) := by
  have ht' :
      r.terms ⟨y * (D.lv ℓ).termKeys + key, idx_lt hy hk⟩ =
        (terms s).map (fun v p => fieldValue D.wW (readNumbered entry v 0 p.val)) := by
    rw [ht]
    change (readNumbered address terms none (y * (D.lv ℓ).termKeys + key)).map _ = _
    rw [← hs, readNumbered_at ha]
  have flag := (reads_terms hr hy hk (Nat.zero_lt_succ _)).trans (congrArg (fun v => termValue v 0) ht')
  have coord (i : I) := (reads_terms hr hy hk (show 1 + entry i < (D.lv ℓ).termArity + 1 by
    have hi := hei i
    omega)).trans (congrArg (fun v => termValue v (1 + entry i)) ht')
  cases h : terms s with
  | none =>
    apply Prod.ext
    · simpa only [h, Option.map_none, termValue, Option.isSome, Bool.false_eq_true, ite_false,
        P1ChkGreedy.termCode] using flag
    · funext i
      have hz : termValue (none : TermSlot D (D.lv ℓ)) (1 + entry i) = 0 := by
        rw [Nat.add_comm 1]
        exact atIndex_fin (fun _ => 0) (⟨entry i, hei i⟩ : Fin (D.lv ℓ).termArity)
      exact ((coord i).trans (by rw [h, Option.map_none])).trans hz
  | some v =>
    apply Prod.ext
    · simpa only [h, Option.map_some, termValue, Option.isSome, ite_true, P1ChkGreedy.termCode] using flag
    · funext i
      apply (coord i).trans
      rw [h, Option.map_some, Nat.add_comm 1, termValue]
      calc
        _ = (fieldValue D.wW (readNumbered entry v 0 (entry i))).val :=
          atIndex_fin _ (⟨entry i, hei i⟩ : Fin (D.lv ℓ).termArity)
        _ = v i := by rw [readNumbered_at he, fieldValue_val (hv v h i)]

private theorem baseValue_addr {a g : ℕ} (X : State a g) (f : X.Base → ℕ) (y : X.Base) :
    baseValue X f (addr X y) = f y := by
  unfold baseValue addr
  rw [dite_eq_left (X.baseIndex y).isLt]
  exact congrArg f (X.baseIndex.symm_apply_apply y)

private theorem finValue_at {n bound : ℕ} (f : Fin n → Fin bound) {i : ℕ} (hi : i < n) :
    finValue f i = (f ⟨i, hi⟩).val :=
  finValue_fin f ⟨i, hi⟩

open private Follows follows_execute levelDims levelDims_bases
  layoutRows runPhases runPhases_length from P1Wit.SpaceFacts

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

local notation "degH" => 2 ^ S.expanderExponent
local notation "Hpos" => Nat.two_pow_pos S.expanderExponent
local notation "Hconn" => And.left (S.port_bound.connected_and_pos S.port_order)

attribute [local instance] P1P7.instDecEqBase

private theorem refresh_coord_lt (D : Dims) {g : ℕ} (X : State S.portExponent (S.portExponent + g))
    (c : DyadicRefreshChoice X S.graph Hpos Hconn Bt.refresh)
    (hrec : (dyadicRefreshNext X S.graph Hpos Hconn Bt.refresh S.port_order S.degree_bounds.2 c).maxWireWidth + 1 ≤
      Bt.recordLimit * (X.maxWireWidth + 1))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (s : X.Base × BitWord g) (j : Fin (2 ^ S.portExponent) × Fin degH) :
    (c s).val j < 2 ^ D.wW := by
  let Y := dyadicRefreshNext X S.graph Hpos Hconn Bt.refresh S.port_order S.degree_bounds.2 c
  let w := ((nb S.graph Hpos Hconn Bt.refresh S.port_order S.degree_bounds.2 X c (s.1, j.1),
    refreshSlots S.degree_bounds.2 (.inr (.inl j.2))), s.2)
  have hw : Y.width w = MotifConversion.supplyWidths Bt.refresh (P1ChkGreedy.blockW X s) (c s).val j :=
    rwidth_int S.graph Hpos Hconn Bt.refresh S.port_order S.degree_bounds.2 X c s.1 j.1 j.2 s.2
  have hcoord : (c s).val j ≤ Y.maxWireWidth := by
    refine le_trans ?_ (Y.width_le_maxWireWidth w)
    rw [hw]
    exact Nat.le_add_right _ _
  exact (hcoord.trans_lt hrec).trans hW

private theorem origin_of_reads (D : Dims) (u : List Bool) (ℓ : ℕ)
    {a g b n : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) (s : p.step.Choice) (f : PanelFits D (D.lv ℓ) X)
    (rec : p.Records) (hrec : p.Bounded rec Bt.recordLimit)
    (hrow : D.lv ℓ = levelDims S.expanderExponent a g X.positions (some (isShrink Bt κ hκ o)))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (hr : Reads D u ℓ (levelRecordsOfState X f
      ⟨(panelAt Bt κ hκ D ℓ o s).layout, (panelAt Bt κ hκ D ℓ o s).colour,
       (panelAt Bt κ hκ D ℓ o s).offset, (panelAt Bt κ hκ D ℓ o s).energy, tableAt Bt κ hκ D ℓ o s⟩)) :
    P1SolCone.SolCone.OriginExtras Bt κ hκ D u ℓ o s := by
  have hbases := f.bases
  cases o with
  | shrink i h X =>
    subst h
    have hlayout : (D.lv ℓ).shrink = true := hrow ▸ rfl
    have hkeys : (D.lv ℓ).termKeys = 2 ^ packingLaneBits (S.degreeExponent i.castSucc) n *
        2 ^ S.degreeExponent i.castSucc := hrow ▸ rfl
    have harity : (D.lv ℓ).termArity = 8 := hrow ▸ rfl
    have hcol : (D.lv ℓ).colW = Nat.clog 2 (2 * 2 ^ S.degreeExponent i.castSucc + 1) := hrow ▸ rfl
    have htag : (D.lv ℓ).tagW = packingTagBits (2 ^ S.degreeExponent i.castSucc) := hrow ▸ rfl
    have hb (y : X.Base) : addr X y < (D.lv ℓ).bases := (X.baseIndex y).isLt.trans_eq hbases.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      have hc : addr X y < (D.lv ℓ).count .colour := by
        simpa only [LevelDims.count, hlayout, ite_true] using hb y
      unfold rdColour
      rw [hr .colour _ hc]
      change finValue (fun j => fieldValue (D.lv ℓ).colW
        (baseValue X (fun z => (X.packingData.color z).val) j.val)) (addr X y) = _
      rw [finValue_at _ (hb y), baseValue_addr]
      exact fieldValue_val (by rw [hcol]; exact (X.packingData.color y).isLt.trans_le (Nat.le_pow_clog (by decide) _))
    · intro y
      have hc : addr X y < (D.lv ℓ).count .offset := by
        simpa only [LevelDims.count, hlayout, ite_true] using hb y
      unfold rdOffset
      rw [hr .offset _ hc]
      change finValue (fun j => fieldValue (D.lv ℓ).tagW
        (baseValue X (fun z => bwNum (X.packingData.offset z)) j.val)) (addr X y) = _
      rw [finValue_at _ (hb y), baseValue_addr]
      exact fieldValue_val (by rw [htag]; exact (bitWordFinEquiv _ (X.packingData.offset y)).isLt)
    · unfold rdLayout
      exact hr .layout 0 (by simp only [LevelDims.count, hlayout, ite_true, Nat.zero_lt_one])
    · intro y
      apply termsDec_of_greedy Bt.shrink D u ℓ X s _ y
      intro e
      apply reads_numbered hr (shrinkAddress_injective X hkeys.ge) shrinkEntry_injective rfl e rfl
      · exact hb ((packingArcEquiv X.Base _ n).symm e).1.1
      · rw [hkeys]
        exact shrinkKey_lt X e
      · intro j
        rw [harity]
        exact shrinkEntry_lt j
      · exact shrinkTerm_lt Bt D i X hW s e
  | @refresh n X =>
    have hkeys : (D.lv ℓ).termKeys = 2 ^ n := by
      rw [hrow]
      change 2 ^ (S.portExponent + n - S.portExponent) = 2 ^ n
      rw [Nat.add_sub_cancel_left]
    have harity : (D.lv ℓ).termArity = 2 ^ S.portExponent * degH := hrow ▸ rfl
    have hnext : (dyadicRefreshNext X S.graph Hpos Hconn Bt.refresh S.port_order S.degree_bounds.2 s).maxWireWidth + 1 ≤
        Bt.recordLimit * (X.maxWireWidth + 1) :=
      (Nat.succ_le_succ (hrec s).2.2).trans (hrec s).2.1
    apply rterm_of_greedy S.graph Hpos Hconn Bt.refresh D u ℓ X s
    intro v
    apply reads_numbered hr (refreshAddress_injective X hkeys.ge) refreshEntry_injective rfl v rfl
    · exact (X.baseIndex v.1).isLt.trans_eq hbases.symm
    · rw [hkeys]
      exact (bitWordFinEquiv n v.2).isLt
    · intro j
      rw [harity]
      exact idx_lt j.1.isLt j.2.isLt
    · intro w hw j
      have hval : (s v).val = w := Option.some.inj hw
      rw [← hval]
      exact refresh_coord_lt Bt D X s hnext hW v j

private def levelFrom {D : Dims} {a g b n start : ℕ} {X : State a g} (E : StateExecution F b n X)
    (P : ExecutionPanels D E start) (T : ExecutionTerms D E start) (c : E.Choices)
    (ℓ : Fin (D.top + 1)) (hℓ : start ≤ ℓ.val) : LevelRecords D (D.lv ℓ.val) :=
  let p := P.atLevel E c ℓ hℓ
  levelRecordsOfState p.state p.data.fits (p.data.step (T.table E c ℓ))

private theorem levelFrom_head {D : Dims} {a g a' g' b n start : ℕ} {X : State a g}
    {p : StatePass F X a' g'} {tail : ∀ i, StateExecution F b n (p.next i)}
    (P : ExecutionPanels D (.more p tail) start) (T : ExecutionTerms D (.more p tail) start)
    (c : (StateExecution.more p tail).Choices) :
    levelFrom (.more p tail) P T c ⟨start, T.1.in_range⟩ le_rfl =
      levelRecordsOfState X (P.1.val c.1).fits ((P.1.val c.1).step (T.1.encode c.1)) := by
  let ℓ : Fin (D.top + 1) := ⟨start, T.1.in_range⟩
  have hp : P.atLevel (.more p tail) c ℓ le_rfl = ⟨a, g, X, P.1.val c.1⟩ := by
    rw [ExecutionPanels.atLevel]
    split
    · rename_i h
      exact (Nat.lt_irrefl start h).elim
    · rfl
  have ht : T.table (.more p tail) c ℓ = T.1.encode c.1 := by
    simp only [ExecutionTerms.table, ℓ, dite_true]
  exact congrArg₂ (fun (p : IndexedPanel D ℓ.val) terms =>
    levelRecordsOfState p.state p.data.fits (p.data.step terms)) hp ht

private theorem levelFrom_tail {D : Dims} {a g a' g' b n start : ℕ} {X : State a g}
    {p : StatePass F X a' g'} {tail : ∀ i, StateExecution F b n (p.next i)}
    (P : ExecutionPanels D (.more p tail) start) (T : ExecutionTerms D (.more p tail) start)
    (c : (StateExecution.more p tail).Choices) (ℓ : Fin (D.top + 1)) (hℓ : start + 1 ≤ ℓ.val) :
    levelFrom (.more p tail) P T c ℓ (Nat.le_of_succ_le hℓ) =
      levelFrom (tail c.1) (P.2 c.1) (T.2 c.1) c.2 ℓ hℓ := by
  have hlt : start < ℓ.val := hℓ
  have hn : (⟨start, T.1.in_range⟩ : Fin (D.top + 1)) ≠ ℓ := by
    intro e
    exact (Nat.ne_of_lt hlt) (congrArg Fin.val e)
  have hp : P.atLevel (.more p tail) c ℓ (Nat.le_of_succ_le hℓ) =
      (P.2 c.1).atLevel (tail c.1) c.2 ℓ hℓ := by
    rw [ExecutionPanels.atLevel]
    split
    · rfl
    · rename_i h
      exact (h hlt).elim
  have ht : T.table (.more p tail) c ℓ = (T.2 c.1).table (tail c.1) c.2 ℓ := by
    simp only [ExecutionTerms.table, dite_eq_right hn]
  exact congrArg₂ (fun (p : IndexedPanel D ℓ.val) terms =>
    levelRecordsOfState p.state p.data.fits (p.data.step terms)) hp ht

private theorem branch_of_reads (D : Dims) (u : List Bool) {a g b n : ℕ} {X : State a g}
    (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E) (c : E.Choices) (start : ℕ)
    (f : ExecFits D E start) (injective : TablesInjective D E start (tableTree Bt κ hκ D E o start))
    (r : E.Records) (hr : E.Bounded Bt.recordLimit r) (xs : List Phase)
    (hphase : Follows E xs)
    (hLoss : ∀ ph ∈ xs, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent))
    (hrows : ∀ j, D.lv (start + j) = ((layoutRows S X.positions g xs)[j]?).getD
      (levelDims S.expanderExponent 0 0 0 none))
    (hW : Bt.recordLimit ^ xs.length * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (hread : ∀ (ℓ : Fin (D.top + 1)) (h : start ≤ ℓ.val), Reads D u ℓ.val
      (levelFrom E (mkPanels D E start f (panelTree Bt κ hκ D E o start))
        (mkTerms D E start f (tableTree Bt κ hκ D E o start) injective) c ℓ h)) :
    P1SolCone.SolCone.BranchExtras Bt κ hκ D u E o c start := by
  induction E generalizing start xs with
  | done => exact True.intro
  | @more a g a' g' X p tail ih =>
    cases xs with
    | nil => exact hphase.elim
    | cons ph xs =>
      obtain ⟨hdeg, hlanes, htail⟩ := hphase
      have he := Nat.add_right_cancel (hlanes.symm.trans (origin_lanes Bt κ hκ o.1))
      rw [hLoss ph List.mem_cons_self, ← hdeg] at he
      have hkind : ph.shrink = isShrink Bt κ hκ o.1 := by
        have hp : a < packingLaneBits a 0 := by
          unfold packingLaneBits
          have := Nat.two_pow_pos a
          omega
        cases hs : ph.shrink <;> cases ho : isShrink Bt κ hκ o.1 <;>
          simp only [hs, ho, Bool.false_eq_true, ite_false, ite_true] at he ⊢
        · omega
        · omega
      have hrow := hrows 0
      simp only [Nat.add_zero, layoutRows, List.getElem?_cons_zero, Option.getD_some, ← hdeg, hkind] at hrow
      have hlim : 0 < Bt.recordLimit := (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      have hbudget : Bt.recordLimit ^ xs.length * (Bt.recordLimit * (X.maxWireWidth + 1)) < 2 ^ D.wW := by
        rwa [← Nat.mul_assoc, ← pow_succ]
      have hlocal : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW :=
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos hlim)).trans_lt hbudget
      let P := mkPanels D (.more p tail) start f (panelTree Bt κ hκ D (.more p tail) o start)
      let T := mkTerms D (.more p tail) start f (tableTree Bt κ hκ D (.more p tail) o start) injective
      refine ⟨?_, ?_⟩
      · have hh := hread ⟨start, T.1.in_range⟩ le_rfl
        change Reads D u start (levelFrom (.more p tail) P T c ⟨start, T.1.in_range⟩ le_rfl) at hh
        rw [levelFrom_head] at hh
        exact origin_of_reads Bt κ hκ D u start o.1 c.1 f.2.1 r.1 hr.1 hrow hlocal hh
      · obtain ⟨hpos, hfollow⟩ := htail c.1
        have hdiv : 0 < ph.divisor := by
          by_contra! hz
          have hp := X.positions_pos
          rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hpos
          omega
        have hpos' : X.positions / ph.divisor = (p.next c.1).positions := by
          rw [hpos, Nat.mul_comm, Nat.mul_div_cancel _ hdiv]
        have hlanes' : g - ph.laneLoss = g' := by omega
        apply ih c.1 (o.2 c.1) c.2 (start + 1) (f.2.2 c.1) (injective.2 c.1) (r.2 c.1) (hr.2 c.1) xs hfollow
        · exact fun ph hp => hLoss ph (List.mem_cons_of_mem _ hp)
        · intro j
          have hj := hrows (j + 1)
          have hindex : start + (j + 1) = (start + 1) + j := by omega
          simpa only [hindex, layoutRows, List.getElem?_cons_succ, hpos', hlanes'] using hj
        · exact (Nat.mul_le_mul_left _
            ((Nat.succ_le_succ (hr.1 c.1).2.2).trans (hr.1 c.1).2.1)).trans_lt hbudget
        · intro ℓ hℓ
          have hh := hread ℓ (Nat.le_of_succ_le hℓ)
          change Reads D u ℓ.val (levelFrom (.more p tail) P T c ℓ (Nat.le_of_succ_le hℓ)) at hh
          rw [levelFrom_tail P T c ℓ hℓ] at hh
          exact hh

private theorem reads_of_sections {D : Dims} {u : List Bool} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (q : C.Tup d)
    (hs : ∀ s < D.nSec, ∀ i < D.count s, (dec D u).val D s i = (ofTuple R q).val D s i)
    (ℓ : Fin (D.top + 1)) : Reads D u ℓ.val (R.level q.1 q.2.1 ℓ) := by
  intro k i hi
  have hℓ := Nat.le_of_lt_succ ℓ.isLt
  have hi' : i < D.count (secLev ℓ.val k) := by
    rw [D.count_secLev k hℓ]
    exact hi
  have h := hs _ (D.secLev_lt_nSec k hℓ) i hi'
  rw [dec_val D u hi'] at h
  simpa only [Fields.val, D.kind_secLev k hℓ, ofTuple_levVal R q _ k i hi,
    levelAt, dite_eq_left ℓ.isLt] using h

variable [Algebra (ZMod 2) F]

private theorem fixed_branch (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) :
    BranchExtrasTarget Bt κ hκ V a b x d bigBias termBias := by
  intro hH hfit q
  let t := lpTime a b x.length
  let T := P1Wrap.Params.T (portConsts Bt) t
  let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  let X := routedState (S := S) V (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t) q.1
  let E := Bt.execute κ hκ T hn X
  let o := executeOrigins Bt κ hκ T hn X
  let D := fixedDims Bt V a b x d bigBias termBias
  let H := trueH Bt κ hκ V a b x d bigBias termBias hH
  let u := List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias H q)
  have f : ExecFits D E 0 := hH.1.choose_spec.choose_spec.2.1 q.1
  have hinj : TablesInjective D E 0 (tableTree Bt κ hκ D E o 0) := hH.2 q.1
  have hr : E.Bounded Bt.recordLimit (Bt.records κ hκ T hn X) :=
    (Procedure.repeat_recordBounds (Bt.recordBounds κ hκ) _ T (P1Wrap.Params.h t)
      (Nat.add_sub_of_le hn).symm X).1
  change P1SolCone.SolCone.BranchExtras Bt κ hκ D u E o q.2.1 0
  apply branch_of_reads Bt κ hκ D u E o q.2.1 0 f hinj _ hr (runPhases S T)
  · exact follows_execute Bt κ hκ T hn X
  · exact run_laneLoss (S := S) T
  · intro j
    have hpos : X.positions = initialPositions (toOAI V) 1 t :=
      P1Net.rn_positions (toOAI V) (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t) q.1 (four_le_baseDegree S)
    rw [Nat.zero_add, hpos]
    rfl
  · rw [runPhases_length]
    let W := P1Net.tupWidth (toOAI V) (P1Wrap.Params.B t)
    let M := Bt.growthConstant ^ T * (W + 1)
    have hw : X.maxWireWidth ≤ W := initial_width_le (toOAI V) 1 (four_le_baseDegree S) q.1
    have hpow : Bt.recordLimit ^ ((S.steps + 1) * T) ≤ Bt.growthConstant ^ T := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (le_max_right _ _) _
    have hM := Nat.mul_le_mul hpow (Nat.succ_le_succ hw)
    have hclog : M + 1 ≤ 2 ^ Nat.clog 2 (M + 1) := Nat.le_pow_clog (by decide) _
    have hD : 2 ^ Nat.clog 2 (M + 1) ≤ 2 ^ D.wW :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact hM.trans_lt ((Nat.lt_succ_self _).trans_le (hclog.trans hD))
  · intro ℓ _
    let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
    have hs := secEq_enc Bt κ hκ V a b x d bigBias termBias H hfit q
    exact reads_of_sections (u := u) R q hs ℓ

end P1Int.P11.SolWLink

theorem P1Int.P11.branchExtras_true {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type}
    [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) :
    P1Int.P11.BranchExtrasTarget Bt κ hκ V a b x d bigBias termBias :=
  P1Int.P11.SolWLink.fixed_branch Bt κ hκ V a b x d bigBias termBias

#print axioms P1Int.P11.branchExtras_true
