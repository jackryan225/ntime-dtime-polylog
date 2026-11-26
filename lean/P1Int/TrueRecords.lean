import P1Int.TrueRecordsDefs
import P1ChkGreedy.Bind
import P1P7.RefreshLocal
import OAI.Computability.VPVNP.CompressorExecutionLevels

/-!
True panel values and term tables for the routed compressor execution. The pass origins
identify which checker formulas to use. Injectivity follows by reading the numbered
addresses and coordinates back within the bounds of the scheduled rows.
-/

namespace P1Int
namespace SolTrueRecords

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open CompressorRecords P1Wit P1Wit.SolWitfill P1Int.P11

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
variable {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

def fieldValue (w v : ℕ) : Fin (2 ^ w) :=
  letI : NeZero (2 ^ w) := ⟨Nat.ne_of_gt (Nat.two_pow_pos _)⟩
  Fin.ofNat _ v

def zeroPanel (D : Dims) (ℓ : ℕ) : PanelVals D ℓ :=
  ⟨false, fun _ => fieldValue _ 0, fun _ => fieldValue _ 0, fun _ => fieldValue _ 0⟩

def baseValue {a g : ℕ} (X : State a g) (v : X.Base → ℕ) (i : ℕ) : ℕ :=
  if h : i < Fintype.card X.Base then v (X.baseIndex.symm ⟨i, h⟩) else 0

def panelAt (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass F X b n} (origin : PassOrigin Bt κ hκ p) :
    p.step.Choice → PanelVals D ℓ := by
  cases origin with
  | shrink i h X =>
    subst h
    intro s
    exact {
      layout := P1P7.layoutBit Bt.shrink X s
      colour := fun y => fieldValue _ (baseValue X (fun z => (X.packingData.color z).val) y.val)
      offset := fun y => fieldValue _ (baseValue X
        (fun z => (bitWordFinEquiv _ (X.packingData.offset z)).val) y.val)
      energy := fun j => fieldValue _ (baseValue X (fun z =>
        P1ChkGreedy.truePrefix X (P1ChkGreedy.termW Bt.shrink X s) z (j.val % 2 == 0)) (j.val / 2)) }
  | refresh X => exact fun _ => zeroPanel D ℓ

/-- Read a function at a numbered index, returning the default outside its image. -/
def readNumbered {A : Type} {C : Type} (number : A → ℕ) (f : A → C)
    (default : C) (j : ℕ) : C := by
  classical
  exact if h : ∃ x, number x = j then f h.choose else default

/-- Store the presence flag as an option and number the coordinates of each present term.
Unused slots are empty, and any unused coordinates of a present slot are zero. -/
def numberedTerms {A I : Type} (D : Dims) (ℓ : ℕ) (address : A → ℕ) (entry : I → ℕ)
    (terms : A → Option (I → ℕ)) : TermTableN D ℓ :=
  fun j => (readNumbered address terms none j.val).map fun v p =>
    fieldValue _ (readNumbered entry v 0 p.val)

def shrinkAddress {a g : ℕ} (X : State a (packingLaneBits a g)) (numKeys : ℕ)
    (e : P1ChkGreedy.OldArc X) : ℕ :=
  (P1ChkGreedy.arcKey X e).1 * numKeys + (P1ChkGreedy.arcKey X e).2

def refreshAddress {a g : ℕ} (X : State a (a + g)) (numKeys : ℕ) (s : X.Base × BitWord g) : ℕ :=
  P1P7.addr X s.1 * numKeys + (bitWordFinEquiv g s.2).val

def tableAt (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass F X b n} (origin : PassOrigin Bt κ hκ p) :
    p.step.Choice → TermTableN D ℓ := by
  cases origin with
  | shrink i h X =>
    subst h
    exact fun s => numberedTerms D ℓ (shrinkAddress X (D.lv ℓ).termKeys)
      P1ChkGreedy.termIdx (P1ChkGreedy.trueTerms Bt.shrink X s)
  | refresh X =>
    exact fun c => numberedTerms D ℓ (refreshAddress X (D.lv ℓ).termKeys)
      (fun (j, h) => j.val * (2 ^ S.expanderExponent) + h.val)
      (P1ChkGreedy.trueBlockTerms S.graph (Nat.two_pow_pos _)
        (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh X c)

def panelTree (D : Dims) {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) :
    PassOrigins Bt κ hκ E → (ℓ : ℕ) → PanelSupply D E ℓ :=
  match E with
  | .done _ => fun _ ℓ => zeroPanel D ℓ
  | .more _ tail => fun o ℓ => ⟨panelAt Bt κ hκ D ℓ o.1,
      fun i => panelTree D (tail i) (o.2 i) (ℓ + 1)⟩

def tableTree (D : Dims) {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) :
    PassOrigins Bt κ hκ E → (ℓ : ℕ) → TableSupply D E ℓ :=
  match E with
  | .done _ => fun _ _ => PUnit.unit
  | .more _ tail => fun o ℓ => ⟨tableAt Bt κ hκ D ℓ o.1,
      fun i => tableTree D (tail i) (o.2 i) (ℓ + 1)⟩

theorem fieldValue_val {w v : ℕ} (h : v < 2 ^ w) : (fieldValue w v).val = v :=
  Nat.mod_eq_of_lt h

theorem readNumbered_at {A C : Type} {number : A → ℕ} (hinj : Function.Injective number)
    (f : A → C) (default : C) (a : A) :
    readNumbered number f default (number a) = f a := by
  unfold readNumbered
  have h : ∃ x, number x = number a := ⟨a, rfl⟩
  rw [dite_eq_left h, hinj h.choose_spec]

theorem numberedTerms_injective {A I : Type} (D : Dims) (ℓ : ℕ)
    (address : A → ℕ) (entry : I → ℕ)
    (ha : Function.Injective address) (hi : Function.Injective entry)
    (hab : ∀ e, address e < (D.lv ℓ).bases * (D.lv ℓ).termKeys)
    (hib : ∀ p, entry p < (D.lv ℓ).termArity)
    {terms terms' : A → Option (I → ℕ)}
    (hfit : ∀ e v, terms e = some v → ∀ p, v p < 2 ^ D.wW)
    (hfit' : ∀ e v, terms' e = some v → ∀ p, v p < 2 ^ D.wW)
    (heq : numberedTerms D ℓ address entry terms = numberedTerms D ℓ address entry terms') :
    terms = terms' := by
  funext e
  have hf := congrFun heq ⟨address e, hab e⟩
  change (readNumbered address terms none (address e)).map _ =
    (readNumbered address terms' none (address e)).map _ at hf
  rw [readNumbered_at ha, readNumbered_at ha] at hf
  cases ht : terms e with
  | none =>
    cases ht' : terms' e with
    | none => rfl
    | some v => simp only [ht, ht', Option.map_none, Option.map_some, reduceCtorEq] at hf
  | some v =>
    cases ht' : terms' e with
    | none => simp only [ht, ht', Option.map_none, Option.map_some, reduceCtorEq] at hf
    | some v' =>
      rw [ht, ht', Option.map_some, Option.map_some] at hf
      congr 1
      funext p
      have hn := congrArg Fin.val (congrFun (Option.some.inj hf) ⟨entry p, hib p⟩)
      change (fieldValue D.wW (readNumbered entry v 0 (entry p))).val =
        (fieldValue D.wW (readNumbered entry v' 0 (entry p))).val at hn
      rw [readNumbered_at hi, readNumbered_at hi, fieldValue_val (hfit e v ht p),
        fieldValue_val (hfit' e v' ht' p)] at hn
      exact hn

theorem packed_lt {x i n d : ℕ} (hx : x < n) (hi : i < d) : x * d + i < n * d := by
  calc
    x * d + i < x * d + d := Nat.add_lt_add_left hi _
    _ = (x + 1) * d := (Nat.succ_mul x d).symm
    _ ≤ n * d := Nat.mul_le_mul_right _ hx

theorem packed_eq {x y i j d : ℕ} (hi : i < d) (hj : j < d)
    (h : x * d + i = y * d + j) : x = y ∧ i = j := by
  have hd : 0 < d := Nat.zero_lt_of_lt hi
  constructor
  · have hdiv := congrArg (fun z => z / d) h
    rw [Nat.mul_comm x d, Nat.mul_comm y d, Nat.mul_add_div hd, Nat.mul_add_div hd,
      Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj, Nat.add_zero, Nat.add_zero] at hdiv
    exact hdiv
  · have hmod := congrArg (fun z => z % d) h
    rw [Nat.mul_comm x d, Nat.mul_comm y d, Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
    exact hmod

theorem shrinkKey_lt {a g : ℕ} (X : State a (packingLaneBits a g)) (e : P1ChkGreedy.OldArc X) :
    (P1ChkGreedy.arcKey X e).2 < 2 ^ packingLaneBits a g * 2 ^ a :=
  packed_lt (bitWordFinEquiv _ ((packingArcEquiv X.Base a g).symm e).2).isLt
    (((packingArcEquiv X.Base a g).symm e).1.2).isLt

theorem shrinkAddress_injective {a g : ℕ} (X : State a (packingLaneBits a g)) {keys : ℕ}
    (hk : 2 ^ packingLaneBits a g * 2 ^ a ≤ keys) :
    Function.Injective (shrinkAddress X keys) := by
  intro e e' he
  obtain ⟨hb, hk'⟩ := packed_eq ((shrinkKey_lt X e).trans_le hk) ((shrinkKey_lt X e').trans_le hk) he
  let q := packingArcEquiv X.Base a g
  apply q.symm.injective
  obtain ⟨hl, hs⟩ := packed_eq (q.symm e).1.2.isLt (q.symm e').1.2.isLt hk'
  exact Prod.ext (Prod.ext (X.baseIndex.injective (Fin.ext hb)) (Fin.ext hs))
    ((bitWordFinEquiv _).injective (Fin.ext hl))

theorem refreshAddress_injective {a g : ℕ} (X : State a (a + g)) {keys : ℕ} (hk : 2 ^ g ≤ keys) :
    Function.Injective (refreshAddress X keys) := by
  intro s s' h
  obtain ⟨hb, hl⟩ := packed_eq ((bitWordFinEquiv g s.2).isLt.trans_le hk)
    ((bitWordFinEquiv g s'.2).isLt.trans_le hk) h
  exact Prod.ext (X.baseIndex.injective (Fin.ext hb)) ((bitWordFinEquiv _).injective (Fin.ext hl))

theorem shrinkEntry_lt (p : Bool × Fin 4) : P1ChkGreedy.termIdx p < 8 := by
  rcases p with ⟨b, j⟩
  have hj := j.isLt
  cases b <;> simp only [P1ChkGreedy.termIdx, Bool.false_eq_true, ite_false, ite_true, Nat.zero_add] <;> omega

theorem shrinkEntry_injective : Function.Injective P1ChkGreedy.termIdx := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> cases c <;>
    simp only [P1ChkGreedy.termIdx, Bool.false_eq_true, ite_false, ite_true, Nat.zero_add] at h
  · exact Prod.ext rfl (Fin.ext h)
  · omega
  · omega
  · exact Prod.ext rfl (Fin.ext (Nat.add_left_cancel h))

theorem refreshEntry_injective {a dH : ℕ} :
    Function.Injective (fun (p : Fin (2 ^ a) × Fin dH) => p.1.val * dH + p.2.val) := by
  intro p q h
  obtain ⟨h₁, h₂⟩ := packed_eq p.2.isLt q.2.isLt h
  exact Prod.ext (Fin.ext h₁) (Fin.ext h₂)

open private Follows follows_execute levelDims levelDims_bases
  layoutRows shrinkPhase refreshPhase prefixPhases blockPhases runPhases runPhases_length
  from P1Wit.SpaceFacts

def isShrink {a g b n : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) : Bool :=
  match o with
  | .shrink _ _ _ => true
  | .refresh _ => false

theorem origin_lanes {a g b n : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) :
    g = (if isShrink Bt κ hκ o then packingLaneBits a 0 else a) + n := by
  cases o with
  | shrink i h X =>
    subst h
    exact (packingLaneBits_add _ _).symm
  | refresh X => rfl

theorem shrinkFieldFactor_le (i : Fin S.steps) : ShrinkMotif.fieldFactor Bt.shrink ≤ Bt.recordLimit := by
  have hstep : State.shrinkHistoryFactor Bt.shrink
      (S.degreeExponent i.castSucc) (S.degreeExponent i.succ) ≤ Bt.recordLimit :=
    (Finset.le_sup (f := fun j : Fin S.steps =>
      State.shrinkHistoryFactor Bt.shrink (S.degreeExponent j.castSucc) (S.degreeExponent j.succ))
      (Finset.mem_univ i)).trans <| (le_max_left _ _).trans (le_max_right _ _)
  refine le_trans ?_ hstep
  unfold State.shrinkHistoryFactor
  exact (le_max_right _ _).trans <| (Nat.le_succ _).trans (le_max_right _ _)

attribute [local instance] P1P7.instDecEqBase

theorem shrinkTerm_lt (D : Dims) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (s : X.ShrinkSelection Bt.shrink) (e : P1ChkGreedy.OldArc X) (v : Bool × Fin 4 → ℕ)
    (hv : P1ChkGreedy.trueTerms Bt.shrink X s e = some v) (j : Bool × Fin 4) :
    v j < 2 ^ D.wW := by
  by_cases hm : P1ChkGreedy.IsMotif X e
  · let m : X.packingData.Motif := ⟨e, hm⟩
    have hval : (s m).val = v := Option.some.inj ((P1ChkGreedy.trueTerms_motif Bt.shrink X s m).symm.trans hv)
    have he := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _)
      (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
      (fun e => X.width_le_maxWireWidth _) Bt.shrink m (s m)
    rw [← hval]
    exact ((he.2 j).1.trans (Nat.mul_le_mul_right _ (shrinkFieldFactor_le Bt i))).trans_lt hW
  · have hnone : P1ChkGreedy.trueTerms Bt.shrink X s e = none := by
      rw [P1ChkGreedy.trueTerms, dite_eq_right hm]
    rw [hnone] at hv
    cases hv

theorem tableAt_injective (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass F X b n} (o : PassOrigin Bt κ hκ p)
    (r : p.Records) (hrec : p.Bounded r Bt.recordLimit)
    (hrow : D.lv ℓ = levelDims S.expanderExponent a g X.positions (some (isShrink Bt κ hκ o)))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW) :
    Function.Injective (tableAt Bt κ hκ D ℓ o) := by
  have hbases : (D.lv ℓ).bases = Fintype.card X.Base := hrow ▸ levelDims_bases X _ _
  cases o with
  | shrink i h X =>
    subst h
    have hkeys : (D.lv ℓ).termKeys = 2 ^ packingLaneBits (S.degreeExponent i.castSucc) n *
        2 ^ S.degreeExponent i.castSucc := hrow ▸ rfl
    have harity : (D.lv ℓ).termArity = 8 := hrow ▸ rfl
    intro s s' heq
    apply P1ChkGreedy.trueTerms_injective Bt.shrink X
    apply numberedTerms_injective D ℓ _ _ (shrinkAddress_injective X hkeys.ge) shrinkEntry_injective
    · intro e
      apply packed_lt
      · rw [hbases]
        exact (X.baseIndex _).isLt
      · rw [hkeys]
        exact shrinkKey_lt X e
    · intro j
      rw [harity]
      exact shrinkEntry_lt j
    · exact shrinkTerm_lt Bt D i X hW s
    · exact shrinkTerm_lt Bt D i X hW s'
    · exact heq
  | refresh X =>
    let hdH := Nat.two_pow_pos S.expanderExponent
    let hc := (S.port_bound.connected_and_pos S.port_order).1
    let hd := S.degree_bounds.2
    have hkeys : (D.lv ℓ).termKeys = 2 ^ n := by
      rw [hrow]
      change 2 ^ (S.portExponent + n - S.portExponent) = 2 ^ n
      rw [Nat.add_sub_cancel_left]
    have harity : (D.lv ℓ).termArity = 2 ^ S.portExponent * 2 ^ S.expanderExponent := hrow ▸ rfl
    have hf (c : DyadicRefreshChoice X S.graph hdH hc Bt.refresh)
        (s : X.Base × BitWord n) (v : Fin (2 ^ S.portExponent) × Fin (2 ^ S.expanderExponent) → ℕ)
        (hv : P1ChkGreedy.trueBlockTerms S.graph hdH hc Bt.refresh X c s = some v)
        (j : Fin (2 ^ S.portExponent) × Fin (2 ^ S.expanderExponent)) : v j < 2 ^ D.wW := by
      have hval : (c s).val = v := Option.some.inj hv
      let Y := dyadicRefreshNext X S.graph hdH hc Bt.refresh S.port_order hd c
      let w := ((P1P7.nb S.graph hdH hc Bt.refresh S.port_order hd X c (s.1, j.1),
        refreshSlots hd (.inr (.inl j.2))), s.2)
      have hw : Y.width w = MotifConversion.supplyWidths Bt.refresh (P1ChkGreedy.blockW X s) (c s).val j :=
        P1P7.rwidth_int S.graph hdH hc Bt.refresh S.port_order hd X c s.1 j.1 j.2 s.2
      -- Each outer coordinate is a summand of the width of its corresponding refreshed wire.
      have hcoord : v j ≤ Y.maxWireWidth := by
        rw [← hval]
        refine le_trans ?_ (Y.width_le_maxWireWidth w)
        rw [hw]
        exact Nat.le_add_right _ _
      have hmax : Y.maxWireWidth + 1 ≤ Bt.recordLimit * (X.maxWireWidth + 1) :=
        (Nat.succ_le_succ (hrec c).2.2).trans (hrec c).2.1
      exact (hcoord.trans_lt hmax).trans hW
    intro c c' heq
    apply P1ChkGreedy.trueBlockTerms_injective S.graph hdH hc Bt.refresh X
    apply numberedTerms_injective D ℓ _ _ (refreshAddress_injective X hkeys.ge) refreshEntry_injective
    · intro s
      apply packed_lt
      · rw [hbases]
        exact (X.baseIndex s.1).isLt
      · rw [hkeys]
        exact (bitWordFinEquiv n s.2).isLt
    · intro j
      rw [harity]
      exact packed_lt j.1.isLt j.2.isLt
    · exact hf c
    · exact hf c'
    · exact heq

theorem prefix_laneLoss (j : ℕ) (hj : j ≤ S.steps) :
    ∀ ph ∈ prefixPhases S j hj, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent) := by
  induction j with
  | zero =>
    intro ph hph
    exact (List.not_mem_nil hph).elim
  | succ j ih =>
    intro ph hph
    rw [prefixPhases, List.mem_append, List.mem_singleton] at hph
    rcases hph with hph | rfl
    · exact ih _ ph hph
    · rfl

theorem run_laneLoss (T : ℕ) :
    ∀ ph ∈ runPhases S T, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent) := by
  induction T with
  | zero =>
    intro ph hph
    exact (List.not_mem_nil hph).elim
  | succ T ih =>
    intro ph hph
    rw [runPhases, blockPhases, List.mem_append, List.mem_append, List.mem_singleton] at hph
    rcases hph with (hph | rfl) | hph
    · exact prefix_laneLoss S.steps le_rfl ph hph
    · rfl
    · exact ih ph hph

theorem tree_injective (D : Dims) {a g b n : ℕ} {X : State a g}
    (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E) (ℓ : ℕ)
    (r : E.Records) (hr : E.Bounded Bt.recordLimit r) (xs : List P1Wit.SolSpace.Phase)
    (hphase : Follows E xs)
    (hLoss : ∀ ph ∈ xs, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent))
    (hrows : ∀ j, D.lv (ℓ + j) = ((layoutRows S X.positions g xs)[j]?).getD
      (levelDims S.expanderExponent 0 0 0 none))
    (hW : Bt.recordLimit ^ xs.length * (X.maxWireWidth + 1) < 2 ^ D.wW) :
    TablesInjective D E ℓ (tableTree Bt κ hκ D E o ℓ) := by
  induction E generalizing ℓ xs with
  | done =>
    exact True.intro
  | @more a g b' n' X p tail ih =>
    cases xs with
    | nil => exact hphase.elim
    | cons ph xs =>
      obtain ⟨hdeg, hlanes, htail⟩ := hphase
      -- The lane loss determines the pass kind since shrinking consumes strictly more than the degree exponent.
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
      -- Reserve one factor of recordLimit for each remaining pass.
      have hbudget : Bt.recordLimit ^ xs.length * (Bt.recordLimit * (X.maxWireWidth + 1)) < 2 ^ D.wW := by
        rwa [← Nat.mul_assoc, ← pow_succ]
      have hlocal : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW :=
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos hlim)).trans_lt hbudget
      refine ⟨tableAt_injective Bt κ hκ D ℓ o.1 r.1 hr.1 hrow hlocal, ?_⟩
      intro c
      obtain ⟨hpos, hfollow⟩ := htail c
      have hdiv : 0 < ph.divisor := by
        by_contra! hz
        have hp := X.positions_pos
        rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hpos
        omega
      have hpos' : X.positions / ph.divisor = (p.next c).positions := by
        rw [hpos, Nat.mul_comm, Nat.mul_div_cancel _ hdiv]
      have hlanes' : g - ph.laneLoss = n' := by omega
      apply ih c (o.2 c) (ℓ + 1) (r.2 c) (hr.2 c) xs hfollow
      · exact fun ph hp => hLoss ph (List.mem_cons_of_mem _ hp)
      · intro j
        have hj := hrows (j + 1)
        have hindex : ℓ + (j + 1) = (ℓ + 1) + j := by omega
        simpa only [hindex, layoutRows, List.getElem?_cons_succ, hpos', hlanes'] using hj
      · exact (Nat.mul_le_mul_left _
          ((Nat.succ_le_succ (hr.1 c).2.2).trans (hr.1 c).2.1)).trans_lt hbudget

end
end SolTrueRecords

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit.SolWitfill

/-- The layout, colour, offset and energy values of the routed execution. -/
noncomputable def trueSupply
    {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ)
    (σ : P1Wit.SolWitfill.RoutedSkeleton V (P1Wrap.Params.I 1 (P1Int.lpTime a b x.length))
      (P1Wrap.Params.h (P1Int.lpTime a b x.length))) :
    P1Int.P11.PanelSupply (P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
      (P1Int.P11.fixedExec Bt κ hκ V a b x σ) 0 :=
  SolTrueRecords.panelTree Bt κ hκ _ _ (CompressorRecords.executeOrigins Bt κ hκ _ _ _) 0

/-- The checker term tables at every pass and for each admitted choice in the routed execution. -/
noncomputable def trueTables
    {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ)
    (σ : P1Wit.SolWitfill.RoutedSkeleton V (P1Wrap.Params.I 1 (P1Int.lpTime a b x.length))
      (P1Wrap.Params.h (P1Int.lpTime a b x.length))) :
    P1Int.P11.TableSupply (P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
      (P1Int.P11.fixedExec Bt κ hκ V a b x σ) 0 :=
  SolTrueRecords.tableTree Bt κ hκ _ _ (CompressorRecords.executeOrigins Bt κ hκ _ _ _) 0

open P1Wit P1Wit.SolSpace P1Wrap
open private follows_execute levelDims layoutRows runPhases runPhases_length from P1Wit.SpaceFacts

/-- The genuine table widths preserve each admitted coordinate, so the tables separate choices at every node. -/
theorem trueTables_injective
    {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) :
    1 ≤ b → ∃ n₂ : ℕ, ∀ x : List Bool, n₂ ≤ x.length →
      ∀ σ : P1Wit.SolWitfill.RoutedSkeleton V (P1Wrap.Params.I 1 (P1Int.lpTime a b x.length))
        (P1Wrap.Params.h (P1Int.lpTime a b x.length)),
      P1Int.P11.TablesInjective (P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
        (P1Int.P11.fixedExec Bt κ hκ V a b x σ) 0 (P1Int.P11.trueTables Bt κ hκ V a b x d bigBias termBias σ) := by
  intro _
  refine ⟨0, ?_⟩
  intro x _ σ
  let t := P1Int.lpTime a b x.length
  let T := Params.T (portConsts Bt) t
  let hn : T * S.laneBits ≤ Params.h t := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  let X := routedState (S := S) V (Params.B t) (Params.I 1 t) σ
  let E := Bt.execute κ hκ T hn X
  let D := fixedDims Bt V a b x d bigBias termBias
  change TablesInjective D E 0 (SolTrueRecords.tableTree Bt κ hκ D E
    (CompressorRecords.executeOrigins Bt κ hκ T hn X) 0)
  have hrec : E.Bounded Bt.recordLimit (Bt.records κ hκ T hn X) :=
    (Procedure.repeat_recordBounds (Bt.recordBounds κ hκ) _ T (Params.h t) (Nat.add_sub_of_le hn).symm X).1
  apply SolTrueRecords.tree_injective Bt κ hκ D E _ 0 _ hrec (runPhases S T)
  · exact follows_execute Bt κ hκ T hn X
  · exact SolTrueRecords.run_laneLoss (S := S) T
  · intro j
    have hpos : X.positions = initialPositions (toOAI V) 1 t :=
      P1Net.rn_positions (toOAI V) (Params.B t) (Params.I 1 t) σ (four_le_baseDegree S)
    rw [Nat.zero_add, hpos]
    rfl
  · rw [runPhases_length]
    let W := P1Net.tupWidth (toOAI V) (Params.B t)
    let M := Bt.growthConstant ^ T * (W + 1)
    have hw : X.maxWireWidth ≤ W := initial_width_le (toOAI V) 1 (four_le_baseDegree S) σ
    have hpow : Bt.recordLimit ^ ((S.steps + 1) * T) ≤ Bt.growthConstant ^ T := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (le_max_right _ _) _
    have hM := Nat.mul_le_mul hpow (Nat.succ_le_succ hw)
    have hclog : M + 1 ≤ 2 ^ Nat.clog 2 (M + 1) := Nat.le_pow_clog (by decide) _
    have hD : 2 ^ Nat.clog 2 (M + 1) ≤ 2 ^ D.wW :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact hM.trans_lt ((Nat.lt_succ_self _).trans_le (hclog.trans hD))

end P11
end P1Int

-- Small-case checks.

section

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh
open CompressorRecords P1Int.P11 P1Int.SolTrueRecords P1Wit

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
variable {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

example {a g : ℕ} (X : State a g) (D : Dims) (ℓ : ℕ) :
    panelTree Bt κ hκ D (.done X) PUnit.unit ℓ = zeroPanel D ℓ ∧
    tableTree Bt κ hκ D (.done X) PUnit.unit ℓ = PUnit.unit :=
  ⟨rfl, rfl⟩

example {a g : ℕ} (X : State a g) (h : Fintype.card X.Base = 1) : False := by
  let : Subsingleton X.Base := Fintype.card_le_one_iff_subsingleton.mp h.le
  let y := Classical.arbitrary X.Base
  let i : Fin (2 ^ a) := ⟨0, Nat.two_pow_pos _⟩
  exact X.slots.base.ends_ne (y, i) (Subsingleton.elim _ _)

example {g : ℕ} (X : State S.portExponent (S.portExponent + g)) (D : Dims) (ℓ : ℕ)
    (s : X.Base × BitWord g) (hkeys : 2 ^ g ≤ (D.lv ℓ).termKeys)
    (hslot : refreshAddress X (D.lv ℓ).termKeys s < (D.lv ℓ).bases * (D.lv ℓ).termKeys) :
    let p := dyadicRefreshPass X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      Bt.refresh S.port_order S.degree_bounds.2 (κ ∘ Sum.inr) ((Bt.solution_iff κ).mp hκ).2
    let E : StateExecution F (S.degreeExponent 0) g X := .more p (fun c => .done (p.next c))
    let o : PassOrigins Bt κ hκ E := ⟨.refresh X, fun _ => PUnit.unit⟩
    ∀ c : p.step.Choice,
      (tableTree Bt κ hκ D E o ℓ).1 c ⟨refreshAddress X (D.lv ℓ).termKeys s, hslot⟩ =
        some (fun j => fieldValue D.wW
          (readNumbered (fun (p : Fin (2 ^ S.portExponent) × Fin (2 ^ S.expanderExponent)) =>
              p.1.val * 2 ^ S.expanderExponent + p.2.val) (c s).val 0 j.val)) := by
  dsimp only [tableTree, tableAt, numberedTerms]
  intro c
  rw [readNumbered_at (refreshAddress_injective X hkeys)]
  rfl

end
