import P1P5.KernelWriter
import P1P7.SolRKernel
import P1ChkFinal.C10RcRefreshRead
import OAI.Computability.VPVNP.CursorLanes

section

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifSelector
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.PairSimulation.LocalHistory
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH
open P1P7 P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open scoped Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

namespace P1ProgEng.SolKWR

variable {U A : Type} [Codec U] [Codec A]

private abbrev regime (U : Type) [Codec U] : Strip.Regime U := ⟨size, send, Dom.base _⟩

private theorem figure {f : U → ℕ} (h : Poly f) : Carry.Figure (regime U) f :=
  ⟨fun u => binary (f u), h, fun _ => value_binary _⟩

theorem poly_tallyMin {n b : U → ℕ} (hn : Poly n) (hb : Poly b) (hc : Dom size b) :
    Poly (fun u => tally (min (n u) (b u))) := by
  have fn := figure hn
  have fb := figure hb
  have fmin : Carry.Figure (regime U) (fun u => min (n u) (b u)) := by
    convert fn.variant fb (fn.compare_ fb) using 1
    funext u
    split <;> omega
  exact fmin.pay (hc.mono fun u => min_le_right _ _)

theorem length_dom {f : U → List A} (hf : Poly f) :
    Dom size (fun u => (f u).length) := by
  have h : Poly (fun u => ruler (f u)) := hf.compose (Easy.ruler Easy.identity).poly
  exact h.length.mono (fun u => by rw [size_tally, ruler_length]; omega)

theorem poly_tallyCap {n : U → ℕ} {f : U → List A}
    (C : ℕ) (hn : Poly n) (hf : Poly f) :
    Poly (fun u => tally (min (n u) (C * (f u).length))) :=
  poly_tallyMin hn (poly_mulNat (poly_const C) (poly_lengthNat hf))
    ((Dom.const size C).mul (length_dom hf))

theorem poly_take {n : U → ℕ} {f : U → List A} (hn : Poly n) (hf : Poly f) :
    Poly (fun u => (f u).take (n u)) := by
  have h := ((poly_tallyMin hn (poly_lengthNat hf) (length_dom hf)).pair hf).compose
    (easy_cut Easy.identity).fstCompose.poly
  convert h using 1
  funext u
  simp only [cutLists, id_eq, tally_length]
  by_cases h : n u ≤ (f u).length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

theorem poly_drop {n : U → ℕ} {f : U → List A} (hn : Poly n) (hf : Poly f) :
    Poly (fun u => (f u).drop (n u)) := by
  have h := ((poly_tallyMin hn (poly_lengthNat hf) (length_dom hf)).pair hf).compose
    (easy_cut Easy.identity).sndCompose.poly
  convert h using 1
  funext u
  simp only [cutLists, id_eq, tally_length]
  by_cases h : n u ≤ (f u).length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

theorem poly_wordEq {f g : U → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun u => decide (f u = g u)) :=
  (hf.pair hg).compose (MotifFields.listEq_poly Bool)

theorem poly_bank {I : Type} [Fintype I] (f : I → U → A) (h : ∀ i, Poly (f i)) :
    Poly (fun u => MotifFields.bank (fun i => f i u)) :=
  poly_fixedTab _ (fun i => h ((Fintype.equivFin I).symm i))

theorem bank_congr {I A : Type} {f g : I → A} {i₁ i₂ : Fintype I} (h : ∀ i, f i = g i) :
    @MotifFields.bank I A i₁ f = @MotifFields.bank I A i₂ g := by
  rw [funext h, Subsingleton.elim i₁ i₂]

theorem ofFn_heq {n m : ℕ} {f : Fin n → Bool} {g : Fin m → Bool}
    (e : HEq f g) : List.ofFn f = List.ofFn g := by
  have hn : n = m := by
    have ht := type_eq_of_heq e
    have hh := congrArg (fun T : Type => Nat.card T) ht
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.pow_right_inj (by decide : 1 < 2)] using hh
  subst m
  rw [eq_of_heq e]

abbrev HalfCode := List (List Bool) × List (List Bool)

def wordAt (q : HalfCode) (out : Bool) (i : ℕ) : List Bool :=
  readAt [] (if out then q.1 else q.2) i

@[fun_prop] theorem poly_wordAt {q : U → HalfCode} {i : U → ℕ} (out : Bool)
    (hq : Poly q) (hi : Poly i) : Poly (fun u => wordAt (q u) out (i u)) := by
  cases out
  · exact poly_readAt [] hq.sndCompose hi
  · exact poly_readAt [] hq.fstCompose hi

def oldCode (u : RefreshKIn) : HalfCode := (readAt default u.2.1 0).2

@[fun_prop] theorem poly_oldCode : Poly oldCode :=
  (poly_readAt default (by fun_prop) (poly_const 0)).sndCompose

def frameLane (u : RefreshKIn) : RefreshFrame × ℕ := (u.1.1, u.1.2.2)

@[fun_prop] theorem poly_frameLane : Poly frameLane := by unfold frameLane; fun_prop

section Segments
variable {a a₀ dH : ℕ}

def outProfileCode (j i : Fin (2 ^ a)) (v : RefreshFrame × ℕ) : ℕ :=
  widthAt v.1 0 j.val (fullLane v.1 i.val v.2)

def inProfileCode (j i : Fin (2 ^ a)) (v : RefreshFrame × ℕ) : ℕ :=
  let e := (rowAt v.1 0 j.val).2.1
  let l := (v.2 ^^^ e.2.1) % laneCount v.1
  widthAt v.1 (inPos a j) e.2.2 (fullLane v.1 i.val l)

def inPortCode (j i : Fin (2 ^ a)) (v : RefreshFrame × ℕ) : ℕ :=
  let e := (rowAt v.1 0 j.val).2.1
  (fullLane v.1 i.val v.2 ^^^ e.2.1) / laneCount v.1

theorem poly_outProfileCode (j i : Fin (2 ^ a)) : Poly (outProfileCode j i) := by
  unfold outProfileCode
  fun_prop

theorem poly_inProfileCode (j i : Fin (2 ^ a)) : Poly (inProfileCode j i) := by
  unfold inProfileCode
  fun_prop

theorem poly_inPortCode (j i : Fin (2 ^ a)) : Poly (inPortCode j i) := by
  unfold inPortCode
  fun_prop

def listSlice {n : ℕ} (w : Fin n → ℕ) (p : Fin n) (xs : List Bool) : List Bool :=
  (xs.drop (∑ i : Fin p.val, w (Fin.castLE p.isLt.le i))).take (w p)

theorem poly_listSlice {n : ℕ} {w : Fin n → U → ℕ} {xs : U → List Bool}
    (p : Fin n) (hw : ∀ i, Poly (w i)) (hxs : Poly xs) :
    Poly (fun u => listSlice (fun i => w i u) p (xs u)) :=
  poly_take (hw p) (poly_drop (poly_fixedSum _ (fun i => hw (Fin.castLE p.isLt.le i))) hxs)

variable (hd : dH + 1 ≤ 2 ^ a₀)

def segCode (j i : Fin (2 ^ a)) (out : Bool) (u : RefreshKIn) : List Bool :=
  let v := frameLane u
  let xs := wordAt u.2.2 out (refreshSlots hd (.inl 0)).val
  if out then listSlice (fun p => outProfileCode j p v) i xs
  else readAt [] (List.ofFn fun p => listSlice (fun q => inProfileCode j q v) p xs)
    (inPortCode j i v)

theorem poly_segCode (j i : Fin (2 ^ a)) (out : Bool) : Poly (segCode hd j i out) := by
  have hword : Poly (fun u : RefreshKIn => wordAt u.2.2 out (refreshSlots hd (.inl 0)).val) :=
    poly_wordAt out (by fun_prop) (poly_const _)
  cases out
  · exact poly_readAt [] (poly_fixedTab _ (fun p =>
      poly_listSlice p (fun q => poly_frameLane.compose (poly_inProfileCode j q)) hword))
      (poly_frameLane.compose (poly_inPortCode j i))
  · exact poly_listSlice i (fun p => poly_frameLane.compose (poly_outProfileCode j p)) hword

def passes (j : Fin (2 ^ a)) (u : RefreshKIn) : Bool :=
  decide (wordAt (oldCode u) true j.val = segCode hd j j true u) &&
  decide (wordAt (oldCode u) false j.val = segCode hd j j false u)

theorem poly_passes (j : Fin (2 ^ a)) : Poly (passes hd j) := by
  have test (out : Bool) := poly_wordEq (poly_wordAt out poly_oldCode (poly_const j.val))
    (poly_segCode hd j j out)
  exact ((test true).pair (test false)).compose (Easy.finite (fun b : Bool × Bool => b.1 && b.2)).poly

end Segments

section Writer
variable {a a₀ dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hd : dH + 1 ≤ 2 ^ a₀)

local notation "S" => expanderSupply P hdH hconn

def demandWord (j : Fin (2 ^ a)) (p : MotifFields.Ends tieSource tieTarget j)
    (u : RefreshKIn) : List Bool :=
  match p with
  | .inl t => wordAt (oldCode u) t.val.1 (tieTarget t.val).val
  | .inr t => segCode hd j (tieSource t.val) t.val.1 u

theorem poly_demandWord (j : Fin (2 ^ a)) (p : MotifFields.Ends tieSource tieTarget j) :
    Poly (demandWord hd j p) := by
  cases p with
  | inl t => exact poly_wordAt _ poly_oldCode (poly_const _)
  | inr t => exact poly_segCode hd j _ _

def supplyWord (j : Fin (2 ^ a)) (p : MotifFields.Port S j) (u : RefreshKIn) : List Bool :=
  match p with
  | .inl e => wordAt u.2.2 true (refreshSlots hd (.inr (.inl e.val.2))).val
  | .inr e => wordAt u.2.2 false (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e.val).2))).val

theorem poly_supplyWord (j : Fin (2 ^ a)) (p : MotifFields.Port S j) :
    Poly (supplyWord P hdH hconn hd j p) := by
  cases p
  · exact poly_wordAt true (by fun_prop) (poly_const _)
  · exact poly_wordAt false (by fun_prop) (poly_const _)

def anchorWord (u : RefreshKIn) : List Bool :=
  wordAt u.2.2 true (refreshSlots hd (.inr (.inl ⟨0, hdH⟩))).val

theorem poly_anchorWord : Poly (anchorWord hdH hd) :=
  poly_wordAt true (by fun_prop) (poly_const _)

def widthTally (C : ℕ) (t : Tie (2 ^ a)) (u : RefreshKIn) : Tally :=
  tally (min (tieCell a t u.1.1 u.1.2.2) (C * (anchorWord hdH hd u).length))

def payloadTally (C : ℕ) (e : Fin (2 ^ a) × Fin dH) (u : RefreshKIn) : Tally :=
  tally (min (termAt u.1.1 u.1.2.2 e.1.val e.2.val) (C * (anchorWord hdH hd u).length))

theorem poly_widthTally (C : ℕ) (t : Tie (2 ^ a)) : Poly (widthTally hdH hd C t) :=
  poly_tallyCap C (poly_frameLane.compose (poly_tieCell t)) (poly_anchorWord hdH hd)

theorem poly_payloadTally (C : ℕ) (e : Fin (2 ^ a) × Fin dH) : Poly (payloadTally hdH hd C e) :=
  poly_tallyCap C (by fun_prop) (poly_anchorWord hdH hd)

def fixedCode (C : ℕ) (j : Fin (2 ^ a)) (u : RefreshKIn) : MotifFields.FixedInput (Fin (2 ^ a)) :=
  (((MotifFields.bank (fun t : Tie (2 ^ a) => widthTally hdH hd C t u), ⟨j⟩),
    MotifFields.bank (fun p => demandWord hd j p u)),
    MotifFields.bank (fun p => (supplyWord P hdH hconn hd j p u,
      payloadTally hdH hd C (MotifFields.edge S j p) u)),
    MotifFields.bank (fun e : Fin (2 ^ a) × Fin dH => payloadTally hdH hd C e u))

theorem poly_fixedCode (C : ℕ) (j : Fin (2 ^ a)) : Poly (fixedCode P hdH hconn hd C j) :=
  (((poly_bank _ (poly_widthTally (a := a) hdH hd C)).pair (poly_const (StackInterpreter.Label.mk j))).pair
    (poly_bank _ (poly_demandWord hd j))).pair
    ((poly_bank _ (fun p => (poly_supplyWord P hdH hconn hd j p).pair (poly_payloadTally hdH hd C _))).pair
      (poly_bank _ (poly_payloadTally (a := a) hdH hd C)))

def writerAt (C : ℕ) (j : Fin (2 ^ a)) (u : RefreshKIn) :
    List (List (MotifFields.FixedInput (Fin (2 ^ a)))) :=
  bif passes hd j u then [[fixedCode P hdH hconn hd C j u]] else []

theorem poly_writerAt (C : ℕ) (j : Fin (2 ^ a)) : Poly (writerAt P hdH hconn hd C j) := by
  have single {A : Type} [Codec A] : Poly (fun x : A => [x]) :=
    (Poly.identity.pair (poly_const ([] : List A))).compose Poly.cons
  exact Poly.choose (poly_passes hd j) ((poly_fixedCode P hdH hconn hd C j).compose
    (single.compose single)) (poly_const [])

def writer (C : ℕ) (u : RefreshKIn) : List (List (MotifFields.FixedInput (Fin (2 ^ a)))) :=
  readAt [] (List.ofFn fun j => writerAt P hdH hconn hd C j u) u.1.2.1

theorem poly_writer (C : ℕ) : Poly (writer P hdH hconn hd C) :=
  poly_readAt [] (poly_fixedTab _ (poly_writerAt P hdH hconn hd C)) (by fun_prop)

end Writer

section Bounds
open WireTensor
variable {a a₀ dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

local notation "S" => expanderSupply P hdH hconn

/-- The base identity needs a nontrivial selector: the zero supply profile alone
cannot realize a demand tensor with a positive off-diagonal width. -/
theorem selectorBits_pos (hD : 1 < 2 ^ a) : 0 < F.selectorBits := by
  by_contra! hz
  have hz' : F.selectorBits = 0 := Nat.eq_zero_of_le_zero hz
  let zero : F.grid.supplies := ⟨fun _ => 0, F.grid.zero_mem_supplies⟩
  let sel : Selector F := (⟨0, F.copyCount_pos⟩, fun _ => zero)
  have same (s : Selector F) : s = sel := by
    apply (selectorCode F).injective
    apply Fin.ext
    have h₁ := ((selectorCode F) s).isLt
    have h₂ := ((selectorCode F) sel).isLt
    have hpow : 2 ^ F.selectorBits = 1 := by rw [hz', pow_zero]
    have h₁' := h₁.trans_le hpow.le
    have h₂' := h₂.trans_le hpow.le
    clear h₁ h₂
    omega
  have hzero : basePayload F sel = fun _ => 0 := by
    funext e
    have h (i : Fin F.power) : F.grid.supplyWidths F.multiple (sel.2 i) e = 0 := by
      apply Nat.cast_injective (R := ℝ)
      rw [F.grid.cast_supplyWidths]
      change ((F.multiple * F.grid.denominator : ℕ) : ℝ) * ((0 : ℚ) : ℝ) = _
      simp only [Rat.cast_zero, mul_zero, Nat.cast_zero]
    simp only [basePayload, MotifBase.payload, h, Finset.sum_const_zero]
  let t : Tie (2 ^ a) := (true, ⟨(⟨0, Nat.two_pow_pos a⟩, ⟨1, hD⟩), by
    intro h
    have hh : (0 : ℕ) = 1 := congrArg Fin.val h
    exact Nat.zero_ne_one hh⟩)
  let grid := demandGrid F (fun _ => zero_lt_one) (fun _ => 1)
  let w := baseDemand F grid
  have hw : 0 < w t := by
    have h := demand_le F (fun _ => zero_lt_one) (fun _ => 1) t
    change 1 ≤ repetitions F (fun _ => 1) * w t at h
    by_contra! hwt
    rw [Nat.eq_zero_of_le_zero hwt, mul_zero] at h
    omega
  obtain ⟨L, hL⟩ := F.baseIdentity grid
  change (MotifBase.binaryWires (k := k) tieSource tieTarget w).coeff =
    ∑ s : Selector F, applyLocal (L s) (MotifBase.binaryWires (S).src (S).dst (basePayload F s)).coeff at hL
  rw [Finset.sum_eq_single sel] at hL
  · have hr : Restricts (MotifBase.binaryWires (k := k) (S).src (S).dst (basePayload F sel))
        (MotifBase.binaryWires tieSource tieTarget w) := ⟨L sel, hL.symm⟩
    let : Nontrivial (Fin (2 ^ a)) := Fin.nontrivial_iff_two_le.mpr hD
    let point := flatteningPoint (k := k) (tieSource t)
    have hle := point.monotone hr
    have hle' : (point.value (MotifBase.binaryWires tieSource tieTarget w) : ℝ) ≤
        (point.value (MotifBase.binaryWires (S).src (S).dst (basePayload F sel)) : ℝ) := hle
    rw [point.value_binary_wireNetwork, point.value_binary_wireNetwork, hzero] at hle'
    simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, Real.rpow_zero] at hle'
    have ht : point.wireDistance (tieSource t) (tieTarget t) = 1 := by
      have ht' : tieSource t ≠ tieTarget t := t.2.property
      simp only [point, flatteningPoint_wireDistance, ht', ne_eq, eq_self, not_true_eq_false,
        true_and, false_and, or_false, not_false_eq_true, ite_true]
    have hpos : 0 < ∑ e, (w e : ℝ) * point.wireDistance (tieSource e) (tieTarget e) := by
      apply Finset.sum_pos' (fun e _ => mul_nonneg (Nat.cast_nonneg _) (point.wireDistance_nonneg _ _))
      refine ⟨t, Finset.mem_univ _, ?_⟩
      rw [ht, mul_one]
      exact Nat.cast_pos.mpr hw
    exact (not_lt_of_ge hle') (Real.one_lt_rpow (by norm_num) hpos)
  · intro s _ hs
    exact (hs (same s)).elim
  · intro hs
    exact (hs (Finset.mem_univ _)).elim

-- One actual expander word bounds the repetition count, hence all unary fields.
def tallyFactor : ℕ :=
  max (∑ z : F.grid.demands, ∑ t, baseDemand F z t)
    (F.scale * (F.radius.num.natAbs * MotifAdmission.denominator
      (expanderMass (D := 2 ^ a) (dH := dH) (2 ^ a₀))))

theorem tally_bounds (hD : 1 < 2 ^ a) (w : Tie (2 ^ a) → ℕ) (v : Fin (2 ^ a) × Fin dH → ℕ)
    (hv : v ∈ outerIndices F w) (e : Fin (2 ^ a) × Fin dH) :
    (∀ t, w t ≤ tallyFactor P hdH hconn F * supplyWidths F w v e) ∧
    (∀ f, v f ≤ tallyFactor P hdH hconn F * supplyWidths F w v e) := by
  let C := tallyFactor P hdH hconn F
  have hr : repetitions F w ≤ supplyWidths F w v e :=
    (Nat.le_mul_of_pos_right _ (selectorBits_pos P hdH hconn F hD)).trans (Nat.le_add_left _ _)
  have hb (t : Tie (2 ^ a)) : baseDemand F (demandGrid F (fun _ => zero_lt_one) w) t ≤ C :=
    (Finset.single_le_sum (f := baseDemand F _) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)).trans
      ((Finset.single_le_sum (f := fun z => ∑ t, baseDemand F z t) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)).trans (le_max_left _ _))
  have hm (e : Fin (2 ^ a) × Fin dH) : 0 < expanderMass (D := 2 ^ a) (2 ^ a₀) e := by
    unfold expanderMass
    positivity
  have hadm := (mem_outerIndices_iff F hm w v).mp hv
  constructor
  · intro t
    rw [mul_comm C]
    exact (demand_le F (fun _ => zero_lt_one) w t).trans (Nat.mul_le_mul hr (hb t))
  · intro f
    rw [mul_comm C]
    apply (MotifAdmission.payload_le_cap _ hm _ _ _ _ hadm f).trans
    unfold MotifAdmission.payloadCap
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul hr (le_max_right _ _)

end Bounds

section Correctness
variable {a a₀ dH g : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
  (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
variable {R : Type} [CommRing R]

open SolRKernel

local notation "Z" => trueFrame P hdH hconn F X c x
local notation "V" => ((x, j), l)
local notation "Y₀" => dyadicRefreshNext X P hdH hconn F hD hd c
local notation "S" => expanderSupply P hdH hconn
local notation "OldPlaced" => Placed (placeEquiv X) X.network.Half V
local notation "NewHalf" => Network.Half (State.network Y₀) V
local notation "PlaceMatch" => PlacedList X (N' := State.network Y₀) (placeEquiv X) V
local notation "T[" m "," hm "]" => refreshTermAt X P hdH hconn F hD hd c m hm
local notation "u₀[" y "," qs "]" => refreshKIn P hdH hconn F hD hd g X c x j l qs y
local notation "q₀[" p "]" => placedSingle (placeEquiv X) V p
local notation "b₀[" y "]" => segments X P hdH hconn F hD hd c x j l y
local notation "h₀[" p "]" => oldPull X x j l (placedSingle (placeEquiv X) V p)

theorem wordAt_halfCode {a G : ℕ} (Y : State a G) (v : Y.network.Site) (z : Y.network.Half v)
    (s : Fin (2 ^ a)) :
    wordAt (halfCode Y v z) true s.val = List.ofFn (z.1 (outEdge Y v s) (outEdge_src Y v s)) ∧
    wordAt (halfCode Y v z) false s.val = List.ofFn (z.2 (inEdge Y v s) (inEdge_dst Y v s)) := by
  exact ⟨readAt_ofFn _ _ _, readAt_ofFn _ _ _⟩

theorem oldCode_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps) :
    oldCode (u₀[z, ps]) = halfCode X ((placeEquiv X).symm V) (q₀[pa]) := by
  obtain ⟨us, hn, hm, rfl⟩ := hp
  change List {p : X.network.Site // V = placeEquiv X p} at us
  let t : {p : X.network.Site // V = placeEquiv X p} :=
    ⟨(placeEquiv X).symm V, ((placeEquiv X).apply_symm_apply V).symm⟩
  have eq (p : {p : X.network.Site // V = placeEquiv X p}) : p = t :=
    Subtype.ext ((placeEquiv X).injective (p.property.symm.trans t.property))
  have hu : us = [t] := by
    cases us with
    | nil => cases hm t
    | cons p qs =>
      have hnp := (List.nodup_cons.mp hn).1
      obtain rfl := eq p
      cases qs with
      | nil => rfl
      | cons r rs => exact (hnp (List.mem_cons.mpr (Or.inl (eq r).symm))).elim
  rw [hu]
  rfl

theorem oldOut_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps) (i : Fin (2 ^ a)) :
    wordAt (oldCode (u₀[z, ps])) true i.val = List.ofFn ((h₀[pa]).1 (((x, l), i), j) rfl) := by
  rw [oldCode_true P hdH hconn F hD hd X c x j l pa z ps hp, (wordAt_halfCode _ _ _ i).1]
  exact (ofFn_heq (oldPull_out X x j l (q₀[pa]) i)).symm

theorem oldIn_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps) (i : Fin (2 ^ a)) :
    wordAt (oldCode (u₀[z, ps])) false i.val =
      List.ofFn (incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j i (h₀[pa])) := by
  rw [oldCode_true P hdH hconn F hD hd X c x j l pa z ps hp, (wordAt_halfCode _ _ _ i).2]
  exact (ofFn_heq (oldPull_in (R := ℤ) X x j l (q₀[pa]) i)).symm

theorem outProfile_true (i : Fin (2 ^ a)) :
    outProfileCode j i (Z, bwNum l) = outProfile X x j l i := by
  rw [outProfileCode, fullLane_true, root_width]
  rfl

theorem inProfile_true (i : Fin (2 ^ a)) :
    inProfileCode j i (Z, bwNum l) = inProfile X x j l i := by
  let d := (inData X x j).2.1
  have hrow := rowAt_root P hdH hconn F X c x j
  have hres := number_residue (oldLane (0 : Fin (2 ^ a)) l - d)
  rw [number_sub, number_oldLane, Fin.val_zero, zero_mul, zero_add, map_sub] at hres
  simp only [oldLane, AddEquiv.apply_symm_apply, Prod.snd_sub] at hres
  unfold inProfileCode
  dsimp only
  rw [hrow]
  change widthAt Z (inPos a j) (inData X x j).1.val
    (fullLane Z i.val ((bwNum l ^^^ bwNum d) % laneCount Z)) = _
  rw [laneCount_true, hres, fullLane_true, in_width]
  rfl

theorem inPort_true (i : Fin (2 ^ a)) :
    inPortCode j i (Z, bwNum l) = (inPort X x j l i).val := by
  let d := (inData X x j).2.1
  unfold inPortCode
  dsimp only
  rw [rowAt_root]
  change (fullLane Z i.val (bwNum l) ^^^ bwNum d) / laneCount Z = _
  rw [fullLane_true, ← number_sub, ← incomingLane]
  change bwNum (oldLane (inPort X x j l i) (l - (splitBitWord a g d).2)) / laneCount Z = _
  rw [number_oldLane, laneCount_true]
  rw [Nat.mul_comm (inPort X x j l i).val]
  exact (div_mod_prod (bitWordFinEquiv g (l - (splitBitWord a g d).2)).isLt).1

theorem listSlice_ofFn {n : ℕ} (w : Fin n → ℕ) (p : Fin n) (b : Refresh.Word (∑ i, w i)) :
    listSlice w p (List.ofFn b) = List.ofFn (slice w b p) := by
  let off := ∑ i : Fin p.val, w (Fin.castLE p.isLt.le i)
  have hoff (i : Fin (w p)) : (finSigmaFinEquiv (n := w) ⟨p, i⟩).val = off + i.val :=
    finSigmaFinEquiv_apply _
  have hlen : w p ≤ (∑ i, w i) - off := by
    by_cases h : w p = 0
    · simp only [h, Nat.zero_le]
    · let i : Fin (w p) := ⟨w p - 1, by omega⟩
      have hi := (finSigmaFinEquiv (n := w) ⟨p, i⟩).isLt
      rw [hoff] at hi
      change off + (w p - 1) < ∑ i, w i at hi
      omega
  change ((List.ofFn b).drop off).take (w p) = _
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn, min_eq_left hlen]
  · intro i hi hj
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
    unfold slice
    congr 1
    apply Fin.ext
    rw [hoff]

theorem segOut_true (z : NewHalf) (ps : List PosCode) (i : Fin (2 ^ a)) :
    segCode hd j i true (u₀[z, ps]) = List.ofFn ((b₀[z]).1 i) := by
  have hw := (wordAt_halfCode Y₀ V z (refreshSlots hd (.inl 0))).1
  have hz := (ofFn_heq (outWord_slot X P hdH hconn F hD hd c x j l z)).symm
  change listSlice (fun p => outProfileCode j p (Z, bwNum l)) i
    (wordAt (halfCode Y₀ V z) true (refreshSlots hd (.inl 0)).val) = _
  rw [show (fun p => outProfileCode j p (Z, bwNum l)) = outProfile X x j l from
    funext (outProfile_true P hdH hconn F X c x j l), hw, hz, listSlice_ofFn]
  rfl

theorem segIn_true (z : NewHalf) (ps : List PosCode) (i : Fin (2 ^ a)) :
    segCode hd j i false (u₀[z, ps]) = List.ofFn ((b₀[z]).2 i) := by
  have hw := (wordAt_halfCode Y₀ V z (refreshSlots hd (.inl 0))).2
  have hz := (ofFn_heq (inWord_slot X P hdH hconn F hD hd c x j l z)).symm
  change readAt [] (List.ofFn fun p => listSlice (fun q => inProfileCode j q (Z, bwNum l)) p
    (wordAt (halfCode Y₀ V z) false (refreshSlots hd (.inl 0)).val)) (inPortCode j i (Z, bwNum l)) = _
  rw [show (fun q => inProfileCode j q (Z, bwNum l)) = inProfile X x j l from
    funext (inProfile_true P hdH hconn F X c x j l), hw, hz,
    inPort_true P hdH hconn F X c x j l i, readAt_ofFn, listSlice_ofFn]
  exact (ofFn_heq (segments_in X P hdH hconn F hD hd c x j l z i)).symm

theorem passes_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps) :
    passes hd j (u₀[z, ps]) = decide
      ((h₀[pa]).1 (((x, l), j), j) rfl = (b₀[z]).1 j ∧
        incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j j (h₀[pa]) = (b₀[z]).2 j) := by
  rw [passes, oldOut_true P hdH hconn F hD hd X c x j l pa z ps hp,
    oldIn_true P hdH hconn F hD hd X c x j l pa z ps hp,
    segOut_true P hdH hconn F hD hd X c x j l, segIn_true P hdH hconn F hD hd X c x j l]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.ofFn_inj]
  exact and_congr (@List.ofFn_inj Bool (widths X (((x, l), j), j))
    ((h₀[pa]).1 (((x, l), j), j) rfl) ((b₀[z]).1 j)) Iff.rfl

theorem inputBits_symm {n : ℕ} (v : Fin (2 ^ n)) :
    MotifEntry.inputBits v = (wordIndex n).symm v :=
  funext fun i => (CursorNetwork.addressWord_bit v i).symm

theorem inputBits_wordIndex {n : ℕ} (v : Refresh.Word n) :
    MotifEntry.inputBits (wordIndex n v) = v :=
  (inputBits_symm _).trans (Equiv.symm_apply_apply _ _)

def actualEntry (pa : OldPlaced) (z : NewHalf) : EntryInput F :=
  ⟨demand X (x, l), (c (x, l)).val, j,
    portInput (R := ℤ) (matching X) (widths X) (x, l) j (h₀[pa]) (b₀[z]),
    readSupply X P hdH hconn F hD hd c x j l z⟩

local notation "e₀[" p "," y "]" => actualEntry P hdH hconn F hD hd X c x j l p y
local notation "C" => tallyFactor P hdH hconn F

theorem demandWord_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps)
    (p : MotifFields.Ends tieSource tieTarget j) :
    let d := MotifEntry.demandBits tieSource tieTarget j (e₀[pa, z]).demandBits
    demandWord hd j p (u₀[z, ps]) =
      match p with
      | .inl t => List.ofFn (d.1 t.val t.property)
      | .inr t => List.ofFn (d.2 t.val t.property) := by
  cases p with
  | inl t =>
    rcases t with ⟨⟨out, ⟨⟨i, s⟩, his⟩⟩, h⟩
    change j = i at h
    subst i
    cases out
    · change wordAt (oldCode (u₀[z, ps])) false s.val = List.ofFn (MotifEntry.inputBits (wordIndex _
        (incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j s (h₀[pa]))))
      rw [inputBits_wordIndex]
      exact oldIn_true P hdH hconn F hD hd X c x j l pa z ps hp s
    · change wordAt (oldCode (u₀[z, ps])) true s.val = List.ofFn (MotifEntry.inputBits (wordIndex _
        ((h₀[pa]).1 (((x, l), s), j) rfl)))
      exact (oldOut_true P hdH hconn F hD hd X c x j l pa z ps hp s).trans
        (congrArg List.ofFn (inputBits_wordIndex (n := widths X (((x, l), s), j))
          ((h₀[pa]).1 (((x, l), s), j) rfl))).symm
  | inr t =>
    rcases t with ⟨⟨out, ⟨⟨i, s⟩, his⟩⟩, h⟩
    change j = s at h
    subst s
    cases out
    · change segCode hd j i false (u₀[z, ps]) = List.ofFn (MotifEntry.inputBits (wordIndex _ ((b₀[z]).2 i)))
      rw [inputBits_wordIndex]
      exact segIn_true P hdH hconn F hD hd X c x j l z ps i
    · change segCode hd j i true (u₀[z, ps]) = List.ofFn (MotifEntry.inputBits (wordIndex _ ((b₀[z]).1 i)))
      rw [inputBits_wordIndex]
      exact segOut_true P hdH hconn F hD hd X c x j l z ps i

theorem supplyWord_true (z : NewHalf) (ps : List PosCode) (p : MotifFields.Port S j) :
    supplyWord P hdH hconn hd j p (u₀[z, ps]) = List.ofFn
      (MotifFields.endpoint S j (mapHalf S (fun _ => MotifEntry.inputBits)
        (readSupply X P hdH hconn F hD hd c x j l z)) p) := by
  cases p with
  | inl e =>
    change wordAt (halfCode Y₀ V z) true (refreshSlots hd (.inr (.inl e.val.2))).val = _
    rw [(wordAt_halfCode Y₀ V z _).1]
    change _ = List.ofFn (MotifEntry.inputBits ((readSupply X P hdH hconn F hD hd c x j l z).1 e.val e.property))
    rw [inputBits_symm]
    exact (ofFn_heq (supplyOut_word X P hdH hconn F hD hd c x j l z e.val e.property)).symm
  | inr e =>
    change wordAt (halfCode Y₀ V z) false
      (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e.val).2))).val = _
    rw [(wordAt_halfCode Y₀ V z _).2]
    change _ = List.ofFn (MotifEntry.inputBits ((readSupply X P hdH hconn F hD hd c x j l z).2 e.val e.property))
    rw [inputBits_symm]
    exact (ofFn_heq (supplyIn_word X P hdH hconn F hD hd c x j l z e.val e.property)).symm

theorem anchorWord_length (z : NewHalf) (ps : List PosCode) :
    (anchorWord hdH hd (u₀[z, ps])).length = supplyWidth X P hdH hconn F c (x, l) (j, ⟨0, hdH⟩) := by
  change (wordAt (halfCode Y₀ V z) true (refreshSlots hd (.inr (.inl ⟨0, hdH⟩))).val).length = _
  rw [(wordAt_halfCode Y₀ V z _).1]
  exact congrArg List.length
    (ofFn_heq (supplyOut_word X P hdH hconn F hD hd c x j l z (j, ⟨0, hdH⟩) rfl)).symm |>.trans
      (by simp only [List.length_ofFn])

theorem fixedCode_true (pa : OldPlaced) (z : NewHalf) (ps : List PosCode)
    (hp : PlaceMatch pa ps) :
    fixedCode P hdH hconn hd C j (u₀[z, ps]) = MotifFields.fixedInput F (e₀[pa, z]) := by
  have hB := tally_bounds P hdH hconn F hD (demand X (x, l)) (c (x, l)).val
    (c (x, l)).property (j, ⟨0, hdH⟩)
  have hW (t : Tie (2 ^ a)) : widthTally hdH hd C t (u₀[z, ps]) = tally (((e₀[pa, z])).demand t) := by
    change tally (min (tieCell a t Z (bwNum l)) (C * (anchorWord hdH hd (u₀[z, ps])).length)) = _
    rw [tieCell_true, anchorWord_length P hdH hconn F hD hd X c x j l z ps, min_eq_left (hB.1 t)]
    rfl
  have hV (e : Fin (2 ^ a) × Fin dH) : payloadTally hdH hd C e (u₀[z, ps]) = tally (((e₀[pa, z])).payload e) := by
    change tally (min (termAt Z (bwNum l) e.1.val e.2.val) (C * (anchorWord hdH hd (u₀[z, ps])).length)) = _
    rw [termAt_true, anchorWord_length P hdH hconn F hD hd X c x j l z ps, min_eq_left (hB.2 e)]
    rfl
  have hDmd := demandWord_true P hdH hconn F hD hd X c x j l pa z ps hp
  have hSpl := supplyWord_true P hdH hconn F hD hd X c x j l z ps
  simp only [fixedCode, MotifFields.fixedInput, MotifFields.mapInput, MotifFields.supplyInput,
    hW, hV, hDmd, hSpl]
  dsimp only [actualEntry]
  refine Prod.ext (Prod.ext (Prod.ext ?_ rfl) ?_) (Prod.ext ?_ ?_)
  all_goals
    dsimp only <;> first | rfl | (apply bank_congr; intro p; cases p <;> rfl)

theorem segmentTests_eq {A B : Type} (p q : A) (r s : B) [Decidable (p = q ∧ r = s)] :
    segmentTest R p q * segmentTest R s r = if p = q ∧ r = s then 1 else 0 := by
  by_cases h : p = q
  · subst q
    by_cases h' : r = s
    · subst s
      simp only [segmentTest, eq_self, and_self, ite_true, mul_one]
    · simp only [segmentTest, eq_self, h', Ne.symm h', true_and, ite_true, ite_false, mul_zero]
  · simp only [segmentTest, h, false_and, ite_false, zero_mul]

theorem portDiagonal_true (pa : OldPlaced) (z : NewHalf) :
    portDiagonal (R := R) (matching X) (widths X) (x, l) j (h₀[pa]) (b₀[z]) =
      if (h₀[pa]).1 (((x, l), j), j) rfl = (b₀[z]).1 j ∧
        incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j j (h₀[pa]) = (b₀[z]).2 j then 1 else 0 :=
  segmentTests_eq (R := R) ((h₀[pa]).1 (((x, l), j), j) rfl) ((b₀[z]).1 j)
    (incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j j (h₀[pa])) ((b₀[z]).2 j)

theorem writer_correct (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)
    (pa : OldPlaced) (z : NewHalf) (ps : List PosCode) (hp : PlaceMatch pa ps) :
    ∃ I : List (List (EntryInput F)),
      writer P hdH hconn hd C (u₀[z, ps]) = I.map (List.map (MotifFields.fixedInput F)) ∧
      entriesValue F (fun _ => zero_lt_one) κ I = (T[κ, hκ]).kernel V pa z := by
  have heq := passes_true P hdH hconn F hD hd X c x j l pa z ps hp
  have hk := kernel_at X P hdH hconn F hD hd c κ hκ x j l pa z
  dsimp only at hk
  rw [portDiagonal_true P hdH hconn F hD hd X c x j l (R := R) pa z] at hk
  have hwr : writer P hdH hconn hd C (u₀[z, ps]) = writerAt P hdH hconn hd C j (u₀[z, ps]) :=
    readAt_ofFn _ _ _
  by_cases h : (h₀[pa]).1 (((x, l), j), j) rfl = (b₀[z]).1 j ∧
      incomingHalf (R := ℤ) (matching X) (widths X) (x, l) j j (h₀[pa]) = (b₀[z]).2 j
  · refine ⟨[[(e₀[pa, z])]], ?_, ?_⟩
    · have ht : passes hd j (u₀[z, ps]) = true := heq.trans (decide_eq_true h)
      simp only [hwr, writerAt, ht, Bool.cond_true, List.map_cons, List.map_nil]
      rw [fixedCode_true P hdH hconn F hD hd X c x j l pa z ps hp]
    · rw [hk, ite_eq_left h, one_mul]
      simp only [entriesValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        List.sum_cons, List.sum_nil, mul_one, add_zero, actualEntry]
      rfl
  · refine ⟨[], ?_, ?_⟩
    · simp only [hwr, writerAt, heq, h, decide_false, Bool.cond_false, List.map_nil]
    · rw [hk, ite_eq_right h, zero_mul]
      rfl

end Correctness

end P1ProgEng.SolKWR

open P1ProgEng.SolKWR

theorem P1ProgEng.refreshKernelProgram {a a₀ dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
    (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
    (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K') (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀) :
    P1P5.KW.RefreshKernelProgram P hdH hconn F hD hd := by
  refine ⟨writer P hdH hconn hd (tallyFactor P hdH hconn F), poly_writer P hdH hconn hd _, ?_⟩
  intro R _ κ hκ g X c x j l pa z ps hp
  have hplaced : PlacedList X (N' := (dyadicRefreshNext X P hdH hconn F hD hd c).network)
      (SolRKernel.placeEquiv X) ((x, j), l) pa ps := hp
  exact writer_correct (P := P) (hdH := hdH) (hconn := hconn) (F := F) (hD := hD) (hd := hd)
    (X := X) (c := c) (x := x) (j := j) (l := l) (κ := κ) (hκ := hκ) (pa := pa) (z := z)
    (ps := ps) hplaced

#print axioms P1ProgEng.refreshKernelProgram

end
end
