import P1P7.SolKernlocSupply
import P1P7.Statement

/-! Slotwise payload transport and bundle coordinates for the dyadic degree refresh. -/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.SpectralGeometry

namespace SolRKernel

noncomputable section

section Grouped

variable {B B' : Type} {R : Type*} {d : ℕ} [Fintype B] [Fintype B'] [CommRing R]
variable {t : Equiv.Perm (Refresh.Arc B d)} {t' : Equiv.Perm (Refresh.Arc B' d)}
variable {w : Refresh.Arc B d → ℕ} {w' : Refresh.Arc B' d → ℕ}
variable {s : B} {s' : B'} {j : Fin d}

theorem segmentTest_heq {n n' : ℕ} (h : n' = n)
    {v u : Refresh.Word n} {v' u' : Refresh.Word n'} (hv : HEq v' v) (hu : HEq u' u) :
    segmentTest R v' u' = segmentTest R v u := by
  subst n'
  cases hv
  cases hu
  rfl

theorem wordIndex_heq {n n' : ℕ} (h : n' = n)
    {u : Refresh.Word n} {u' : Refresh.Word n'} (hu : HEq u' u) :
    HEq (wordIndex n' u') (wordIndex n u) := by
  subst n'
  cases hu
  rfl

theorem wordIndex_value {n n' : ℕ} (h : n' = n) {u : Fin (2 ^ n)} {u' : Fin (2 ^ n')}
    (hu : HEq ((wordIndex n').symm u') ((wordIndex n).symm u)) : u'.val = u.val := by
  subst n'
  exact congrArg Fin.val ((wordIndex n).symm.injective (eq_of_heq hu))

variable (q : (oldWireGraph t w).Half (s, j)) (q' : (oldWireGraph t' w').Half (s', j))
variable (z : PortSegments t w s j) (z' : PortSegments t' w' s' j)

theorem portDiagonal_eq (ho : w' ((s', j), j) = w ((s, j), j))
    (hi : w' (t'.symm ((s', j), j)) = w (t.symm ((s, j), j)))
    (hqo : HEq (q'.1 ((s', j), j) rfl) (q.1 ((s, j), j) rfl))
    (hqi : HEq (incomingHalf (R := R) t' w' s' j j q') (incomingHalf (R := R) t w s j j q))
    (hzo : HEq (z'.1 j) (z.1 j)) (hzi : HEq (z'.2 j) (z.2 j)) :
    portDiagonal (R := R) t' w' s' j q' z' = portDiagonal (R := R) t w s j q z :=
  congrArg₂ (· * ·) (segmentTest_heq ho hqo hzo) (segmentTest_heq hi hzi hqi)

theorem portInput_heq (hw : internalWidth t' w' s' = internalWidth t w s)
    (hqo : ∀ i, HEq (q'.1 ((s', i), j) rfl) (q.1 ((s, i), j) rfl))
    (hqi : ∀ i, HEq (incomingHalf (R := R) t' w' s' j i q')
      (incomingHalf (R := R) t w s j i q))
    (hzo : ∀ i, HEq (z'.1 i) (z.1 i)) (hzi : ∀ i, HEq (z'.2 i) (z.2 i)) :
    HEq (portInput (R := R) t' w' s' j q' z') (portInput (R := R) t w s j q z) := by
  apply SolKernloc.halfBits_heq hw
  · rintro ⟨b, ⟨⟨p, i⟩, hpi⟩⟩ h
    change j = p at h
    subst p
    cases b
    · exact SolKernloc.finVal_eq (congrArg (2 ^ ·) (congrFun hw (false, ⟨(j, i), hpi⟩)))
        (wordIndex_heq (congrFun hw (false, ⟨(j, i), hpi⟩)) (hqi i))
    · exact SolKernloc.finVal_eq (congrArg (2 ^ ·) (congrFun hw (true, ⟨(j, i), hpi⟩)))
        (wordIndex_heq (congrFun hw (true, ⟨(j, i), hpi⟩)) (hqo i))
  · rintro ⟨b, ⟨⟨i, p⟩, hip⟩⟩ h
    change j = p at h
    subst p
    cases b
    · exact SolKernloc.finVal_eq (congrArg (2 ^ ·) (congrFun hw (false, ⟨(i, j), hip⟩)))
        (wordIndex_heq (congrFun hw (false, ⟨(i, j), hip⟩)) (hzi i))
    · exact SolKernloc.finVal_eq (congrArg (2 ^ ·) (congrFun hw (true, ⟨(i, j), hip⟩)))
        (wordIndex_heq (congrFun hw (true, ⟨(i, j), hip⟩)) (hzo i))

def slice {d : ℕ} (w : Fin d → ℕ) (b : Refresh.Word (∑ i, w i)) (k : Fin d) : Refresh.Word (w k) :=
  fun i => b (finSigmaFinEquiv (n := w) ⟨k, i⟩)

theorem slice_heq {w w' : Fin d → ℕ} (hw : w' = w)
    {b : Refresh.Word (∑ i, w i)} {b' : Refresh.Word (∑ i, w' i)} (hb : HEq b' b)
    {i i' : Fin d} (hi : i' = i) : HEq (slice w' b' i') (slice w b i) := by
  subst w'
  subst i'
  cases hb
  rfl

omit [Fintype B] in
theorem incidentIn (target : Equiv.Perm (B × Fin d))
    (h : ∀ e : Refresh.Arc B d, (t e).1 = target e.1) (p : B × Fin d)
    (bo : Refresh.Word (∑ i, w (p, i))) (bi : Refresh.Word (∑ i, w (target.symm p, i)))
    (k : Fin d) :
    HEq ((incidentPortSegments t target h w p bo bi).2 k)
      (slice (fun i => w (target.symm p, i)) bi (t.symm (p, k)).2) := by
  classical
  let z : External w := Function.update (fun _ _ => false) (target.symm p) bi
  have hz : z (target.symm p) = bi := Function.update_self _ _ _
  rw [← hz]
  change HEq ((incidentPortSegments t target h w p (z p) (z (target.symm p))).2 k) _
  rw [incidentPortSegments_external]
  have hq : (t.symm (p, k)).1 = target.symm p := by
    apply target.injective
    rw [← h, t.apply_symm_apply, target.apply_symm_apply]
  change HEq (slice (fun i => w ((t.symm (p, k)).1, i)) (z (t.symm (p, k)).1) (t.symm (p, k)).2) _
  have hzcongr (b b' : B × Fin d) (e : b = b') : HEq (z b) (z b') := by
    cases e
    rfl
  exact slice_heq (congrArg (fun b => fun i => w (b, i)) hq) (hzcongr _ _ hq) rfl

end Grouped

section Input

variable {a g : ℕ} {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}

theorem inData_eq
    (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 1 →
      panel X y = panel X' y') :
    inData X x = inData X' x' := by
  have hxx := hagree x x' hx (by simp only [SimpleGraph.edist_self, zero_le])
  funext s
  have hn : inNbr X x s = inNbr X' x' s := congrArg (fun p => p.2.2.1 s) hxx
  have hf : inFar X x s = inFar X' x' s := congrArg (fun p => p.2.2.2.1 s) hxx
  simp only [inNbr, inFar, Prod.mk.injEq] at hn hf
  have hw : outWidths X (X.slots.base.target.symm (x, s)).1 =
      outWidths X' (X'.slots.base.target.symm (x', s)).1 :=
    congrArg (fun p => p.2.2.2.2) (hagree _ _ hn.1 (edist_inNbr_le X x s))
  simp only [inData]
  rw [Fin.ext hf, hn.2, hw]

theorem oldOut (ho : outWidths X x = outWidths X' x') (m : BitWord (a + g))
    (i : Fin (2 ^ a)) :
    X.network.Payload ((outFib X (x, m)).symm i).1 =
      X'.network.Payload ((outFib X' (x', m)).symm i).1 := by
  exact congrArg (fun w : Fin (2 ^ a) → BitWord (a + g) → ℕ => Fin (w i m) → Bool) ho

theorem oldIn (hi : inData X x = inData X' x') (m : BitWord (a + g))
    (i : Fin (2 ^ a)) :
    X.network.Payload ((inFib X (x, m)).symm i).1 =
      X'.network.Payload ((inFib X' (x', m)).symm i).1 := by
  exact congrArg (fun q : Fin (2 ^ a) × BitWord (a + g) ×
    (Fin (2 ^ a) → BitWord (a + g) → ℕ) => Fin (q.2.2 q.1 (m - q.2.1)) → Bool)
    (congrFun hi i)

def placeEquiv (X : State a (a + g)) :
    X.network.Site ≃ (X.Base × Fin (2 ^ a)) × BitWord g :=
  ((Equiv.refl X.Base).prodCongr (splitBitWord a g).toEquiv).trans
    (refreshPositions (bitWordFinEquiv a))

def mergeLane (j : Fin (2 ^ a)) (l : BitWord g) : BitWord (a + g) :=
  (splitBitWord a g).symm ((bitWordFinEquiv a).symm j, l)

def placedSingle {U V : Type} {H : U → Type} (p : U ≃ V) (v : V) :
    Placed p H v ≃ H (p.symm v) where
  toFun b := b (p.symm v) (p.apply_symm_apply v).symm
  invFun b u hu := (congrArg p.symm hu).trans (p.symm_apply_apply u) ▸ b
  left_inv b := by
    funext u hu
    obtain rfl := p.injective ((p.apply_symm_apply v).trans hu)
    rfl
  right_inv _ := rfl

theorem pos_eq (X : State a (a + g)) (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
    (u : X.network.Site) (hu : ((x, j), l) = placeEquiv X u) :
    u = (x, (splitBitWord a g).symm ((bitWordFinEquiv a).symm j, l)) :=
  ((congrArg (placeEquiv X).symm hu).trans ((placeEquiv X).symm_apply_apply u)).symm

end Input

section Output

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
variable (c : DyadicRefreshChoice X P hdH hconn F) (c' : DyadicRefreshChoice X' P hdH hconn F)

local notation "Y" => dyadicRefreshNext X P hdH hconn F hD hd c
local notation "Y'" => dyadicRefreshNext X' P hdH hconn F hD hd c'

theorem demandWidths_eq (ho : outWidths X x = outWidths X' x')
    (hi : inData X x = inData X' x') (l : BitWord g) :
    blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) (x, l) =
      blockDemandWidths (splitSlots X') (bitWordFinEquiv a) (splitWidths X') (x', l) := by
  rw [demand_eq, demand_eq, ho, hi]

theorem newOut (j : Fin (2 ^ a)) (l : BitWord g) (hn : panel Y (x, j) = panel Y' (x', j))
    (i : Fin (2 ^ a₀)) :
    (Y).network.Payload ((outFib Y ((x, j), l)).symm i).1 =
      (Y').network.Payload ((outFib Y' ((x', j), l)).symm i).1 := by
  have h : outWidths Y (x, j) = outWidths Y' (x', j) := congrArg (fun p => p.2.2.2.2) hn
  exact congrArg (fun w : Fin (2 ^ a₀) → BitWord g → ℕ => Fin (w i l) → Bool) h

theorem extWidth (p : X.Base × Fin (2 ^ a)) (i : Fin 1) (l : BitWord g) :
    (Y).width ((nb P hdH hconn F hD hd X c p, refreshSlots hd (.inl i)), l) =
      ∑ j : Fin (2 ^ a), X.width ((p.1, p.2), mergeLane j l) := by
  rcases p with ⟨x, j⟩
  exact rwidth_ext P hdH hconn F hD hd X c x j i l

set_option maxHeartbeats 600000 in
theorem newIn (ho : outWidths X x = outWidths X' x')
    (hi : inData X x = inData X' x') (j : Fin (2 ^ a)) (l : BitWord g)
    (ht : (c (x, l)).val = (c' (x', l)).val) (i : Fin (2 ^ a₀)) :
    (Y).network.Payload ((inFib Y ((x, j), l)).symm i).1 =
      (Y').network.Payload ((inFib Y' ((x', j), l)).symm i).1 := by
  suffices (Y).width ((Y).slots.base.target.symm (nb P hdH hconn F hD hd X c (x, j), i),
      l - (Y).slots.displacement ((Y).slots.base.target.symm (nb P hdH hconn F hD hd X c (x, j), i))) =
    (Y').width ((Y').slots.base.target.symm (nb P hdH hconn F hD hd X' c' (x', j), i),
      l - (Y').slots.displacement ((Y').slots.base.target.symm (nb P hdH hconn F hD hd X' c' (x', j), i))) from
    congrArg (fun n => Fin n → Bool) this
  obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective i
  rcases r with i | i | i
  · simp only [rslotsInv_ext, rdisp_ext, extWidth]
    exact congrArg (fun q : Fin (2 ^ a) × BitWord (a + g) ×
      (Fin (2 ^ a) → BitWord (a + g) → ℕ) =>
        ∑ p : Fin (2 ^ a), q.2.2 q.1 ((splitBitWord a g).symm
          ((bitWordFinEquiv a).symm p, l - (splitBitWord a g q.2.1).2))) (congrFun hi j)
  · simp only [rslotsInv_int, rdisp_int, sub_zero, rwidth_int]
    exact congrArg₂ (fun w u => supplyWidths F w u (P.toSlotGraph.target.symm (j, i)))
      (demandWidths_eq ho hi l) ht
  · simp only [rslotsInv_pad, rdisp_pad, sub_zero, rwidth_pad]

end Output

section Placed

variable {a g : ℕ} {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
variable (ho : outWidths X x = outWidths X' x') (hi : inData X x = inData X' x')
variable (j : Fin (2 ^ a)) (l : BitWord g)

local notation "rLane" => mergeLane j l
local notation "site₀" => ((x, j), l)
local notation "site₁" => ((x', j), l)

noncomputable def oldPlaced :
    Placed (placeEquiv X) X.network.Half site₀ ≃ Placed (placeEquiv X') X'.network.Half site₁ :=
  (placedSingle (placeEquiv X) site₀).trans
    ((halfEquiv X X' (x, rLane) (x', rLane) (oldOut ho rLane) (oldIn hi rLane)).trans
      (placedSingle (placeEquiv X') site₁).symm)

theorem oldPlaced_out (hx : addr X x = addr X' x')
    (pa : Placed (placeEquiv X) X.network.Half site₀)
    (u : X.network.Site) (hu : site₀ = placeEquiv X u)
    (hu' : site₁ = placeEquiv X' (tPos X X' u)) :
    SolKernloc.SlotOut (pa u hu) (oldPlaced ho hi j l pa (tPos X X' u) hu') := by
  obtain rfl := pos_eq X x j l u hu
  have h : tPos X X' (x, rLane) = (x', rLane) :=
    Prod.ext (pb_eq X X' hx) rfl
  suffices ∀ u' : X'.network.Site, u' = (x', rLane) → ∀ hu' : site₁ = placeEquiv X' u',
      SolKernloc.SlotOut (pa (x, rLane) hu) (oldPlaced ho hi j l pa u' hu') from this _ h hu'
  intro u' he hu'
  subst u'
  exact halfEquiv_out X X' (x, rLane) (x', rLane) (oldOut ho rLane) (oldIn hi rLane) (pa _ hu)

theorem oldPlaced_in (hx : addr X x = addr X' x')
    (pa : Placed (placeEquiv X) X.network.Half site₀)
    (u : X.network.Site) (hu : site₀ = placeEquiv X u)
    (hu' : site₁ = placeEquiv X' (tPos X X' u)) :
    SolKernloc.SlotIn (pa u hu) (oldPlaced ho hi j l pa (tPos X X' u) hu') := by
  obtain rfl := pos_eq X x j l u hu
  have h : tPos X X' (x, rLane) = (x', rLane) :=
    Prod.ext (pb_eq X X' hx) rfl
  suffices ∀ u' : X'.network.Site, u' = (x', rLane) → ∀ hu' : site₁ = placeEquiv X' u',
      SolKernloc.SlotIn (pa (x, rLane) hu) (oldPlaced ho hi j l pa u' hu') from this _ h hu'
  intro u' he hu'
  subst u'
  exact halfEquiv_in X X' (x, rLane) (x', rLane) (oldOut ho rLane) (oldIn hi rLane) (pa _ hu)

end Placed

section Coordinates

variable {a g : ℕ}
variable (X : State a (a + g))

abbrev matching := oldPortMatching (splitSlots X) (bitWordFinEquiv a)
abbrev widths := groupedWidths (bitWordFinEquiv a) (splitWidths X)
abbrev target := bundleTarget (splitSlots X)

def outProfile (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) : Fin (2 ^ a) → ℕ :=
  fun i => widths X (((x, l), j), i)

def inProfile (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) : Fin (2 ^ a) → ℕ :=
  fun i => widths X ((target X).symm ((x, l), j), i)

def inPort (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) : Equiv.Perm (Fin (2 ^ a)) :=
  (bundlePort (splitSlots X) (bitWordFinEquiv a) ((target X).symm ((x, l), j))).symm

theorem outProfile_eq {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
    (ho : outWidths X x = outWidths X' x') (j : Fin (2 ^ a)) (l : BitWord g) :
    outProfile X' x' j l = outProfile X x j l :=
  congrArg (fun w => fun i => w j ((splitBitWord a g).symm ((bitWordFinEquiv a).symm i, l))) ho.symm

theorem inProfile_eq {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
    (hi : inData X x = inData X' x') (j : Fin (2 ^ a)) (l : BitWord g) :
    inProfile X' x' j l = inProfile X x j l :=
  congrArg (fun q : Fin (2 ^ a) × BitWord (a + g) × (Fin (2 ^ a) → BitWord (a + g) → ℕ) =>
    fun i => q.2.2 q.1 ((splitBitWord a g).symm
      ((bitWordFinEquiv a).symm i, l - (splitBitWord a g q.2.1).2))) (congrFun hi.symm j)

theorem inPort_eq {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
    (hi : inData X x = inData X' x') (j : Fin (2 ^ a)) (l : BitWord g) :
    inPort X' x' j l = inPort X x j l :=
  congrArg (fun m : BitWord (a + g) => ((bitWordFinEquiv a).symm.trans
    ((Equiv.addRight (splitBitWord a g m).1).trans (bitWordFinEquiv a))).symm)
    (congrArg (fun q => q.2.1) (congrFun hi.symm j))

theorem incomingProfile (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) (i : Fin (2 ^ a)) :
    widths X ((matching X).symm (((x, l), j), i)) = inProfile X x j l (inPort X x j l i) := by
  rw [oldPortMatching_symm_apply]
  rfl

theorem inPort_index (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) (i : Fin (2 ^ a)) :
    ((matching X).symm (((x, l), j), i)).2 = inPort X x j l i :=
  congrArg Prod.snd (oldPortMatching_symm_apply (splitSlots X) (bitWordFinEquiv a) ((x, l), j) i)

abbrev unfoldedSites := originalSites (V := X.Base) (L := BitWord g) (bitWordFinEquiv a)

abbrev original := originalIso (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
abbrev lane := relaneIso X.slots (splitBitWord a g) X.width

def oldPull (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
    (q : X.network.Half ((placeEquiv X).symm ((x, j), l))) :
    (oldWireGraph (matching X) (widths X)).Half ((x, l), j) :=
  (original X).pullHalf ((x, l), j) ((lane X).pullHalf (unfoldedSites X ((x, l), j)) q)

theorem oldPull_out (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
    (q : X.network.Half ((placeEquiv X).symm ((x, j), l))) (i : Fin (2 ^ a)) :
    HEq ((oldPull X x j l q).1 (((x, l), i), j) rfl)
      (q.1 (outEdge X ((placeEquiv X).symm ((x, j), l)) i)
        (outEdge_src X ((placeEquiv X).symm ((x, j), l)) i)) := HEq.rfl

theorem oldPull_in (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
    (q : X.network.Half ((placeEquiv X).symm ((x, j), l))) (i : Fin (2 ^ a)) {R : Type*}
    [CommRing R] :
    HEq (incomingHalf (R := R) (matching X) (widths X) (x, l) j i (oldPull X x j l q))
      (q.2 (inEdge X ((placeEquiv X).symm ((x, j), l)) i)
        (inEdge_dst X ((placeEquiv X).symm ((x, j), l)) i)) := by
  let e := (matching X).symm (((x, l), i), j)
  let e₁ := (original X).edge e
  let e₂ := (lane X).edge e₁
  have h : ((x, l), j) = source (matching X e) :=
    (congrArg source ((matching X).apply_symm_apply (((x, l), i), j))).symm
  have h₁ := (congrArg (original X).site h).trans ((original X).dst e)
  have h₂ := (congrArg (lane X).site h₁).trans ((lane X).dst e₁)
  change HEq (q.2 e₂ h₂) _
  refine SolKernloc.halfReadIn q e₂ h₂ i ?_
  have hs (f : Refresh.Arc (X.Base × BitWord g) (2 ^ a)) :
      (X.slots.actualGraph.target ((lane X).edge ((original X).edge f))).2 =
        (matching X f).1.2 := by
    obtain ⟨b, p⟩ := f
    rw [oldPortMatching_apply]
    rfl
  exact (hs e).trans (congrArg (fun f => f.1.2) ((matching X).apply_symm_apply _))

end Coordinates

theorem castEquiv_pull {A W W' : Type} (h : W = W') (e : A ≃ W) (b : W') :
    HEq (e ((cast (congrArg (fun T => A ≃ T) h) e).symm b)) b := by
  subst W'
  exact heq_of_eq (e.apply_symm_apply b)

end

end SolRKernel

end P1P7
