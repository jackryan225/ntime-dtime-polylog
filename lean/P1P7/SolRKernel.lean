import P1P7.SolRLocal

/-! Radius-one kernel locality for the actual dyadic degree-refresh pass. -/

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

section Formula

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (X : State a (a + g))
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable (c : DyadicRefreshChoice X P hdH hconn F)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ)

abbrev demand := blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
abbrev supplyWidth := blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F c
abbrev labels (s : X.Base × BitWord g) (e : Fin (2 ^ a) × Fin dH) :=
  Fin (2 ^ supplyWidth X P hdH hconn F c s e)

noncomputable abbrev promote :=
  promotedIso (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P.toSlotGraph hD hd
    (labels X P hdH hconn F c) (supplyWidth X P hdH hconn F c)
    (fun s e => (wordIndex (supplyWidth X P hdH hconn F c s e)).symm)

noncomputable abbrev refreshTermAt :=
  (dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c

variable (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)

local notation "p₀" => ((x, l), j)
local notation "Y₀" => dyadicRefreshNext X P hdH hconn F hD hd c
local notation "T₀" => refreshTermAt X P hdH hconn F hD hd c κ hκ
local notation "pr" => promote X P hdH hconn F hD hd c

def newPull (z : (Y₀).network.Half ((x, j), l)) :
    (refreshOutput (target X) (widths X) Prod.fst (fun e => (P.toSlotGraph.target e).1)
      (labels X P hdH hconn F c) (2 ^ a₀ - (dH + 1))).Half ((x, l), j) :=
  Network.Iso.pullHalf (pr) ((x, l), j) z

def outWord (z : (Y₀).network.Half ((x, j), l)) : Refresh.Word (∑ i, outProfile X x j l i) :=
  (newPull X P hdH hconn F hD hd c x j l z).1 (.inl p₀) rfl

def inWord (z : (Y₀).network.Half ((x, j), l)) : Refresh.Word (∑ i, inProfile X x j l i) :=
  (newPull X P hdH hconn F hD hd c x j l z).2
    (.inl ((target X).symm p₀)) ((target X).apply_symm_apply p₀).symm

def segments (z : (Y₀).network.Half ((x, j), l)) : PortSegments (matching X) (widths X) (x, l) j :=
  incidentPortSegments (matching X) (target X)
    (oldPortMatching_bundle (splitSlots X) (bitWordFinEquiv a)) (widths X) p₀
    (outWord X P hdH hconn F hD hd c x j l z) (inWord X P hdH hconn F hD hd c x j l z)

theorem segments_in (z : (Y₀).network.Half ((x, j), l)) (i : Fin (2 ^ a)) :
    HEq ((segments X P hdH hconn F hD hd c x j l z).2 i)
      (slice (inProfile X x j l) (inWord X P hdH hconn F hD hd c x j l z) (inPort X x j l i)) :=
  (incidentIn (target X) (oldPortMatching_bundle (splitSlots X) (bitWordFinEquiv a)) p₀
    (outWord X P hdH hconn F hD hd c x j l z) (inWord X P hdH hconn F hD hd c x j l z) i).trans
    (slice_heq rfl HEq.rfl (inPort_index X x j l i))

def readSupply (z : (Y₀).network.Half ((x, j), l)) :
    HalfBits Prod.fst (fun e => (P.toSlotGraph.target e).1)
    (supplyWidth X P hdH hconn F c (x, l)) j :=
  supplyHalf (R := ℕ) (target X) (widths X) Prod.fst (fun e => (P.toSlotGraph.target e).1)
    (labels X P hdH hconn F c) (2 ^ a₀ - (dH + 1)) p₀
    (newPull X P hdH hconn F hD hd c x j l z)

theorem tieMass_pos {d : ℕ} (i : Tie d) : 0 < tieMass i := zero_lt_one

set_option maxHeartbeats 600000 in
theorem promoteExternal (p : (X.Base × BitWord g) × Fin (2 ^ a))
    (b : (Y₀).network.Payload ((pr).edge (.inl p))) :
    HEq (((pr).payload (.inl p)).symm b) b := by
  have hw : Refresh.Word (∑ i, widths X (p, i)) =
      (Y₀).network.Payload ((pr).edge (.inl p)) :=
    congrArg (fun n => Refresh.Word n)
      (actualWidth_external_bundle (hd := hd) (bitWordFinEquiv a) (splitWidths X)
        (supplyWidth X P hdH hconn F c) p).symm
  exact castEquiv_pull hw (Equiv.refl _) b

set_option maxHeartbeats 600000 in
theorem promoteInternal (s : X.Base × BitWord g) (e : Fin (2 ^ a) × Fin dH)
    (b : (Y₀).network.Payload ((pr).edge (.inr (.inl (s, e))))) :
    HEq ((wordIndex (supplyWidth X P hdH hconn F c s e)).symm
      (((pr).payload (.inr (.inl (s, e)))).symm b)) b := by
  have hw : Refresh.Word (supplyWidth X P hdH hconn F c s e) =
      (Y₀).network.Payload ((pr).edge (.inr (.inl (s, e)))) :=
    congrArg (fun n => Refresh.Word n) (rwidth_int P hdH hconn F hD hd X c s.1 e.1 e.2 s.2).symm
  exact castEquiv_pull hw (wordIndex (supplyWidth X P hdH hconn F c s e)).symm b

theorem outWord_slot (z : (Y₀).network.Half ((x, j), l)) :
    HEq (outWord X P hdH hconn F hD hd c x j l z)
      (z.1 (outEdge Y₀ ((x, j), l) (refreshSlots hd (.inl 0)))
        (outEdge_src Y₀ ((x, j), l) (refreshSlots hd (.inl 0)))) :=
  promoteExternal X P hdH hconn F hD hd c p₀
    (z.1 (outEdge Y₀ ((x, j), l) (refreshSlots hd (.inl 0)))
      (outEdge_src Y₀ ((x, j), l) (refreshSlots hd (.inl 0))))

set_option maxHeartbeats 600000 in
theorem inWord_slot (z : (Y₀).network.Half ((x, j), l)) :
    HEq (inWord X P hdH hconn F hD hd c x j l z)
      (z.2 (inEdge Y₀ ((x, j), l) (refreshSlots hd (.inl 0)))
        (inEdge_dst Y₀ ((x, j), l) (refreshSlots hd (.inl 0)))) := by
  let p := (target X).symm p₀
  let e := (pr).edge (.inl p)
  have h : ((x, j), l) = (Y₀).network.dst e :=
    (congrArg (pr).site ((target X).apply_symm_apply p₀).symm).trans ((pr).dst (.inl p))
  refine (promoteExternal X P hdH hconn F hD hd c p (z.2 e h)).trans
    (@SolKernloc.halfReadIn a₀ g Y₀ ((x, j), l) z e h (refreshSlots hd (.inl 0)) ?_)
  change ((degreeRefresh (splitSlots X) P.toSlotGraph hD hd).actualGraph.target
    (((p.1.1, p.2), p.1.2), refreshSlots hd (.inl 0))).2 = _
  rw [degreeRefresh_external]

set_option maxHeartbeats 600000 in
theorem supplyOut_word (z : (Y₀).network.Half ((x, j), l))
    (e : Fin (2 ^ a) × Fin dH) (he : j = e.1) :
    HEq ((wordIndex (supplyWidth X P hdH hconn F c (x, l) e)).symm
        ((readSupply X P hdH hconn F hD hd c x j l z).1 e he))
      (z.1 (outEdge Y₀ ((x, j), l) (refreshSlots hd (.inr (.inl e.2))))
        (outEdge_src Y₀ ((x, j), l) (refreshSlots hd (.inr (.inl e.2))))) := by
  subst j
  exact promoteInternal X P hdH hconn F hD hd c (x, l) e
    (z.1 (outEdge Y₀ ((x, e.1), l) (refreshSlots hd (.inr (.inl e.2))))
      (outEdge_src Y₀ ((x, e.1), l) (refreshSlots hd (.inr (.inl e.2)))))

set_option maxHeartbeats 600000 in
theorem supplyIn_word (z : (Y₀).network.Half ((x, j), l))
    (e : Fin (2 ^ a) × Fin dH) (he : j = (P.toSlotGraph.target e).1) :
    HEq ((wordIndex (supplyWidth X P hdH hconn F c (x, l) e)).symm
        ((readSupply X P hdH hconn F hD hd c x j l z).2 e he))
      (z.2 (inEdge Y₀ ((x, j), l) (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e).2))))
        (inEdge_dst Y₀ ((x, j), l) (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e).2))))) := by
  let f := (pr).edge (.inr (.inl ((x, l), e)))
  have hs : ((x, l), j) = ((x, l), (P.toSlotGraph.target e).1) := Prod.ext rfl he
  have h : ((x, j), l) = (Y₀).network.dst f :=
    (congrArg (pr).site hs).trans ((pr).dst (.inr (.inl ((x, l), e))))
  refine (promoteInternal X P hdH hconn F hD hd c (x, l) e (z.2 f h)).trans
    (@SolKernloc.halfReadIn a₀ g Y₀ ((x, j), l) z f h
      (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e).2))) ?_)
  change ((degreeRefresh (splitSlots X) P.toSlotGraph hD hd).actualGraph.target
    (((x, e.1), l), refreshSlots hd (.inr (.inl e.2)))).2 = _
  rw [degreeRefresh_internal]

set_option maxHeartbeats 800000 in
theorem kernel_at (pa : Placed (T₀).place X.network.Half ((x, j), l))
    (z : (Y₀).network.Half ((x, j), l)) :
    (T₀).kernel ((x, j), l) pa z =
      let q := oldPull X x j l (placedSingle (placeEquiv X) ((x, j), l) pa)
      let b := segments X P hdH hconn F hD hd c x j l z
      portDiagonal (R := R) (matching X) (widths X) (x, l) j q b *
        evalEntry κ (entry F tieMass_pos (demand X (x, l)) (c (x, l)).val j
          (portInput (R := R) (matching X) (widths X) (x, l) j q b)
          (readSupply X P hdH hconn F hD hd c x j l z)) := by
  rfl

end Formula

section Congruence

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ)

theorem entry_congr {w w' : Tie (2 ^ a) → ℕ} {u u' : Fin (2 ^ a) × Fin dH → ℕ}
    (j : Fin (2 ^ a)) (hw : w' = w) (hu : u' = u)
    {b : HalfBits tieSource tieTarget w j} {b' : HalfBits tieSource tieTarget w' j}
    {y : HalfBits Prod.fst (fun e => (P.toSlotGraph.target e).1) (supplyWidths F w u) j}
    {y' : HalfBits Prod.fst (fun e => (P.toSlotGraph.target e).1) (supplyWidths F w' u') j}
    (hb : HEq b' b) (hy : HEq y' y) :
    evalEntry κ (entry F tieMass_pos w' u' j b' y') =
      evalEntry κ (entry F tieMass_pos w u j b y) := by
  subst w'
  subst u'
  cases hb
  cases hy
  rfl

variable {X X' : State a (a + g)} {x : X.Base} {x' : X'.Base}
variable (c : DyadicRefreshChoice X P hdH hconn F) (c' : DyadicRefreshChoice X' P hdH hconn F)
variable (j : Fin (2 ^ a)) (l : BitWord g)

local notation "U₀" => dyadicRefreshNext X P hdH hconn F hD hd c
local notation "U₁" => dyadicRefreshNext X' P hdH hconn F hD hd c'
local notation "T₀" => refreshTermAt X P hdH hconn F hD hd c κ hκ
local notation "T₁" => refreshTermAt X' P hdH hconn F hD hd c' κ hκ

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1300000 in
theorem kernel_congr (ho : outWidths X x = outWidths X' x') (hi : inData X x = inData X' x')
    (ht : (c' (x', l)).val = (c (x, l)).val)
    (pa : Placed (T₀).place X.network.Half ((x, j), l))
    (pa' : Placed (T₁).place X'.network.Half ((x', j), l))
    (z : (U₀).network.Half ((x, j), l)) (z' : (U₁).network.Half ((x', j), l))
    (hqo : SolKernloc.SlotOut (placedSingle (placeEquiv X) ((x, j), l) pa)
      (placedSingle (placeEquiv X') ((x', j), l) pa'))
    (hqi : SolKernloc.SlotIn (placedSingle (placeEquiv X) ((x, j), l) pa)
      (placedSingle (placeEquiv X') ((x', j), l) pa'))
    (hzo : @SolKernloc.SlotOut a₀ g g U₀ U₁ ((x, j), l) ((x', j), l) z z')
    (hzi : @SolKernloc.SlotIn a₀ g g U₀ U₁ ((x, j), l) ((x', j), l) z z') :
    (T₁).kernel ((x', j), l) pa' z' = (T₀).kernel ((x, j), l) pa z := by
  let q := placedSingle (placeEquiv X) ((x, j), l) pa
  let q' := placedSingle (placeEquiv X') ((x', j), l) pa'
  have hqOut (i : Fin (2 ^ a)) := (oldPull_out X' x' j l q' i).trans
    ((hqo i).trans (oldPull_out X x j l q i).symm)
  have hqIn (i : Fin (2 ^ a)) := (oldPull_in X' x' j l q' i (R := R)).trans
    ((hqi i).trans (oldPull_in X x j l q i (R := R)).symm)
  have heOut := (outWord_slot X' P hdH hconn F hD hd c' x' j l z').trans
    ((hzo (refreshSlots hd (.inl 0))).trans (outWord_slot X P hdH hconn F hD hd c x j l z).symm)
  have heIn := (inWord_slot X' P hdH hconn F hD hd c' x' j l z').trans
    ((hzi (refreshSlots hd (.inl 0))).trans (inWord_slot X P hdH hconn F hD hd c x j l z).symm)
  have hwOut := outProfile_eq ho j l
  have hwIn := inProfile_eq hi j l
  have hp := inPort_eq hi j l
  let b := segments X P hdH hconn F hD hd c x j l z
  let b' := segments X' P hdH hconn F hD hd c' x' j l z'
  have hbOut (i : Fin (2 ^ a)) : HEq (b'.1 i) (b.1 i) :=
    slice_heq hwOut heOut rfl
  have hbIn (i : Fin (2 ^ a)) : HEq (b'.2 i) (b.2 i) := by
    exact (segments_in X' P hdH hconn F hD hd c' x' j l z' i).trans
      ((slice_heq hwIn heIn (congrArg (fun p : Equiv.Perm (Fin (2 ^ a)) => p i) hp)).trans
        (segments_in X P hdH hconn F hD hd c x j l z i).symm)
  have hw : demand X' (x', l) = demand X (x, l) := (demandWidths_eq ho hi l).symm
  have hu : supplyWidth X' P hdH hconn F c' (x', l) = supplyWidth X P hdH hconn F c (x, l) :=
    congrArg₂ (supplyWidths F) hw ht
  have hs : HEq (readSupply X' P hdH hconn F hD hd c' x' j l z')
      (readSupply X P hdH hconn F hD hd c x j l z) := by
    apply SolKernloc.halfBits_heq hu
    · intro e he
      exact wordIndex_value (congrFun hu e)
        ((supplyOut_word X' P hdH hconn F hD hd c' x' j l z' e he).trans
          ((hzo (refreshSlots hd (.inr (.inl e.2)))).trans
            (supplyOut_word X P hdH hconn F hD hd c x j l z e he).symm))
    · intro e he
      exact wordIndex_value (congrFun hu e)
        ((supplyIn_word X' P hdH hconn F hD hd c' x' j l z' e he).trans
          ((hzi (refreshSlots hd (.inr (.inl (P.toSlotGraph.target e).2)))).trans
            (supplyIn_word X P hdH hconn F hD hd c x j l z e he).symm))
  have hdiagIn : widths X' ((matching X').symm (((x', l), j), j)) =
      widths X ((matching X).symm (((x, l), j), j)) := by
    simp only [incomingProfile, hwIn, hp]
  have hdg := portDiagonal_eq (R := R) (oldPull X x j l q) (oldPull X' x' j l q') b b'
    (congrFun hwOut j) hdiagIn (hqOut j) (hqIn j) (hbOut j) (hbIn j)
  have hb := portInput_heq (R := R) (oldPull X x j l q) (oldPull X' x' j l q') b b'
    hw hqOut hqIn hbOut hbIn
  exact (kernel_at X' P hdH hconn F hD hd c' κ hκ x' j l pa' z').trans
    ((congrArg₂ (· * ·) hdg (entry_congr P hdH hconn F κ j hw ht hb hs)).trans
      (kernel_at X P hdH hconn F hD hd c κ hκ x j l pa z).symm)

end Congruence

theorem slotIn_apply {a G G' : ℕ} {Y : State a G} {Y' : State a G'}
    {u : Y.network.Site} {u' : Y'.network.Site} {z : Y.network.Half u} {z' : Y'.network.Half u'}
    (h : @SolKernloc.SlotIn a G G' Y Y' u u' z z') (i : Fin (2 ^ a)) :
    HEq (z'.2 (inEdge Y' u' i) (inEdge_dst Y' u' i))
      (z.2 (inEdge Y u i) (inEdge_dst Y u i)) :=
  h i

end

end SolRKernel

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1300000 in
/-- Radius-one kernel locality of the dyadic refresh pass. -/
theorem refresh_kernel_local (X X' : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) (c' : DyadicRefreshChoice X' P hdH hconn F)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 1 → panel X y = panel X' y')
    (hterm : ∀ l : BitWord g, (c (x, l)).val = (c' (x', l)).val)
    (j : Fin (2 ^ a)) (l : BitWord g) :
    ∃ (eP : Placed ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place X.network.Half ((x, j), l) ≃
          Placed ((dyadicRefreshPass X' P hdH hconn F hD hd κ hκ).step.term c').place X'.network.Half ((x', j), l))
      (eO : (dyadicRefreshNext X P hdH hconn F hD hd c).network.Half ((x, j), l) ≃
          (dyadicRefreshNext X' P hdH hconn F hD hd c').network.Half ((x', j), l)),
      (∀ pa u (hu : ((x, j), l) = ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place u)
          (hu' : ((x', j), l) = ((dyadicRefreshPass X' P hdH hconn F hD hd κ hκ).step.term c').place (tPos X X' u))
          (kk : Fin (2 ^ a)),
        HEq ((eP pa (tPos X X' u) hu').1 (outEdge X' (tPos X X' u) kk) (outEdge_src X' (tPos X X' u) kk))
          ((pa u hu).1 (outEdge X u kk) (outEdge_src X u kk))) ∧
      (∀ pa u (hu : ((x, j), l) = ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place u)
          (hu' : ((x', j), l) = ((dyadicRefreshPass X' P hdH hconn F hD hd κ hκ).step.term c').place (tPos X X' u))
          (kk : Fin (2 ^ a)),
        HEq ((eP pa (tPos X X' u) hu').2 (inEdge X' (tPos X X' u) kk) (inEdge_dst X' (tPos X X' u) kk))
          ((pa u hu).2 (inEdge X u kk) (inEdge_dst X u kk))) ∧
      (∀ z (kk : Fin (2 ^ a₀)),
        HEq ((eO z).1 (outEdge (dyadicRefreshNext X' P hdH hconn F hD hd c') ((x', j), l) kk)
            (outEdge_src (dyadicRefreshNext X' P hdH hconn F hD hd c') ((x', j), l) kk))
          (z.1 (outEdge (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) kk)
            (outEdge_src (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) kk))) ∧
      (∀ z (kk : Fin (2 ^ a₀)),
        HEq ((eO z).2 (inEdge (dyadicRefreshNext X' P hdH hconn F hD hd c') ((x', j), l) kk)
            (inEdge_dst (dyadicRefreshNext X' P hdH hconn F hD hd c') ((x', j), l) kk))
          (z.2 (inEdge (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) kk)
            (inEdge_dst (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) kk))) ∧
      ∀ pa z, ((dyadicRefreshPass X' P hdH hconn F hD hd κ hκ).step.term c').kernel ((x', j), l) (eP pa) (eO z) =
        ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).kernel ((x, j), l) pa z := by
  have hxx := hagree x x' hx (by simp only [SimpleGraph.edist_self, zero_le])
  have ho : outWidths X x = outWidths X' x' := congrArg (fun p => p.2.2.2.2) hxx
  have hi := SolRKernel.inData_eq hx hagree
  have hn := refresh_panel_local P hdH hconn F hD hd X X' c c' x x' hx hagree hterm j
  let Y := dyadicRefreshNext X P hdH hconn F hD hd c
  let Y' := dyadicRefreshNext X' P hdH hconn F hD hd c'
  let eP := SolRKernel.oldPlaced ho hi j l
  let hout := SolRKernel.newOut P hdH hconn F hD hd c c' j l hn
  let hin := SolRKernel.newIn P hdH hconn F hD hd c c' ho hi j l (hterm l)
  let v : Y.network.Site := ((x, j), l)
  let v' : Y'.network.Site := ((x', j), l)
  let eO := halfEquiv Y Y' v v' hout hin
  have hzOut (z : Y.network.Half v) : @SolKernloc.SlotOut a₀ g g Y Y' v v' z (eO z) :=
    @SolKernloc.halfEquiv_slotOut a₀ g g Y Y' v v' hout hin z
  have hzIn (z : Y.network.Half v) : @SolKernloc.SlotIn a₀ g g Y Y' v v' z (eO z) :=
    @SolKernloc.halfEquiv_slotIn a₀ g g Y Y' v v' hout hin z
  refine ⟨eP, eO, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun pa u hu hu' => SolRKernel.oldPlaced_out ho hi j l hx pa u hu hu'
  · exact fun pa u hu hu' => SolRKernel.oldPlaced_in ho hi j l hx pa u hu hu'
  · change ∀ z : Y.network.Half v, @SolKernloc.SlotOut a₀ g g Y Y' v v' z (eO z)
    exact hzOut
  · intro z i
    have h := @SolRKernel.slotIn_apply a₀ g g
      (dyadicRefreshNext X P hdH hconn F hD hd c) (dyadicRefreshNext X' P hdH hconn F hD hd c')
      ((x, j), l) ((x', j), l) z (eO z) (hzIn z) i
    exact h
  · intro pa z
    let q := SolRKernel.placedSingle (SolRKernel.placeEquiv X) ((x, j), l) pa
    let m := SolRKernel.mergeLane j l
    have hqo : @SolKernloc.SlotOut a (a + g) (a + g) X X' (x, m) (x', m)
        q (SolRKernel.placedSingle (SolRKernel.placeEquiv X') ((x', j), l) (eP pa)) :=
      SolKernloc.halfEquiv_slotOut X X' (x, m) (x', m)
        (SolRKernel.oldOut ho m) (SolRKernel.oldIn hi m) q
    have hqi : @SolKernloc.SlotIn a (a + g) (a + g) X X' (x, m) (x', m)
        q (SolRKernel.placedSingle (SolRKernel.placeEquiv X') ((x', j), l) (eP pa)) :=
      SolKernloc.halfEquiv_slotIn X X' (x, m) (x', m)
        (SolRKernel.oldOut ho m) (SolRKernel.oldIn hi m) q
    exact SolRKernel.kernel_congr P hdH hconn F hD hd κ hκ c c' j l ho hi (hterm l).symm
      pa (eP pa) z (eO z) hqo hqi (hzOut z) (hzIn z)

end Refresh

#print axioms refresh_kernel_local

end P1P7
