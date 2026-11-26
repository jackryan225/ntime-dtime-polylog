import P1P7.Defs

/-!
# P7, refresh substep: proof of one-substep locality (radius 1)

Proves `refresh_panel_local'`, the statement `P1P7.refresh_panel_local` of `P1P7/Statement.lean` (same text), for
OpenAI's `dyadicRefreshNext` (DegreeRefreshPass.lean:41). The slot-class facts come from OpenAI's own simp lemmas
`degreeRefresh_external`, `degreeRefresh_internal`, `degreeRefresh_padding` (DegreeRefreshTopology.lean:132-150).
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

/-- An in-neighbour of `x` lies within distance 1 of `x`. -/
theorem edist_inNbr_le {a g : ℕ} (X : State a g) (x : X.Base) (s : Fin (2 ^ a)) :
    (baseGraph X).edist x (X.slots.base.target.symm (x, s)).1 ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  left
  rw [baseGraph, SimpleGraph.fromRel_adj]
  have hq : X.slots.base.target (X.slots.base.target.symm (x, s)) = (x, s) := Equiv.apply_symm_apply _ _
  refine ⟨?_, Or.inr ⟨(X.slots.base.target.symm (x, s)).2, ?_⟩⟩
  · intro h
    have hne := X.slots.base.ends_ne (X.slots.base.target.symm (x, s))
    rw [hq] at hne
    exact hne h
  · rw [Prod.mk.eta, hq]

section RefreshProof

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- A base of the refreshed state, named by an old base and a port (a type cast, so that rewriting works). -/
def nb (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (p : X.Base × Fin (2 ^ a)) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).Base := p

/-- Addresses of the refreshed state. -/
theorem raddr (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (p : X.Base × Fin (2 ^ a)) :
    addr (dyadicRefreshNext X P hdH hconn F hD hd c) (nb P hdH hconn F hD hd X c p) =
      (p.2 : ℕ) + 2 ^ a * addr X p.1 := rfl

theorem rslots_ext (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (p : X.Base × Fin (2 ^ a)) (i : Fin 1) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target (nb P hdH hconn F hD hd X c p, refreshSlots hd (.inl i)) =
      (nb P hdH hconn F hD hd X c (X.slots.base.target p), refreshSlots hd (.inl i)) := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have e := degreeRefresh_external (splitSlots X) P.toSlotGraph hD hd p (0 : BitWord g)
  rw [LiftedSlots.actualGraph_target, Prod.mk.injEq, Prod.mk.injEq] at e
  exact Prod.ext e.1.1 e.2

theorem rslots_int (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin dH) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target
        (nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inl h))) =
      (nb P hdH hconn F hD hd X c (x, (P.toSlotGraph.target (j, h)).1),
        refreshSlots hd (.inr (.inl (P.toSlotGraph.target (j, h)).2))) := by
  have e := degreeRefresh_internal (splitSlots X) P.toSlotGraph hD hd x j (0 : BitWord g) h
  rw [LiftedSlots.actualGraph_target, Prod.mk.injEq, Prod.mk.injEq] at e
  exact Prod.ext e.1.1 e.2

theorem rslots_pad (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin (2 ^ a₀ - (dH + 1))) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target
        (nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inr h))) =
      (nb P hdH hconn F hD hd X c (x, finRotate (2 ^ a) j), refreshSlots hd (.inr (.inr h))) := by
  have e := degreeRefresh_padding (splitSlots X) P.toSlotGraph hD hd x j (0 : BitWord g) h
  rw [LiftedSlots.actualGraph_target, Prod.mk.injEq, Prod.mk.injEq] at e
  exact Prod.ext e.1.1 e.2

theorem rslotsInv_ext (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (i : Fin 1) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target.symm
        (nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inl i)) =
      (nb P hdH hconn F hD hd X c (X.slots.base.target.symm (x, j)), refreshSlots hd (.inl i)) := by
  rw [Equiv.symm_apply_eq, rslots_ext P hdH hconn F hD hd X c, Equiv.apply_symm_apply]

theorem rslotsInv_int (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin dH) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target.symm
        (nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inl h))) =
      (nb P hdH hconn F hD hd X c (x, (P.toSlotGraph.target.symm (j, h)).1),
        refreshSlots hd (.inr (.inl (P.toSlotGraph.target.symm (j, h)).2))) := by
  rw [Equiv.symm_apply_eq, rslots_int P hdH hconn F hD hd X c]
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]

theorem rslotsInv_pad (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin (2 ^ a₀ - (dH + 1))) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.base.target.symm
        (nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inr h))) =
      (nb P hdH hconn F hD hd X c (x, (finRotate (2 ^ a)).symm j), refreshSlots hd (.inr (.inr h))) := by
  rw [Equiv.symm_apply_eq, rslots_pad P hdH hconn F hD hd X c, Equiv.apply_symm_apply]

theorem rdisp_ext (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (p : X.Base × Fin (2 ^ a)) (i : Fin 1) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.displacement
        (nb P hdH hconn F hD hd X c p, refreshSlots hd (.inl i)) =
      (splitBitWord a g (X.slots.displacement p)).2 := by
  show (degreeRefresh (splitSlots X) P.toSlotGraph hD hd).displacement (p, refreshSlots hd (.inl i)) = _
  simp only [degreeRefresh, Equiv.symm_apply_apply] <;> rfl

theorem rdisp_int (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (p : X.Base × Fin (2 ^ a)) (h : Fin dH) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.displacement
        (nb P hdH hconn F hD hd X c p, refreshSlots hd (.inr (.inl h))) = 0 := by
  show (degreeRefresh (splitSlots X) P.toSlotGraph hD hd).displacement (p, refreshSlots hd (.inr (.inl h))) = 0
  simp only [degreeRefresh, Equiv.symm_apply_apply]

theorem rdisp_pad (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (p : X.Base × Fin (2 ^ a)) (h : Fin (2 ^ a₀ - (dH + 1))) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).slots.displacement
        (nb P hdH hconn F hD hd X c p, refreshSlots hd (.inr (.inr h))) = 0 := by
  show (degreeRefresh (splitSlots X) P.toSlotGraph hD hd).displacement (p, refreshSlots hd (.inr (.inr h))) = 0
  simp only [degreeRefresh, Equiv.symm_apply_apply]

theorem rwidth_ext (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (i : Fin 1) (l : BitWord g) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).width
        ((nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inl i)), l) =
      ∑ j' : Fin (2 ^ a), X.width ((x, j), (splitBitWord a g).symm ((bitWordFinEquiv a).symm j', l)) := by
  show newWidths hd (bundleWidths (bitWordFinEquiv a) (splitWidths X))
    (blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F c) ((x, l), j)
    (refreshSlots hd (.inl i)) = _
  simp only [newWidths, Equiv.symm_apply_apply] <;> rfl

theorem rwidth_int (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin dH) (l : BitWord g) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).width
        ((nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inl h))), l) =
      MotifConversion.supplyWidths F (blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) (x, l))
        (c (x, l)).val (j, h) := by
  show newWidths hd (bundleWidths (bitWordFinEquiv a) (splitWidths X))
    (blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F c) ((x, l), j)
    (refreshSlots hd (.inr (.inl h))) = _
  simp only [newWidths, Equiv.symm_apply_apply] <;> rfl

theorem rwidth_pad (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base) (j : Fin (2 ^ a)) (h : Fin (2 ^ a₀ - (dH + 1))) (l : BitWord g) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).width
        ((nb P hdH hconn F hD hd X c (x, j), refreshSlots hd (.inr (.inr h))), l) = 0 := by
  show newWidths hd (bundleWidths (bitWordFinEquiv a) (splitWidths X))
    (blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F c) ((x, l), j)
    (refreshSlots hd (.inr (.inr h))) = 0
  simp only [newWidths, Equiv.symm_apply_apply]

end RefreshProof

/-! ## The block demand widths read only the base and its in-neighbours -/

section Demand

variable {a g : ℕ}

/-- What the block demand of `(x, l)` reads at in-slot `s` of `x`: the far slot, the displacement and the
out-widths of the in-neighbour. -/
def inData (X : State a (a + g)) (x : X.Base) (s : Fin (2 ^ a)) :
    Fin (2 ^ a) × BitWord (a + g) × (Fin (2 ^ a) → BitWord (a + g) → ℕ) :=
  ((X.slots.base.target.symm (x, s)).2, X.slots.displacement (X.slots.base.target.symm (x, s)),
    outWidths X (X.slots.base.target.symm (x, s)).1)

/-- The block demand widths written with the data of `x` and of its in-neighbours only. -/
def demandOf (ow : Fin (2 ^ a) → BitWord (a + g) → ℕ)
    (inD : Fin (2 ^ a) → Fin (2 ^ a) × BitWord (a + g) × (Fin (2 ^ a) → BitWord (a + g) → ℕ))
    (l : BitWord g) (t : Tie (2 ^ a)) : ℕ :=
  if t.1 then ow t.2.val.2 ((splitBitWord a g).symm ((bitWordFinEquiv a).symm t.2.val.1, l))
  else
    (inD t.2.val.2).2.2 (inD t.2.val.2).1 ((splitBitWord a g).symm ((bitWordFinEquiv a).symm
      (((bitWordFinEquiv a).symm.trans ((Equiv.addRight (splitBitWord a g (inD t.2.val.2).2.1).1).trans
        (bitWordFinEquiv a))).symm t.2.val.1), l - (splitBitWord a g (inD t.2.val.2).2.1).2))

theorem demand_eq (X : State a (a + g)) (x : X.Base) (l : BitWord g) :
    blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) (x, l) =
      demandOf (outWidths X x) (inData X x) l := by
  rw [blockDemandWidths_eq]
  rfl

end Demand

/-! ## The theorem -/

section Main

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- The statement of `P1P7.refresh_panel_local`, PROVED. -/
theorem refresh_panel_local' (X X' : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) (c' : DyadicRefreshChoice X' P hdH hconn F)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 1 → panel X y = panel X' y')
    (hterm : ∀ l : BitWord g, (c (x, l)).val = (c' (x', l)).val)
    (j : Fin (2 ^ a)) :
    panel (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j) =
      panel (dyadicRefreshNext X' P hdH hconn F hD hd c') (x', j) := by
  change panel (dyadicRefreshNext X P hdH hconn F hD hd c) (nb P hdH hconn F hD hd X c (x, j)) =
    panel (dyadicRefreshNext X' P hdH hconn F hD hd c') (nb P hdH hconn F hD hd X' c' (x', j))
  have hxx : panel X x = panel X' x' := hagree x x' hx (by simp [SimpleGraph.edist_self])
  have hon : outNbr X x = outNbr X' x' := congrArg (fun p => p.1) hxx
  have hof : outFar X x = outFar X' x' := congrArg (fun p => p.2.1) hxx
  have hin : inNbr X x = inNbr X' x' := congrArg (fun p => p.2.2.1) hxx
  have hif : inFar X x = inFar X' x' := congrArg (fun p => p.2.2.2.1) hxx
  have how : outWidths X x = outWidths X' x' := congrArg (fun p => p.2.2.2.2) hxx
  -- the in-neighbour data agree
  have hinD : inData X x = inData X' x' := by
    funext s
    have h1 : (inNbr X x s) = (inNbr X' x' s) := congrFun hin s
    have h2 : (inFar X x s) = (inFar X' x' s) := congrFun hif s
    simp only [inNbr, inFar, Prod.mk.injEq] at h1 h2
    have hw : outWidths X (X.slots.base.target.symm (x, s)).1 =
        outWidths X' (X'.slots.base.target.symm (x', s)).1 :=
      congrArg (fun p => p.2.2.2.2)
        (hagree _ _ h1.1 (edist_inNbr_le X x s))
    simp only [inData]
    rw [Fin.ext h2, h1.2, hw]
  have hdem : ∀ l : BitWord g,
      blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) (x, l) =
        blockDemandWidths (splitSlots X') (bitWordFinEquiv a) (splitWidths X') (x', l) := by
    intro l
    rw [demand_eq, demand_eq, how, hinD]
  have h1 := fun s => congrFun hon s
  have h2 := fun s => congrFun hof s
  have h3 := fun s => congrFun hin s
  have h4 := fun s => congrFun hif s
  simp only [outNbr, outFar, inNbr, inFar, Prod.mk.injEq] at h1 h2 h3 h4
  simp only [panel, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- out-slots: neighbour address and displacement
    funext kk
    obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective kk
    rcases r with i | h | h
    · simp only [outNbr, rslots_ext P hdH hconn F hD hd, rdisp_ext P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [(h1 j).1, (h1 j).2, h2 j]
    · simp only [outNbr, rslots_int P hdH hconn F hD hd, rdisp_int P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [hx]
    · simp only [outNbr, rslots_pad P hdH hconn F hD hd, rdisp_pad P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [hx]
  · -- far slots of the out-slots
    funext kk
    obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective kk
    rcases r with i | h | h
    · simp only [outFar, rslots_ext P hdH hconn F hD hd]
    · simp only [outFar, rslots_int P hdH hconn F hD hd]
    · simp only [outFar, rslots_pad P hdH hconn F hD hd]
  · -- in-slots: neighbour address and displacement
    funext kk
    obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective kk
    rcases r with i | h | h
    · simp only [inNbr, rslotsInv_ext P hdH hconn F hD hd, rdisp_ext P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [(h3 j).1, (h3 j).2, h4 j]
    · simp only [inNbr, rslotsInv_int P hdH hconn F hD hd, rdisp_int P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [hx]
    · simp only [inNbr, rslotsInv_pad P hdH hconn F hD hd, rdisp_pad P hdH hconn F hD hd,
        raddr P hdH hconn F hD hd]
      rw [hx]
  · -- far slots of the in-slots
    funext kk
    obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective kk
    rcases r with i | h | h
    · simp only [inFar, rslotsInv_ext P hdH hconn F hD hd]
    · simp only [inFar, rslotsInv_int P hdH hconn F hD hd]
    · simp only [inFar, rslotsInv_pad P hdH hconn F hD hd]
  · -- widths
    funext kk l
    obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective kk
    rcases r with i | h | h
    · simp only [outWidths, rwidth_ext P hdH hconn F hD hd]
      exact Finset.sum_congr rfl fun j' _ => congrFun (congrFun how j) _
    · simp only [outWidths, rwidth_int P hdH hconn F hD hd]
      rw [hterm l, hdem l]
    · simp only [outWidths, rwidth_pad P hdH hconn F hD hd]

end Main

end P1P7
