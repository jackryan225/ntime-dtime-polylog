import P1P7.KernelFib

/-!
# P7 kernel locality, layer 3: old positions placed at a new site

* `tPos`, `outEdge`, `inEdge` (moved here unchanged from KernelStatement.lean).
* `payload_eq`: the payload of a state wire is a bit word of its width.
* `oldIn_payload`, `oldHalfEquiv`: the half-wires of a good old position and of its partner.
* `oplace`: the placement of the actual shrinking term (`T.place`, by `rfl`).
* `posEquiv`: the old positions placed at `((x, j), l)` correspond to those placed at `((pb x, j), l)`.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.NetworkKernel

section Edges

variable {a G : ℕ}

/-- The partner of an old position (base replaced by the base with the same address, lane kept). -/
noncomputable def tPos (X X' : State a G) (u : X.Base × BitWord G) : X'.Base × BitWord G :=
  (pb X X' u.1, u.2)

/-- The actual out-arc of a position at slot `k`. -/
def outEdge (X : State a G) (u : X.Base × BitWord G) (k : Fin (2 ^ a)) : X.network.Edge := (u, k)

/-- The actual in-arc of a position at in-slot `k`. -/
def inEdge (X : State a G) (u : X.Base × BitWord G) (k : Fin (2 ^ a)) : X.network.Edge :=
  X.slots.actualGraph.target.symm (u, k)

theorem outEdge_src (X : State a G) (u : X.Base × BitWord G) (k : Fin (2 ^ a)) :
    u = X.network.src (outEdge X u k) := rfl

theorem inEdge_dst (X : State a G) (u : X.Base × BitWord G) (k : Fin (2 ^ a)) :
    u = X.network.dst (inEdge X u k) :=
  (congrArg Prod.fst (X.slots.actualGraph.target.apply_symm_apply (u, k))).symm

theorem payload_eq (X : State a G) (e : X.network.Edge) :
    X.network.Payload e = (Fin (X.width ((e.1.1, e.2), e.1.2)) → Bool) := rfl

end Edges

section Old

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}

theorem oldIn_payload (y : X.Base) (l : BitWord (packingLaneBits a g)) (k : Fin (2 ^ a)) (hy : SGood X X' y)
    (hy0 : SGood X X' (X.slots.base.target.symm (y, k)).1) :
    X.network.Payload ((inFib X (y, l)).symm k).1 =
      X'.network.Payload ((inFib X' (pb X X' y, l)).symm k).1 := by
  have e1 : X'.slots.base.target.symm (pb X X' y, k) =
      (pb X X' (X.slots.base.target.symm (y, k)).1, (X.slots.base.target.symm (y, k)).2) :=
    Prod.ext (hy.itgt1 k).symm (hy.itgt2 k).symm
  have hd := (hy.inNbr_eq k).2
  have hw := hy0.width_eq (X.slots.base.target.symm (y, k)).2
    (l - X.slots.displacement (X.slots.base.target.symm (y, k)))
  change (Fin (X.width (X.slots.base.target.symm (y, k),
      l - X.slots.displacement (X.slots.base.target.symm (y, k)))) → Bool) =
    (Fin (X'.width (X'.slots.base.target.symm (pb X X' y, k),
      l - X'.slots.displacement (X'.slots.base.target.symm (pb X X' y, k)))) → Bool)
  rw [← hd, e1]
  exact congrArg (fun n => Fin n → Bool) hw

/-- The half-wires of a good old position and of its partner (slot `k` to slot `k`). -/
noncomputable def oldHalfEquiv (u : X.network.Site) (hy : SGood X X' u.1)
    (hin : ∀ k, SGood X X' (X.slots.base.target.symm (u.1, k)).1) :
    X.network.Half u ≃ X'.network.Half (tPos X X' u) :=
  halfEquiv X X' u (tPos X X' u) (fun k => congrArg (fun n => Fin n → Bool) (hy.width_eq k u.2))
    (fun k => oldIn_payload u.1 u.2 k hy (hin k))

/-- The placement of the actual shrinking term, read on the state's own sites. -/
noncomputable def oplace (X : State a (packingLaneBits a g)) (L : Bool) (u : X.network.Site) :
    (X.Base × TagW a) × BitWord g :=
  X.packingData.shrinkPlace L ((packingInputSites X.Base a g).symm u)

theorem tPos_tPos (u : X.network.Site) (h : SGood X X' u.1) : tPos X' X (tPos X X' u) = u := by
  change (pb X' X (pb X X' u.1), u.2) = u
  rw [pb_pb X X' h.addr_eq]
  rfl

theorem oplace_tPos (L : Bool) (u : X.network.Site) (h : SGood X X' u.1) :
    oplace X' L (tPos X X' u) =
      ((pb X X' (oplace X L u).1.1, (oplace X L u).1.2), (oplace X L u).2) := by
  unfold oplace PackingData.shrinkPlace
  have := placement_tP (X := X) (X' := X') L ((packingInputSites X.Base a g).symm u) h
  change packedSiteEquiv (X'.packingData.placement L (tP X X' ((packingInputSites X.Base a g).symm u))) = _
  rw [this]
  rfl

theorem oplace_near (L : Bool) (u : X.network.Site) :
    (baseGraph X).edist (oplace X L u).1.1 u.1 ≤ 1 :=
  placement_near X L ((packingInputSites X.Base a g).symm u)

/-- Positions placed near `x` are good, and so are their in-neighbours. -/
theorem placed_good {x : X.Base} (hg : Good3 X X' x) (L : Bool) (tg : TagW a) (l : BitWord g)
    (u : X.network.Site) (hu : ((x, tg), l) = oplace X L u) :
    SGood X X' u.1 ∧ ∀ k, SGood X X' (X.slots.base.target.symm (u.1, k)).1 := by
  have hx : (oplace X L u).1.1 = x := (congrArg (fun q => q.1.1) hu).symm
  have h1 : (baseGraph X).edist x u.1 ≤ 1 := hx ▸ oplace_near L u
  refine ⟨hg _ (h1.trans (by norm_num)), fun k => hg _ ?_⟩
  have h2 : (baseGraph X).edist u.1 (X.slots.base.target.symm (u.1, k)).1 ≤ 1 := by
    have := edist_target_le X (X.slots.base.target.symm (u.1, k)).1 (X.slots.base.target.symm (u.1, k)).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply, SimpleGraph.edist_comm] at this
    exact this
  exact (edist_add_le h1 h2).trans (by norm_num)

/-- The old positions placed at `((x, tg), l)` and at `((pb x, tg), l)` (layouts `L = L'`). -/
noncomputable def posEquiv {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) :
    {u : X.network.Site // ((x, tg), l) = oplace X L u} ≃
      {u : X'.network.Site // ((pb X X' x, tg), l) = oplace X' L' u} :=
  subEquiv (fun u _ => tPos X X' u)
    (fun u hu => by
      subst hLL
      rw [oplace_tPos L u (placed_good hg L tg l u hu).1, ← hu])
    (fun u' _ => tPos X' X u')
    (fun u' hu' => by
      subst hLL
      have hx : pb X' X (pb X X' x) = x := pb_pb X X' (hg x (by simp)).addr_eq
      rw [oplace_tPos L u' (placed_good hg' L tg l u' hu').1, ← hu', hx])
    (fun u hu => tPos_tPos u (placed_good hg L tg l u hu).1)
    (fun u' hu' => tPos_tPos u' (placed_good hg' L' tg l u' hu').1)

theorem posEquiv_apply {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) (u : X.network.Site)
    (hu : ((x, tg), l) = oplace X L u) :
    (posEquiv hg hg' L L' hLL tg l ⟨u, hu⟩).1 = tPos X X' u := rfl

end Old

end P1P7
