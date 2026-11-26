import P1P7.ShrinkLocal

/-!
# P7 kernel locality, layer 0 and 1: symmetric balls and generic equivalences

* `addr_transport_back`: under the hypothesis of `addr_transport` (neighbour addresses agree on the ball of `x`),
  every base `y'` of `X'` within `r + 1` of `x'` has a partner in `X` at no larger distance from `x`.
* `agree_symm`: the radius-3 hypothesis of the locality theorems is symmetric (so every one-sided lemma also runs
  from `X'` to `X`, which gives inverse maps).
* `placedCongr`: an equivalence of `Placed` families from an equivalence of fibres and of the fibre types.
* `outFib`, `inFib`: the out- and in-half-wire fibres at a site of a state network are numbered by the slots.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

section Back

variable {a g g' : ℕ}

theorem addr_transport_back_getVert (X : State a g) (X' : State a g') (x : X.Base) (x' : X'.Base)
    (hx : addr X x = addr X' x') (r : ℕ)
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ r →
      ∀ k, addr X (X.slots.base.target (y, k)).1 = addr X' (X'.slots.base.target (y', k)).1 ∧
        addr X (X.slots.base.target.symm (y, k)).1 = addr X' (X'.slots.base.target.symm (y', k)).1)
    {y' : X'.Base} (p : (baseGraph X').Walk x' y') (hp : p.length ≤ r + 1) :
    ∀ i, i ≤ p.length → ∃ v : X.Base, addr X v = addr X' (p.getVert i) ∧ (baseGraph X).edist x v ≤ i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [SimpleGraph.Walk.getVert_zero]
    exact ⟨x, hx, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨v, hv, hd⟩ := ih (by omega)
    have hadj := p.adj_getVert_succ (i := i) (by omega)
    have hir : (baseGraph X).edist x v ≤ r :=
      hd.trans (by exact_mod_cast (by omega : i ≤ r))
    have hnb := hagree v _ hv hir
    obtain ⟨w, hw, hadj'⟩ := adj_transport X' X _ _ v (fun k => ⟨(hnb k).1.symm, (hnb k).2.symm⟩) hadj
    refine ⟨w, hw, ?_⟩
    calc (baseGraph X).edist x w
        ≤ (baseGraph X).edist x v + (baseGraph X).edist v w := SimpleGraph.edist_triangle
      _ ≤ i + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj']
          exact add_le_add hd le_rfl
      _ = ((i + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- Backward transport of a ball: partners in `X` of the bases of `X'` near `x'`. -/
theorem addr_transport_back (X : State a g) (X' : State a g') (x : X.Base) (x' : X'.Base)
    (hx : addr X x = addr X' x') (r : ℕ)
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ r →
      ∀ k, addr X (X.slots.base.target (y, k)).1 = addr X' (X'.slots.base.target (y', k)).1 ∧
        addr X (X.slots.base.target.symm (y, k)).1 = addr X' (X'.slots.base.target.symm (y', k)).1)
    (y' : X'.Base) (hy : (baseGraph X').edist x' y' ≤ r + 1) :
    ∃ y : X.Base, addr X y = addr X' y' ∧ (baseGraph X).edist x y ≤ (baseGraph X').edist x' y' := by
  have hne : (baseGraph X').edist x' y' ≠ ⊤ := ne_top_of_le_ne_top (by simp) hy
  obtain ⟨w, hw⟩ := (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
  have hlen : w.length ≤ r + 1 := by
    have : ((w.length : ℕ) : ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) := by rw [hw]; exact_mod_cast hy
    exact_mod_cast this
  obtain ⟨y, hy', hd⟩ := addr_transport_back_getVert X X' x x' hx r hagree w hlen w.length le_rfl
  rw [SimpleGraph.Walk.getVert_length] at hy'
  exact ⟨y, hy', hw ▸ hd⟩

/-- Partners of partners. -/
theorem pb_pb (X : State a g) (X' : State a g') {y : X.Base} (h : addr X' (pb X X' y) = addr X y) :
    pb X' X (pb X X' y) = y :=
  pb_eq X' X h

end Back

section Symm

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- The radius-3 agreement hypothesis is symmetric. -/
theorem agree_symm (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 3 →
      shrinkData B X s y = shrinkData B X' s' y') :
    ∀ y' y, addr X' y' = addr X y → (baseGraph X').edist x' y' ≤ 3 →
      shrinkData B X' s' y' = shrinkData B X s y := by
  intro y' y hyy hd'
  have hnb : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 2 →
      ∀ kk, addr X (X.slots.base.target (y, kk)).1 = addr X' (X'.slots.base.target (y', kk)).1 ∧
        addr X (X.slots.base.target.symm (y, kk)).1 = addr X' (X'.slots.base.target.symm (y', kk)).1 := by
    intro y y' h hd kk
    have hd' : (baseGraph X).edist x y ≤ 3 := hd.trans (by norm_num)
    have hp : panel X y = panel X' y' := congrArg (fun q => q.1) (hagree y y' h hd')
    have h1 := congrFun (congrArg (fun q => q.1) hp : outNbr X y = outNbr X' y') kk
    have h2 := congrFun (congrArg (fun q => q.2.2.1) hp : inNbr X y = inNbr X' y') kk
    exact ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩
  obtain ⟨y0, hy0, hd0⟩ := addr_transport_back X X' x x' hx 2 hnb y' (hd'.trans (by norm_num))
  have hy : y0 = y := addr_injective X (hy0.trans hyy)
  subst hy
  exact (hagree y0 y' hy0 (hd0.trans hd')).symm

end Symm

/-! ## Generic equivalences of placed families and half-wire fibres -/

section Placed

/-- A placed family is a function on the fibre. -/
def placedSub {U V : Type} (p : U → V) (B : U → Type) (v : V) :
    Placed p B v ≃ ((u : {u // v = p u}) → B u.1) where
  toFun f u := f u.1 u.2
  invFun g u h := g ⟨u, h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence of placed families from equivalences of the fibres and of the fibre types. -/
def placedCongr {U U' V V' : Type} {p : U → V} {p' : U' → V'} {B : U → Type} {B' : U' → Type}
    {v : V} {v' : V'} (e : {u // v = p u} ≃ {u' // v' = p' u'}) (f : ∀ u : {u // v = p u}, B u.1 ≃ B' (e u).1) :
    Placed p B v ≃ Placed p' B' v' :=
  (placedSub p B v).trans ((Equiv.piCongr e f).trans (placedSub p' B' v').symm)

theorem placedCongr_apply {U U' V V' : Type} {p : U → V} {p' : U' → V'} {B : U → Type} {B' : U' → Type}
    {v : V} {v' : V'} (e : {u // v = p u} ≃ {u' // v' = p' u'}) (f : ∀ u : {u // v = p u}, B u.1 ≃ B' (e u).1)
    (pa : Placed p B v) (u : U) (hu : v = p u) :
    placedCongr e f pa (e ⟨u, hu⟩).1 (e ⟨u, hu⟩).2 = f ⟨u, hu⟩ (pa u hu) := by
  simp only [placedCongr, placedSub, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  exact Equiv.piCongr_apply_apply (W := fun u => B u.1) (Z := fun u' => B' u'.1) e f _ ⟨u, hu⟩

end Placed

section Fib

variable {a G : ℕ}

/-- The out-half-wires at a site are numbered by the out-slots. -/
def outFib (X : State a G) (u : X.network.Site) :
    {e : X.network.Edge // u = X.network.src e} ≃ Fin (2 ^ a) where
  toFun e := e.1.2
  invFun k := ⟨(u, k), rfl⟩
  left_inv := by
    rintro ⟨⟨u0, k⟩, h⟩
    change u = u0 at h
    subst h
    rfl
  right_inv _ := rfl

/-- The in-half-wires at a site are numbered by the in-slots. -/
noncomputable def inFib (X : State a G) (u : X.network.Site) :
    {e : X.network.Edge // u = X.network.dst e} ≃ Fin (2 ^ a) where
  toFun e := (X.slots.actualGraph.target e.1).2
  invFun k := ⟨X.slots.actualGraph.target.symm (u, k),
    (congrArg Prod.fst (X.slots.actualGraph.target.apply_symm_apply (u, k))).symm⟩
  left_inv := by
    rintro ⟨e, h⟩
    apply Subtype.ext
    apply X.slots.actualGraph.target.injective
    exact (X.slots.actualGraph.target.apply_symm_apply _).trans (Prod.ext h rfl)
  right_inv k := by
    change (X.slots.actualGraph.target (X.slots.actualGraph.target.symm (u, k))).2 = k
    rw [Equiv.apply_symm_apply]

theorem inFib_symm (X : State a G) (u : X.network.Site) (k : Fin (2 ^ a)) :
    ((inFib X u).symm k).1 = X.slots.actualGraph.target.symm (u, k) := rfl

theorem outFib_symm (X : State a G) (u : X.network.Site) (k : Fin (2 ^ a)) :
    ((outFib X u).symm k).1 = (u, k) := rfl

end Fib

end P1P7
