import P1P7.KernelBall

/-!
# P7 kernel locality, layer 2: half-wire equivalences and fibres of motifs, owners and placed positions

* `halfEquiv`: the half-wire assignments at two sites of two state networks are equivalent when the payload types
  agree slot by slot (out-slot `k` to out-slot `k`, in-slot `k` to in-slot `k`); `halfEquiv_out`, `halfEquiv_in`:
  the canonical clauses (payload unchanged, as `HEq`).
* `tM`: the partner of a motif whose two wire ends are good; `tA_tA`, `tM_tM`: partners of partners.
* `subEquiv`: an equivalence of subtypes from two inverse partial maps.
* `Good3`: all bases within distance 3 are good.
* fibre lemmas: residents and owners of a motif lie near its wire ends; placed positions lie near the site.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.NetworkKernel

section HalfEq

variable {a G G' : ℕ}

theorem placedCongr_heq {U U' V V' : Type} {p : U → V} {p' : U' → V'} {B : U → Type} {B' : U' → Type}
    {v : V} {v' : V'} (e : {u // v = p u} ≃ {u' // v' = p' u'}) (f : ∀ u : {u // v = p u}, B u.1 ≃ B' (e u).1)
    (pa : Placed p B v) (u : U) (hu : v = p u) (u' : U') (hu' : v' = p' u') (h : (e ⟨u, hu⟩).1 = u') :
    HEq (placedCongr e f pa u' hu') (f ⟨u, hu⟩ (pa u hu)) := by
  subst h
  exact heq_of_eq (placedCongr_apply e f pa u hu)

/-- Half-wire assignments at `u` and `u'` with slotwise equal payload types. -/
noncomputable def halfEquiv (X : State a G) (X' : State a G') (u : X.network.Site) (u' : X'.network.Site)
    (hout : ∀ k, X.network.Payload ((outFib X u).symm k).1 = X'.network.Payload ((outFib X' u').symm k).1)
    (hin : ∀ k, X.network.Payload ((inFib X u).symm k).1 = X'.network.Payload ((inFib X' u').symm k).1) :
    X.network.Half u ≃ X'.network.Half u' :=
  (placedCongr ((outFib X u).trans (outFib X' u').symm) (fun e => Equiv.cast
      ((congrArg (fun e => X.network.Payload e.1) ((outFib X u).symm_apply_apply e)).symm.trans
        (hout (outFib X u e))))).prodCongr
    (placedCongr ((inFib X u).trans (inFib X' u').symm) (fun e => Equiv.cast
      ((congrArg (fun e => X.network.Payload e.1) ((inFib X u).symm_apply_apply e)).symm.trans
        (hin (inFib X u e)))))

theorem halfEquiv_out (X : State a G) (X' : State a G') (u : X.network.Site) (u' : X'.network.Site)
    (hout : ∀ k, X.network.Payload ((outFib X u).symm k).1 = X'.network.Payload ((outFib X' u').symm k).1)
    (hin : ∀ k, X.network.Payload ((inFib X u).symm k).1 = X'.network.Payload ((inFib X' u').symm k).1)
    (z : X.network.Half u) (k : Fin (2 ^ a)) :
    HEq ((halfEquiv X X' u u' hout hin z).1 ((outFib X' u').symm k).1 ((outFib X' u').symm k).2)
      (z.1 ((outFib X u).symm k).1 ((outFib X u).symm k).2) := by
  refine (placedCongr_heq _ _ z.1 _ ((outFib X u).symm k).2 _ _ ?_).trans (cast_heq _ _)
  change ((outFib X' u').symm ((outFib X u) ((outFib X u).symm k))).1 = _
  rw [Equiv.apply_symm_apply]

theorem halfEquiv_in (X : State a G) (X' : State a G') (u : X.network.Site) (u' : X'.network.Site)
    (hout : ∀ k, X.network.Payload ((outFib X u).symm k).1 = X'.network.Payload ((outFib X' u').symm k).1)
    (hin : ∀ k, X.network.Payload ((inFib X u).symm k).1 = X'.network.Payload ((inFib X' u').symm k).1)
    (z : X.network.Half u) (k : Fin (2 ^ a)) :
    HEq ((halfEquiv X X' u u' hout hin z).2 ((inFib X' u').symm k).1 ((inFib X' u').symm k).2)
      (z.2 ((inFib X u).symm k).1 ((inFib X u).symm k).2) := by
  refine (placedCongr_heq _ _ z.2 _ ((inFib X u).symm k).2 _ _ ?_).trans (cast_heq _ _)
  change ((inFib X' u').symm ((inFib X u) ((inFib X u).symm k))).1 = _
  rw [Equiv.apply_symm_apply]

end HalfEq

section Sub

/-- An equivalence of subtypes from two inverse partial maps. -/
def subEquiv {A A' : Type*} {P : A → Prop} {P' : A' → Prop}
    (f : ∀ x, P x → A') (hf : ∀ x h, P' (f x h)) (g : ∀ x', P' x' → A) (hg : ∀ x' h, P (g x' h))
    (gf : ∀ x h, g (f x h) (hf x h) = x) (fg : ∀ x' h, f (g x' h) (hg x' h) = x') :
    {x // P x} ≃ {x' // P' x'} where
  toFun x := ⟨f x.1 x.2, hf x.1 x.2⟩
  invFun x' := ⟨g x'.1 x'.2, hg x'.1 x'.2⟩
  left_inv x := Subtype.ext (gf x.1 x.2)
  right_inv x' := Subtype.ext (fg x'.1 x'.2)

end Sub

section Motif

variable {a g : ℕ}

theorem tS_tS {T L : Type*} (X X' : State a (packingLaneBits a g)) (s : Site X.Base T L)
    (h : SGood X X' s.1) : tS X' X (tS X X' s) = s := by
  change (pb X' X (pb X X' s.1), s.2) = s
  rw [pb_pb X X' h.addr_eq]

theorem tA_tA (X X' : State a (packingLaneBits a g))
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) (h : SGood X X' α.1.1.1) :
    tA X' X (tA X X' α) = α := by
  change ((tS X' X (tS X X' α.1.1), α.1.2), α.2) = α
  rw [tS_tS X X' α.1.1 h]

/-- The partner motif. -/
noncomputable abbrev tM {X X' : State a (packingLaneBits a g)} (m : X.packingData.Motif)
    (h : EndsGood X X' m.val) : X'.packingData.Motif :=
  ⟨tA X X' m.val, motif_tA X X' m.val h m.property⟩

theorem tM_val {X X' : State a (packingLaneBits a g)} (m : X.packingData.Motif) (h : EndsGood X X' m.val) :
    (tM m h).val = tA X X' m.val := rfl

theorem tM_tM {X X' : State a (packingLaneBits a g)} (m : X.packingData.Motif) (h : EndsGood X X' m.val)
    (h' : EndsGood X' X (tM m h).val) : tM (tM m h) h' = m :=
  Subtype.ext (tA_tA X X' m.val h.1)

/-- All bases within distance 3 of `x` are good. -/
def Good3 (X X' : State a (packingLaneBits a g)) (x : X.Base) : Prop :=
  ∀ y, (baseGraph X).edist x y ≤ 3 → SGood X X' y

theorem edist_add_le {X : State a (packingLaneBits a g)} {u v w : X.Base} {p q : ℕ}
    (h1 : (baseGraph X).edist u v ≤ p) (h2 : (baseGraph X).edist v w ≤ q) :
    (baseGraph X).edist u w ≤ (p + q : ℕ) :=
  (SimpleGraph.edist_triangle (v := v)).trans ((add_le_add h1 h2).trans (by push_cast; rfl))

/-- A motif whose two wire ends are within 2 of `x` has good ends, good bundle mates and a good bundle head. -/
theorem motif_conds {X X' : State a (packingLaneBits a g)} {x : X.Base} (hg : Good3 X X' x)
    (m : X.packingData.Motif) (h1 : (baseGraph X).edist x m.val.1.1.1 ≤ 2)
    (h2 : (baseGraph X).edist x (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 ≤ 2) :
    EndsGood X X' m.val ∧
      (∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m → EndsGood X X' m2.val) ∧
      SGood X X' (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1 := by
  have hC : (baseGraph X).edist x (X.packingData.C m).1.1 ≤ 2 := by
    rcases C_base X m with h | h <;> rw [h]
    · exact h1
    · exact h2
  refine ⟨⟨hg _ (h1.trans (by norm_num)), hg _ (h2.trans (by norm_num))⟩, ?_, ?_⟩
  · intro m2 hb
    have hbase : (X.packingData.C m2).1.1 = (X.packingData.C m).1.1 :=
      congrArg (fun b => b.1.1) hb
    obtain ⟨e1, e2⟩ := ends_of_base X m2 (C_base X m2)
    rw [hbase] at e1 e2
    exact ⟨hg _ ((edist_add_le hC e1).trans (by norm_num)), hg _ ((edist_add_le hC e2).trans (by norm_num))⟩
  · exact hg _ ((edist_add_le hC (edist_target_le X _ _)).trans (by norm_num))

/-- A placed position lies at its own base or at an out-neighbour of it. -/
theorem placement_near (X : State a (packingLaneBits a g)) (layout : Bool)
    (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1)) :
    (baseGraph X).edist (X.packingData.placement layout p).1 p.1.1 ≤ 1 := by
  unfold PackingData.placement
  split_ifs
  · simp
  · rw [SimpleGraph.edist_comm]
    exact edist_target_le X p.1.1 (X.packingData.slotLabel p.2.2)
  · show (baseGraph X).edist p.1.1 p.1.1 ≤ 1
    simp

end Motif

end P1P7
