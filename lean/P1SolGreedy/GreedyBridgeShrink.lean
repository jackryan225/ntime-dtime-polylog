import P1SolGreedy.GreedyBridgeFixed

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int.P11 P1Wit P1P7 P1ChkFinal

theorem shrink_of_located {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (D : Dims) (u : List Bool) (ℓ : ℕ) (G : Prop) (hkind : (D.lv ℓ).shrink = true)
    (hloc : LocatedRow Bt κ hκ D u ℓ G) :
    ∃ (a g : ℕ) (X : State a (packingLaneBits a g)),
      (D.lv ℓ).bases = Fintype.card X.Base ∧ (D.lv ℓ).slots = 2 ^ a ∧ agOf D ℓ = (a, g) ∧
      (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) ∧ (GreedyStep.ShrinkTrue Bt.shrink D u ℓ X ↔ G) := by
  obtain ⟨a, g, b, n, X, p, o, f, r, c, hr, hrow, hW, hE, hp, hg⟩ := hloc
  cases o with
  | shrink i h X =>
    subst h
    have hpanel (s : X.ShrinkSelection Bt.shrink) :=
      panel_reads_transfer X f (originStep Bt κ hκ D ℓ (.shrink i rfl X) c)
        (originStep Bt κ hκ D ℓ (.shrink i rfl X) s) hp
    refine ⟨_, _, X, f.bases, f.slots, ?_, ?_, ?_⟩
    · have hslot : (D.lv ℓ).slotW = S.degreeExponent i.castSucc := hrow ▸ rfl
      have hlane : (D.lv ℓ).laneW = packingLaneBits (S.degreeExponent i.castSucc) n := hrow ▸ rfl
      rw [agOf, hslot, hlane, ← packingLaneBits_add (S.degreeExponent i.castSucc) n, Nat.add_sub_cancel_left]
    · exact panel_of_reads X f (originStep Bt κ hκ D ℓ (.shrink i rfl X) c) hp
    · refine Iff.trans ?_ hg
      constructor
      · rintro ⟨hc, ho, s, ht, he, hl⟩
        exact ⟨s, (shrink_row_iff Bt κ hκ D u ℓ i X f s hrow hW (hE s) (hpanel s)).mpr
          ⟨hc, ho, ht, he, hl⟩⟩
      · rintro ⟨s, hs⟩
        obtain ⟨hc, ho, ht, he, hl⟩ := (shrink_row_iff Bt κ hκ D u ℓ i X f s hrow hW (hE s) (hpanel s)).mp hs
        exact ⟨hc, ho, s, ht, he, hl⟩
  | refresh X =>
    have hh : (D.lv ℓ).shrink = false := hrow ▸ rfl
    rw [hh] at hkind
    cases hkind

end P1SolGreedy.SolBridge

open P1SolGreedy.SolBridge

set_option maxHeartbeats 800000 in
theorem P1SolGreedy.bridgeShrinkE {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) :
    P1ChkFinal.GreedyBridge.BridgeShrinkTargetE Bt κ hκ V a b x d bigBias termBias hH hE := by
  intro ℓ hℓ hkind u t ht hprev hp
  exact shrink_of_located Bt κ hκ _ _ ℓ _ hkind
    (fixed_located Bt κ hκ V a b x d bigBias termBias hH hE hℓ u t ht hprev hp)

#print axioms P1SolGreedy.bridgeShrinkE
