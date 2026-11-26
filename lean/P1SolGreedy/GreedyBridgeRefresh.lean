import P1SolGreedy.GreedyBridgeFixed

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh
open P1Wit P1P7 P1ChkFinal

theorem refresh_of_located {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (D : Dims) (u : List Bool) (ℓ : ℕ) (G : Prop) (hkind : (D.lv ℓ).shrink = false)
    (hloc : LocatedRow Bt κ hκ D u ℓ G) :
    ∃ (g : ℕ) (X : State S.portExponent (S.portExponent + g)),
      (D.lv ℓ).bases = Fintype.card X.Base ∧ (D.lv ℓ).termKeys = 2 ^ g ∧
      (D.lv ℓ).laneW - S.portExponent = g ∧ (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) ∧
      ((∃ c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos S.expanderExponent)
          (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh,
          C7R.storedTm (dH := 2 ^ S.expanderExponent) D u ℓ X =
            P1ChkGreedy.trueBlockTerms S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
              Bt.refresh X c) ↔ G) := by
  obtain ⟨a, g, b, n, X, p, o, f, r, c, hr, hrow, hW, hE, hp, hg⟩ := hloc
  cases o with
  | shrink i h X =>
    have hh : (D.lv ℓ).shrink = true := hrow ▸ rfl
    rw [hh] at hkind
    cases hkind
  | refresh X =>
    refine ⟨_, X, f.bases, ?_, ?_, ?_, ?_⟩
    · rw [hrow]
      exact congrArg (fun j : ℕ => (2 : ℕ) ^ j) (Nat.add_sub_cancel_left _ _)
    · rw [hrow]
      exact Nat.add_sub_cancel_left _ _
    · exact panel_of_reads X f (originStep Bt κ hκ D ℓ (.refresh X) c) hp
    · refine Iff.trans ?_ hg
      apply exists_congr
      intro s
      have hpanel := panel_reads_transfer X f (originStep Bt κ hκ D ℓ (.refresh X) c)
        (originStep Bt κ hκ D ℓ (.refresh X) s) hp
      exact (refresh_row_iff Bt κ hκ D u ℓ X f s hrow
        ((Nat.succ_le_succ (hr s).2.2).trans (hr s).2.1) hW hpanel).symm

end P1SolGreedy.SolBridge

open P1SolGreedy.SolBridge

set_option maxHeartbeats 800000 in
theorem P1SolGreedy.bridgeRefreshE {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias) :
    P1ChkFinal.GreedyBridge.BridgeRefreshTargetE Bt κ hκ V a b x d bigBias termBias hH hE := by
  intro ℓ hℓ hkind u t ht hprev hp
  exact refresh_of_located Bt κ hκ _ _ ℓ _ hkind
    (fixed_located Bt κ hκ V a b x d bigBias termBias hH hE hℓ u t ht hprev hp)

#print axioms P1SolGreedy.bridgeRefreshE
