import P1Int.DirLinkProof

/-!
# P1Int.DirLink: `dirLink`, `panelLink` (owner P1-lean-integ; PROVED by Sol P1-sol-dirlink, DirLinkProof.lean copied unchanged)

`P1Int.P11.DirLinkStmt` (directory, checks C1-C3, C14) and `P1Int.P11.PanelLinkStmt` (level-0 panels, check C4),
both in DirLinkDefs.lean, for every record package `H` and every typed tuple `t`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h) {D : P1Wit.Dims} {d : ℕ}

/-- **Target (Sol).** -/
theorem dirLink (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) :
    DirLinkStmt Bt κ hκ V a x Bk I Tc hn H t :=
  dirLink_proof Bt κ hκ V a x Bk I Tc hn H t

/-- **Target 2 (Sol).** -/
theorem panelLink (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) :
    PanelLinkStmt Bt κ hκ V a x Bk I Tc hn H t :=
  panelLink_proof Bt κ hκ V a x Bk I Tc hn H t

end P11

end P1Int

universe u in
example : type_of% @P1Int.P11.dirLink.{u} = type_of% @P1Int.P11.dirLink_proof.{u} := rfl
universe u in
example : type_of% @P1Int.P11.panelLink.{u} = type_of% @P1Int.P11.panelLink_proof.{u} := rfl
#print axioms P1Int.P11.dirLink
#print axioms P1Int.P11.panelLink
