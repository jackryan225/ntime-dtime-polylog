import P1Wit.WitNetTuple
import P1Int.NetGlue

namespace P1Wit

open OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11 SolWitfill

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h)
  {D : Dims} {d : ℕ} (H : NetRecordInputs Bt κ hκ V Bk I Tc hn D d)

/-- The witness records for the exact `NetData` consumed by `CountInput`. -/
def p11TupleRecords :
    TupleRecords D (netData Bt κ hκ V a x Bk I Tc hn (netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData d :=
  let C := netData Bt κ hκ V a x Bk I Tc hn (netSiteOrder Bt κ hκ V Bk I Tc hn)
  SolWitfill.netTupleRecords Bt κ hκ V Bk I Tc hn (netF1 V a x Bk I h (four_le_baseDegree S) F)
    C.unowned C.acc H

omit [Algebra (ZMod 2) F] in
/-- The S3 bits in the P11 witness have the final state's total width. -/
theorem p11Tuple_payload_length
    (t : (netData Bt κ hκ V a x Bk I Tc hn (netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) :
    (tuplePayload (p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).length =
      ((netExecution Bt κ hκ V Bk I Tc hn t.1).finalState t.2.1).totalWidth :=
  let C := netData Bt κ hκ V a x Bk I Tc hn (netSiteOrder Bt κ hκ V Bk I Tc hn)
  netTuple_payload_length Bt κ hκ V Bk I Tc hn (netF1 V a x Bk I h (four_le_baseDegree S) F)
    C.unowned C.acc H t

omit [Algebra (ZMod 2) F] in
/-- The exact `hinj` input to P11, with the D9 site order. -/
theorem encNetTuple_injective (m : ℕ)
    (hm : ∀ t, D.fixedLen + (tuplePayload (p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).length ≤ m) :
    Function.Injective (encTuple (p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) m :
      (netData Bt κ hκ V a x Bk I Tc hn (netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d →
        (Fin m → Bool)) :=
  encTuple_injective _ m hm

end

end P1Wit

#print axioms P1Wit.p11TupleRecords
#print axioms P1Wit.p11Tuple_payload_length
#print axioms P1Wit.encNetTuple_injective
