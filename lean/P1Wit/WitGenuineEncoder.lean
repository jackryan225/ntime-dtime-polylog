import P1Wit.WitCountInput
import P1Int.WitnessFit

namespace P1Wit

open Filter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11
open P1Wrap (Consts)
open P1Wrap.W3 (sOf)
open SolWitfill

/-- At the genuine dimensions and the Lemma P witness length, the encoder
for `NetInput` is injective once its bounded local records are supplied. -/
theorem encGenuineNetTuple_injective {k : Type*} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F]
    (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (K : Consts) (V : C1Challenge.Machine)
    (aM : ℕ) (haM : 1 ≤ aM) (hb0 : S.laneBits ≤ K.b0) (hC2 : Bt.growthConstant ≤ K.C2)
    (d bigBias termBias a b : ℕ) :
    ∀ᶠ n in atTop,
      let t := lpTime a b n
      let Bk := P1Wrap.Params.B t
      let I := P1Wrap.Params.I aM t
      let h := P1Wrap.Params.h t
      let Tc := P1Wrap.Params.T K t
      let hn := lane_bound K S.laneBits hb0 t
      let D := SolSpace.genuineDims Bt K (toOAI V) aM t (a * (n ^ 2 + 1)) d bigBias termBias
      let m := lpM2 (sOf K.j) a b n
      ∀ [NeZero Bk] [NeZero I] (x : List Bool)
        (H : NetRecordInputs Bt κ hκ V Bk I (h := h) Tc hn D d),
      let ord := netSiteOrder Bt κ hκ V Bk I (h := h) Tc hn
      let enc : (netData Bt κ hκ V a x Bk I Tc hn ord).toCountData.Tup d → (Fin m → Bool) :=
        encTuple (p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) m
      Function.Injective enc := by
  filter_upwards [witness_fits Bt κ hκ K V aM haM hb0 hC2 d bigBias termBias a b] with n hfit
  dsimp only
  intro instB instI x H
  apply encNetTuple_injective
  intro u
  rw [p11Tuple_payload_length]
  exact @hfit instB instI u.1 u.2.1

end P1Wit

#print axioms P1Wit.encGenuineNetTuple_injective
