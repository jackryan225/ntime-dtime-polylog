import P1Int.FormGroups
import P1Int.TrueH
import P1SolCone.Wof

/-!
# The W link (P1-lean-integ, statements only; tracker p11_wlink)

The cone lane's `P1SolCone.wof_def_ok` gives `Wof .. x u v = W_v` for `u` = the code of a genuine tuple, under
`BranchExtras D u E origins ι 0` (the decoded colour / offset / layout / term tables of `u` along the branch `ι` are the
true OpenAI data) and `tape_order = ρ`. For the TRUE records `trueH` the tape order is `Fintype.equivFin` (`fixedTapeOrder`,
Records.lean). The one open piece is `BranchExtrasTarget`: the code of every tuple of `trueH` satisfies `BranchExtras`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone P1Wit P1Wit.SolWitfill OAI.Computability.VPVNP.CompressorRecords

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Target (Sol): `BranchExtras` for the code of every tuple of the true records.** -/
def BranchExtrasTarget : Prop :=
  ∀ (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias),
    EncFits Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) →
    ∀ t : (fixedCD Bt κ hκ V a b x).Tup d,
      BranchExtras Bt κ hκ (fixedDims Bt V a b x d bigBias termBias)
        (List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) t))
        (netExecution Bt κ hκ V (P1Wrap.Params.B (lpTime a b x.length)) (P1Wrap.Params.I 1 (lpTime a b x.length))
          (h := P1Wrap.Params.h (lpTime a b x.length)) (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
          (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length)) t.1)
        (executeOrigins Bt κ hκ (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
          (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
          (routedState (S := S) V (P1Wrap.Params.B (lpTime a b x.length)) (P1Wrap.Params.I 1 (lpTime a b x.length))
            (h := P1Wrap.Params.h (lpTime a b x.length)) t.1))
        t.2.1 0

end

end P11

end P1Int
