import P1Int.FormC14
import P1Int.FormAg
import P1ChkDir.D5Steps

/-!
# The bridge of group `c4` (P1-lean-integ, statements only)

`P1ChkDir.d5_c4w_step` (lane checks) gives: under a true directory, checks C4 pass iff `c4Rhs` (every level-0 panel
field at the address `addrL y` holds the panel of `stateNet` of the STORED skeleton, read with the layout `dirAt`).
`G.c4 = c4G` (FormAg.lean) is the tuple form (some tuple agrees on the trit section and on all level-0 panel sections).

* `c4Rhs H τ u`: the right side of `d5_c4w_step` at `genuineC4Dims` (`D = fixedDims`, `h = Params.h`,
  `Wc = Ws = strWidth`, `Wt = tupWidth`, i.e. `stateNet = rnState`), degree exponent `S.degreeExponent 0`
  (`four_le_baseDegree S`), tape numbering `τ`.
* `C4BridgeTarget`: for `0 < d`, a tape numbering `τ` that is `H.tape_order`, and a true directory: `c4Rhs ↔ c4G`.
  Tools: `dir_exists` (FormC14.lean), `panelLink` (DirLink.lean), `dirTrue_dirAt` (C4Wired.lean).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **The right side of the C4 stage at the fixed code.** -/
def c4Rhs [NeZero (fixedDims Bt V a b x d bigBias termBias).I] (τ : (toOAI V).K → ℕ)
    (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∀ y, P1ChkDir.PanelStored (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) (P1ChkDir.addrL y)
    (P1P7.panel (P1Net.stateNet (K := (toOAI V).K) (fixedDims Bt V a b x d bigBias termBias).I
      ((P1ChkDir.dirAt (fixedDims Bt V a b x d bigBias termBias) τ (fixedDims Bt V a b x d bigBias termBias).I
        (2 ^ P1Wrap.Params.h (lpTime a b x.length))).sigmaS (List.ofFn u))
      (four_le_baseDegree S)
      (P1Net.strWidth (toOAI V) (P1Wrap.Params.B (lpTime a b x.length)))
      (P1Net.strWidth (toOAI V) (P1Wrap.Params.B (lpTime a b x.length)))
      (P1Net.tupWidth (toOAI V) (P1Wrap.Params.B (lpTime a b x.length)))) y)

/-- **Target: the C4 bridge** (`c4Rhs ↔ c4G` under a true directory). -/
def C4BridgeTarget [NeZero (fixedDims Bt V a b x d bigBias termBias).I]
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  0 < d → ∀ (τ : (toOAI V).K → ℕ), (∀ kk, (H.tape_order kk : ℕ) = τ kk) →
    ∀ u : Fin (fixedM Bt a b x) → Bool, dirG Bt κ hκ V a b x d bigBias termBias H u →
      (c4Rhs Bt V a b x d bigBias termBias τ u ↔ c4G Bt κ hκ V a b x d bigBias termBias H u)

end

end P11

end P1Int
