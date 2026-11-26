import P1Int.FormGroups

/-!
# `FormSound` for the fixed groups (P1-lean-integ, statements only)

`FormSoundAsmTarget H`: from `EncFits H`, a W link for `Wof` (the evaluation of `W_v` from the witness agrees with `C.W`
on the code of every tuple) and the chain length `finP fixedDims = P σ ι`, the code of every VALID tuple satisfies every
group of `fixedGroups`. Pieces (all PROVED): `dir_sound` (FormDir), `c14_sound` (FormC14; `Valid` gives `unowned = 0`),
`secEq_enc` (FormLev; gives `c4G` with the tuple itself), `levels_sound` (FormLev; greedyG, c10G below top),
`c11_sound` (FormC11); new here: `c12G` of a code (payload length = prefix of the final widths, zero tail) and `c13G` of
a code (stored chain = the chain of the tuple; `ChainOK` of `Wof` = `ChainOK` of `C.W` by the W link).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Target: `FormSound` for the fixed groups.** -/
def FormSoundAsmTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
  ∀ (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F),
    (∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (i : Fin ((fixedCD Bt κ hκ V a b x).P t.1 t.2.1)),
      Wof x (List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)) i =
        (fixedCD Bt κ hκ V a b x).W t.1 t.2.1 t.2.2.1 i) →
    (∀ σ ι, P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias) = (fixedCD Bt κ hκ V a b x).P σ ι) →
    ∀ cnt : ℕ → ℕ,
      FormSound Bt κ hκ V a b x bigBias termBias bs l H (fixedIndex Bt V a b x d bigBias termBias cnt)
        (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof)

end

end P11

end P1Int
