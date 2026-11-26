import P1Int.FormGroups

/-!
# `FormClose` for the fixed groups (P1-lean-integ, statements only)

`FormCloseAsmTarget H`: from `EncFits H`, the piece `C14CloseTarget H` (PROVED, FormC14.lean), a W link for `Wof`
(the evaluation of `W_v` from the witness agrees with `C.W` on the CODE of every tuple; for `H = trueH` this is the W link
of WLinkDefs.lean with `wof_def_ok`) and the chain length `finP fixedDims = P σ ι`, `FormClose` holds for the fixed
groups. Route (board 13:37Z): from `u` and a tuple `t` agreeing on every section except the chain, build
`t' := (t.1, t.2.1, z, j)` with `z` = the payload read from `u` (`c12G`: long enough, zero tail; the final widths of `u`
are those of `t`) and `j` = the chain read from `u` (`c13G`); then `fixedEnc H t' = u` by `encOfAgree` (FormLev.lean),
and only then the W link at `u = fixedEnc H t'` gives `ChainOK` of `C.W`; `c14_close` gives `unowned = 0`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Target: `FormClose` for the fixed groups.** -/
def FormCloseAsmTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
  C14CloseTarget Bt κ hκ V a b x d bigBias termBias H →
  ∀ (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F),
    (∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (i : Fin ((fixedCD Bt κ hκ V a b x).P t.1 t.2.1)),
      Wof x (List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)) i =
        (fixedCD Bt κ hκ V a b x).W t.1 t.2.1 t.2.2.1 i) →
    (∀ σ ι, P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias) = (fixedCD Bt κ hκ V a b x).P σ ι) →
    ∀ cnt : ℕ → ℕ,
      FormClose Bt κ hκ V a b x bigBias termBias bs l H (fixedIndex Bt V a b x d bigBias termBias cnt)
        (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof)

end

end P11

end P1Int
