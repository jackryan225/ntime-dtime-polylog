import P1Int.FormDefs
import P1ChkFinal.Wired

/-!
# The group `c11` at the fixed code and its two form pieces (P1-lean-integ, statements only)

* `c11G H u`: the right side of `P1ChkFinal.C11w_iff` at `fixedDims` (the stored Omega numbers are the prefix sums of
  the stored final-level base widths); the group predicate `G.c11`.
* `C11SoundTarget`: the code of every tuple satisfies `c11G` (piece of `FormSound`).
* `C11FixTarget`: all level sections agreeing and `c11G` give an agreeing Omega section (piece of `FormFix`).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Group `c11` at the fixed code** (`H` enters only through the type). -/
def c11G (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∀ y < P1ChkFinal.finN (fixedDims Bt V a b x d bigBias termBias),
    P1Wit.rdOmega (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) y =
      P1ChkFinal.pre (P1ChkFinal.wsOf (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u)) y

/-- Piece of `FormSound`: the code of every tuple satisfies `c11G`. -/
def C11SoundTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ t : (fixedCD Bt κ hκ V a b x).Tup d,
      c11G Bt V a b x d bigBias termBias (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)

/-- Piece of `FormFix`: agreeing level sections (all levels `0 .. top`) and `c11G` give an agreeing Omega section. -/
def C11FixTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    LevUpTo Bt κ hκ V a b x d bigBias termBias H u t ((fixedDims Bt V a b x d bigBias termBias).top + 1) →
    c11G Bt V a b x d bigBias termBias u →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t (fixedDims Bt V a b x d bigBias termBias).secOmega

end

end P11

end P1Int
