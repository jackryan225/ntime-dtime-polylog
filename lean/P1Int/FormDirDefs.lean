import P1Int.FormDefs
import P1Int.ComposeDir
import P1Int.DirLink

/-!
# The group `dir` at the fixed code and its two form pieces (P1-lean-integ, statements only)

* `dirG H u`: lane checks' `DirTrue` for the layout `dirP6 (fixedDims ..) H.tape_order` on `List.ofFn u`
  (the group predicate `G.dir`; the step is `d5_dir_step`, ComposeDir.lean).
* `DirSoundTarget`: the code of every tuple has a true directory (piece of `FormSound`).
* `DirFixTarget`: a true directory and an agreeing trit section give agreeing start / prev / next sections
  (piece of `FormFix`).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Group `dir` at the fixed code.** -/
def dirG (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  P1ChkDir.DirTrue (P1ChkDir.dirP6 (fixedDims Bt V a b x d bigBias termBias) H.tape_order) (List.ofFn u)

/-- Piece of `FormSound`: the code of every tuple has a true directory. -/
def DirSoundTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ t : (fixedCD Bt κ hκ V a b x).Tup d,
      dirG Bt κ hκ V a b x d bigBias termBias H (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)

/-- Piece of `FormFix`: a true directory and an agreeing trit section give agreeing directory sections. -/
def DirFixTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    dirG Bt κ hκ V a b x d bigBias termBias H u →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secStart ∧
      SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secPrev ∧
      SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secNext

end

end P11

end P1Int
