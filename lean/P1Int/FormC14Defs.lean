import P1Int.FormDirDefs
import P1ChkDir.D5Steps

/-!
# The group `c14` at the fixed code, its form pieces, and `DirExists` (P1-lean-integ, statements only)

* `c14G H u`: the right side of `P1ChkDir.d5_c14_step` at `fixedDims`, `ρ = H.tape_order`, `M = toOAI V`,
  `B = Params.B (lpTime a b |x|)`, guess length `g = a (|x|² + 1)`: the stored guess owners are the least owners
  and no guess cell is unowned. The group predicate `G.c14`.
* `DirExistsTarget`: a true directory is the directory of SOME tuple: some tuple agrees with `u` on the trit section.
* `C14SoundTarget`: the code of every tuple with `unowned = 0` satisfies `c14G` (piece of `FormSound`; `Valid`
  includes `unowned = 0`).
* `C14FixTarget`: a true directory, `c14G` and an agreeing trit section give an agreeing guess section
  (piece of `FormFix`).
* `C14CloseTarget`: `c14G` and an agreeing trit section give `unowned t.1 = 0` (piece of `FormClose`).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1Wit OAI.DepthThreeLowerBound

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Group `c14` at the fixed code.** -/
def c14G (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  (∀ q, P1ChkDir.gOwnS (P1ChkDir.dirP6 (fixedDims Bt V a b x d bigBias termBias) H.tape_order)
      (P1ChkDir.guessP6 (fixedDims Bt V a b x d bigBias termBias) (toOAI V).inputTape fun q => ((q : ℕ) : ℤ))
      (List.ofFn u) q =
    some (P1ChkDir.gOwnT
      (P1ChkDir.guessP6 (fixedDims Bt V a b x d bigBias termBias) (toOAI V).inputTape fun q => ((q : ℕ) : ℤ))
      (fixedDims Bt V a b x d bigBias termBias).N
      ((P1ChkDir.dirP6 (fixedDims Bt V a b x d bigBias termBias) H.tape_order).sigmaS (List.ofFn u)) q)) ∧
  unownedCount (B := P1Wrap.Params.B (lpTime a b x.length))
    (withGuessLayout (M := toOAI V) x (a * (x.length ^ 2 + 1)))
    ((P1ChkDir.dirP6 (fixedDims Bt V a b x d bigBias termBias) H.tape_order).sigmaS (List.ofFn u))
    (fixedDims Bt V a b x d bigBias termBias).N (fixedDims Bt V a b x d bigBias termBias).I = 0

/-- **DirExists**: a true directory is the directory of some tuple (agreeing trit section). `0 < d` is needed: for
`d = 0` there is no chain `Fin (P + 1) → Fin 0`, so no tuple (counterexample of Sol formc14, 13:38Z); in the final
theorem `d` is the dimension of the field `F` over `ZMod 2`, so `0 < d`. -/
def DirExistsTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  0 < d → ∀ u : Fin (fixedM Bt a b x) → Bool, dirG Bt κ hκ V a b x d bigBias termBias H u →
    ∃ t : (fixedCD Bt κ hκ V a b x).Tup d, SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit

/-- Piece of `FormSound`: the code of every tuple with no unowned guess cell satisfies `c14G`. -/
def C14SoundTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ t : (fixedCD Bt κ hκ V a b x).Tup d, (fixedCD Bt κ hκ V a b x).unowned t.1 = 0 →
      c14G Bt κ hκ V a b x d bigBias termBias H (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)

/-- Piece of `FormFix`: a true directory, `c14G` and an agreeing trit section give an agreeing guess section. -/
def C14FixTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    dirG Bt κ hκ V a b x d bigBias termBias H u →
    c14G Bt κ hκ V a b x d bigBias termBias H u →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secGuess

/-- Piece of `FormClose`: `c14G` and an agreeing trit section give `unowned t.1 = 0`. -/
def C14CloseTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    dirG Bt κ hκ V a b x d bigBias termBias H u →
    c14G Bt κ hκ V a b x d bigBias termBias H u →
    SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit →
    (fixedCD Bt κ hκ V a b x).unowned t.1 = 0

end

end P11

end P1Int
