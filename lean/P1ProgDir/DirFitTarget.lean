import P1ProgDir.FamDir
import P1Int.WitnessFit
import P1Int.Assembly

/-!
# P1ProgDir.DirFitTarget: the open inputs of C1, C2, C3, C14 at the real parameters (lane P1-lean-greedy)

`famC1 .. famC14` (FamDir.lean) take three inputs. At the real parameters (`A = Bt`, `Kc = portConsts Bt`, `V = toOAI V`,
`aM = 1`, as integ's `fixedDims`):
* the tape numbering `tape n := Fintype.equivFin (toOAI V).K` (= integ's `fixedTapeOrder`, Records.lean:73; `r` of the
  genuine dims is `Fintype.card K` by `rfl`);
* the input-tape index of C14: `kIn := (toOAI V).inputTape` (integ's `c14G`, FormC14Defs.lean), `t := (equivFin K kIn : ℕ)`
  (does not depend on `n`, so `ht` holds by `rfl`);
* the witness fit: `DirFitTarget` below (target of Sol P1-sol-dirfit): for long inputs the trit section `2 I N r` fits in the
  fixed part and the fixed part fits in the witness length (from `P1Int.P11.witness_fits` and non-empty choices).
-/

namespace P1ProgDir.DirFit

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11

/-- The genuine dims at the real parameters. -/
noncomputable abbrev rD {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias n : ℕ) : P1Wit.Dims :=
  DirFinal.gD Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias n

/-- **Target of Sol P1-sol-dirfit**: the witness fit of C1, C2, C3, C14 at the real parameters, for long inputs. -/
def DirFitTarget.{u, v} : Prop :=
  ∀ {k : Type u} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {R : Type v} [CommRing R]
    (κ : Bt.Entry → R) (_hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ),
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      2 * ((rD Bt V a b d bigBias termBias n).I * (rD Bt V a b d bigBias termBias n).N *
          (rD Bt V a b d bigBias termBias n).r) ≤ (rD Bt V a b d bigBias termBias n).fixedLen ∧
        (rD Bt V a b d bigBias termBias n).fixedLen ≤ lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b n

/-- Small case of the tape numbering: integ's numbering has exactly the type that `famC1 .. famC14` need (`r = card K`). -/
noncomputable example {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias n : ℕ) : (toOAI V).K ≃ Fin (rD Bt V a b d bigBias termBias n).r :=
  Fintype.equivFin (toOAI V).K

end P1ProgDir.DirFit
