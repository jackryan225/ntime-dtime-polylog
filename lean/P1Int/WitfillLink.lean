import P1Int.Assembly
import P1Wit.WitGenuineEncoder

/-!
# P1Int.WitfillLink: the witness code of Sol witfill at the fixed parameters of `ChecksHyp`

Owner: P1-lean-integ (Opus restart, 2026-11-25). Integration of the outside prover P1-sol-witfill (DONE 11:59:50Z,
files copied UNCHANGED into research/p1/lean/Wit/P1Wit/Wit*.lean, sha256 = research/agents/P1-sol-witfill/DONE.md).

* `witfill_fixed`: at the fixed parameters of `P1Int.Assembly` (`K = portConsts Bt`, `aM = 1`, `t = lpTime a b |x|`,
  `n = |x|`), for every large input `x` and EVERY record package `H : NetRecordInputs ..` at the genuine dimensions,
  the explicit code `encTuple (p11TupleRecords .. H) m` with the site order `netSiteOrder` (D9) is injective; its type
  is written out exactly as the binder `enc` of `ChecksHyp` (so the check below is a type check by elaboration).
* `ChecksRec Bt κ hκ bs l`: `ChecksHyp` with the order and the code FIXED to witfill's; the records `H` and the two
  format constants `bigBias`, `termBias` are existential. Left open in it: alphabet, programs, totality, the records
  `H` (the TRUE records: the values that the checks force) and `hchecks` for this code.
* `OpenChecksRec` (`ChecksRec` for the data of every port).
* The glue `checksHyp_of_rec : ChecksRec → ChecksHyp` and `openChecks_of_rec : OpenChecksRec → OpenChecks` is in
  `P1Int.WitfillGlue`.
-/

namespace P1Int

namespace P11

open Filter Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression OAI.Computability.VPVNP.WireTensor

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- The genuine witness dimensions at the fixed parameters (`aM = 1`, `K = portConsts Bt`, `t = lpTime a b |x|`,
guess length `a (|x|² + 1)`). -/
abbrev fixedDims (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) : P1Wit.Dims :=
  P1Wit.SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1 (lpTime a b x.length) (a * (x.length ^ 2 + 1)) d
    bigBias termBias

/-- The record package of Sol witfill at the fixed parameters. -/
abbrev FixedRecords (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) : Type :=
  P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V (P1Wrap.Params.B (lpTime a b x.length))
    (P1Wrap.Params.I 1 (lpTime a b x.length)) (h := P1Wrap.Params.h (lpTime a b x.length))
    (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
    (fixedDims Bt V a b x d bigBias termBias) d

/-- The D9 site order at the fixed parameters (`P1Wit.netSiteOrder`). -/
abbrev fixedOrd (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) :=
  P1Wit.netSiteOrder Bt κ hκ V (P1Wrap.Params.B (lpTime a b x.length))
    (P1Wrap.Params.I 1 (lpTime a b x.length)) (h := P1Wrap.Params.h (lpTime a b x.length))
    (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))

/-- The witness code of Sol witfill at the fixed parameters, typed EXACTLY as the binder `enc` of `ChecksHyp`
(with `ord := fixedOrd`). -/
abbrev fixedEnc (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
        (P1Wrap.Params.I 1 (lpTime a b x.length))
        (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
        (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
        (fixedOrd Bt κ hκ V a b x)).toCountData.Tup d →
      (Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool) :=
  P1Wit.encTuple (P1Wit.p11TupleRecords Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
    (P1Wrap.Params.I 1 (lpTime a b x.length)) (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length)) H)
    (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)

/-- **Sol witfill at the fixed parameters**: for all long inputs and every record package, the code is injective. -/
theorem witfill_fixed (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) :
    ∃ n₂ : ℕ, ∀ x : List Bool, n₂ ≤ x.length →
      ∀ H : FixedRecords Bt κ hκ V a b x d bigBias termBias,
        Function.Injective (fixedEnc Bt κ hκ V a b x d bigBias termBias H) := by
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1
    (P1Wit.encGenuineNetTuple_injective Bt κ hκ (portConsts Bt) V 1 le_rfl (portConsts_b0 Bt)
      (portConsts_C2 Bt) d bigBias termBias a b)
  refine ⟨n₂, fun x hx H => ?_⟩
  exact hn₂ x.length hx x H

/-! ## `ChecksHyp` with the code fixed to witfill's -/

variable {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

open scoped Classical in
/-- **`ChecksHyp` with witfill's order and code.** Open in it: the alphabet, the check programs `chk`, the
constant `c ≥ 1`, the threshold `n₁`, the format constants `bigBias`, `termBias`, totality within `chkBudget`, the
TRUE records `H` per input, and `hchecks` for the code `fixedEnc .. H`. -/
def ChecksRec : Prop :=
  ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A)) (c n₁ bigBias termBias : ℕ), 1 ≤ c ∧
    ∀ x : List Bool, n₁ ≤ x.length →
      (∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
        ∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc →
        ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
          ∃ v, ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) v
            (chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)) ∧
      ∃ H : FixedRecords Bt κ hκ V a b x D bigBias termBias,
        ∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
          (∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc → ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
            ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true
              (chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)) ↔
          ∃ t, (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (fixedOrd Bt κ hκ V a b x)).toCountData.Valid bs l t ∧
            fixedEnc Bt κ hκ V a b x D bigBias termBias H t = u

end

/-- **Open input 2 in witfill form**: `ChecksRec` for the data of every port. -/
def OpenChecksRec : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ChecksRec Bt κ hκ bs l

end P11

end P1Int
