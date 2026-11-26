import P1Int.D5Asm
import P1Int.FormTrue
import P1Int.SizeFacts
import P1Int.EncFitsTrue
import P1Int.C10Check
import P1ChkFinal.FamClosed
import P1ChkFinal.FamGreedyAg
import P1ChkFinal.FamFinal
import P1ChkFinal.GreedyFieldTarget
import P1ChkFinal.GreedyBridgeE
import P1C10.FamClosed
import P1C10.Out
import P1P5.ConeTarget

/-!
# The named inputs of the final wiring (P1-lean-integ, statements only)

`OpenChecksStaged` (ComposeStage.lean) is to be proved from `FinalInputs` (= `FinalWiringTarget`). The inputs that other
lanes still owe, each at the real parameters (`portConsts Bt`, `toOAI V`, `aM = 1`, chain dimension `d`, true records):

* `ConeIn`: the cone program (`ConeTarget` at `ρ = Fintype.equivFin`): values, `ScheduleKernelsOK`, `WHyp` (P1-lean-eval).
* `Factor0In`: `Factor0Hyp` with the tape order `Fintype.equivFin` and the Beneš settings `bset` (P1-lean-eval).
* `GreedyIn`: the two bridges with `hE` (P1-lean-greedy; GreedyBridgeE.lean); `EnergyFitIn`: the energy fit (D16).
* `DispIn`: the dispatcher (P1-lean-disp): 16 programs with `FamProg` for the deciders `ck`, and for long inputs the
  deciders as the lanes' families at the fixed dims, the counts `cnt`, their fit into `2 ^ (lpK2 a b |x| - 4)` index
  words, and the field `out`.
Proved and used by the wiring (mine): `d5Steps_asm`, `form_true` (via its pieces), `c4_bridge`, `sizeFacts`,
`encFits_true`, `wlink_true`, `trueH_facts`, `P1C10.c10_field_closed`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- **Input (eval): the cone program** (= `P1P5.Cone.ConeTarget` at `ρ = Fintype.equivFin` with the kernel programs
discharged): kernel values with `ScheduleKernelsOK` and the D14 program `WHyp` of the cone's `Wof`. -/
def ConeIn [Fintype F] (d : ℕ) (bs : Module.Basis (Fin d) (ZMod 2) F) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b bigBias termBias : ℕ), 1 ≤ b →
    ∀ hf : Factor0Hyp Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) P1Benes.NetBridge.bset,
    ∃ (values : KernelValues F) (cW : ℕ), ScheduleKernelsOK Bt κ hκ values ∧
      ∀ M K : ℕ → ℕ, P1ChkFinal.WHyp bs (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) M K
        (P1SolCone.βW Bt V a b cW)

/-- **Input (eval): `Factor0Hyp` at every machine and parameters.** -/
def Factor0In [Fintype F] (d : ℕ) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b bigBias termBias : ℕ), 1 ≤ b →
    Factor0Hyp Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) P1Benes.NetBridge.bset

/-- **Input (greedy): the two bridges** (with the energy fit `hE`, decision D16), for the true records at every input.
The greedy field itself is PROVED from them (`P1ChkFinal.GreedyBridge.greedyFieldE`). -/
def GreedyIn (d : ℕ) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (bigBias termBias : ℕ)
    (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias),
    P1ChkFinal.GreedyBridge.BridgeShrinkTargetE Bt κ hκ V a b x d bigBias termBias hH hE ∧
    P1ChkFinal.GreedyBridge.BridgeRefreshTargetE Bt κ hκ V a b x d bigBias termBias hH hE

/-- **Input (greedy): the energy fit for long inputs** (decision D16; = `EnergyFitLong` at this port). -/
def EnergyFitIn (d : ℕ) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b bigBias termBias : ℕ), 1 ≤ b → ∃ n₇ : ℕ, ∀ x : List Bool, n₇ ≤ x.length →
    P1ChkFinal.EnergyFit.EnergyFitTarget Bt κ hκ V a b x d bigBias termBias

open Classical in
/-- **Input (disp): the dispatcher.** For the cone's `Wof` (kernel `values`, `hf : Factor0Hyp`): sixteen programs with
`FamProg` for the deciders `ck`, and for long inputs the deciders are the lanes' families at the fixed dims, the counts,
their fit, and the field `out` at `fixedIndex (cnt |x|)`. -/
def DispIn [Fintype F] (d : ℕ) (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b bigBias termBias : ℕ) (values : KernelValues F)
    (_hv : ScheduleKernelsOK Bt κ hκ values)
    (hf : Factor0Hyp Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) P1Benes.NetBridge.bset)
    (cW : ℕ) (_hW : ∀ M K : ℕ → ℕ,
      P1ChkFinal.WHyp bs (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) M K (P1SolCone.βW Bt V a b cW)),
    1 ≤ b →
  ∃ (chk : ℕ → Option (Prog Ltr)) (ck : ℕ → List Bool → List Bool → ℕ → Bool) (cnt : ℕ → ℕ → ℕ),
    (∀ c' < 2 ^ 4, ∃ Rc, chk c' = some Rc ∧ ∃ cc n₂ : ℕ,
      FamProg Ltr.bit P1Dispatch.answer Rc (ck c') ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂) ∧
    ∃ n₄ : ℕ, ∀ x : List Bool, n₄ ≤ x.length →
      -- the deciders
      (∀ u i, ck 0 x u i = true ↔ P1ChkDir.C1F (fixedDims Bt V a b x d bigBias termBias)
        (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
      (∀ u i, ck 1 x u i = true ↔ P1ChkDir.C2F (fixedDims Bt V a b x d bigBias termBias)
        (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
      (∀ u i, ck 2 x u i = true ↔ P1ChkDir.C3F (fixedDims Bt V a b x d bigBias termBias)
        (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
      (∀ u i, ck 3 x u i = true ↔ P1ChkDir.C4w (four_le_baseDegree S)
        (fun kk => ((Fintype.equivFin (toOAI V).K kk : Fin _) : ℕ)) (c4dims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 4 x u i = true ↔ P1ChkGreedy.C5fam (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 5 x u i = true ↔ P1ChkGreedy.C6fam (gdims Bt V a b d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
      (∀ u i, ck 6 x u i = true ↔ P1ChkFinal.C7R.C7all S.graph (Nat.two_pow_pos S.expanderExponent)
        (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink (gdims Bt V a b d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
      (∀ u i, ck 7 x u i = true ↔ P1SolGreedy.C8fam Bt.shrink (gdims Bt V a b d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
      (∀ u i, ck 8 x u i = true ↔ P1ChkGreedy.C9fam (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 9 x u i = true ↔ P1C10.C10w (P1C10.fx10 Bt) (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 10 x u i = true ↔ P1ChkFinal.C11w (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 11 x u i = true ↔ P1ChkFinal.C12w (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 12 x u i = true ↔ P1ChkFinal.C13linkw bs (gdims Bt V a b d bigBias termBias)
        (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) x u i) ∧
      (∀ u i, ck 13 x u i = true ↔ P1ChkFinal.C13endsw bs l (gdims Bt V a b d bigBias termBias) x u i) ∧
      (∀ u i, ck 14 x u i = true ↔ P1ChkDir.C14F (fixedDims Bt V a b x d bigBias termBias)
        (fixedTapeOrder Bt V a b x d bigBias termBias) (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) u i) ∧
      -- the counts
      cnt x.length 0 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).N *
        (fixedDims Bt V a b x d bigBias termBias).r ∧
      cnt x.length 1 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).r ∧
      cnt x.length 2 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).r * 3 * 2 ∧
      cnt x.length 3 = P1ChkDir.cnt4 (toOAI V).K (c4dims Bt V a b d bigBias termBias) x.length ∧
      cnt x.length 4 = P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias) ∧
      cnt x.length 5 = P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias) ∧
      cnt x.length 6 = P1ChkFinal.C7R.cnt7all (fixedDims Bt V a b x d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias) x.length) ∧
      cnt x.length 7 = P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias) ∧
      cnt x.length 8 = P1ChkGreedy.cntLev (fixedDims Bt V a b x d bigBias termBias) ∧
      cnt x.length 9 = P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias) ∧
      cnt x.length 10 = P1ChkFinal.cnt11 (gdims Bt V a b d bigBias termBias) x.length ∧
      cnt x.length 11 = P1ChkFinal.cnt12 (gdims Bt V a b d bigBias termBias) x.length ∧
      cnt x.length 12 = P1ChkFinal.cnt13link (gdims Bt V a b d bigBias termBias) x.length ∧
      cnt x.length 13 = P1ChkFinal.cnt13ends (gdims Bt V a b d bigBias termBias) x.length ∧
      cnt x.length 14 = (fixedDims Bt V a b x d bigBias termBias).nGB ∧
      -- the fit into the index words
      (∀ c < 15, cnt x.length c ≤ 2 ^ (lpK2 a b x.length - 4)) ∧
      -- the field `out`
      (∀ u : Fin (fixedM Bt a b x) → Bool, ∀ c < 16, ∀ i < 2 ^ (lpK2 a b x.length - 4),
        (fixedIndex Bt V a b x d bigBias termBias (cnt x.length)).stg c i = 0 → ck c x (List.ofFn u) i = true)

end

/-- **All named inputs of the final wiring**, for the data of every port (the binders of `OpenChecksStaged`). -/
def FinalInputs : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Module.Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant →
    haveI : Fintype F := Fintype.ofFinite F
    ConeIn Bt κ hκ D bs ∧ Factor0In Bt κ hκ D ∧ GreedyIn Bt κ hκ D ∧ DispIn Bt κ hκ D bs l ∧
      EnergyFitIn Bt κ hκ D

/-- **Target of the final wiring** (the proof is the wiring of the proved pieces). -/
def FinalWiringTarget : Prop := FinalInputs → OpenChecksStaged

end P11

end P1Int
