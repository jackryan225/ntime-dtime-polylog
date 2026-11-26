import P1Int.WitfillLink
import P1ChkFinal.Skeleton
import P1ChkFinal.C10RcCodes
import P1P5.KernelWriter

/-!
# P1, level-0 factors from the witness: the FROZEN target `P1P5.F0.Factor0Hyp` (owner P1-lean-eval, 13:45Z)

Text copied UNCHANGED (only the namespace) from the cone prover's file research/agents/P1-sol-cone/lean/P1SolCone/Factor0.lean
(sha256 baafb89a..), on G3-chief's order (board 2208): the header reader (rule codes of the D9 level-0 requests from `x` and the
P6 skeleton in `u`, crossing bits) on top of the PROVED `P1SolFactor.factor0EntryPoly` / `P1SolFactor.crossPoly`. One `Code`
program reads the needed level-0 data in batch and returns the factors in request order; scalar 1 gives `netF1`.
-/

namespace P1P5.F0

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.DepthThreeLowerBound
open P1Int P1Int.P11
open P1Wit P1Wit.SolWitfill
open scoped Classical P1ChkFinal.AstraC10

/-- The input, witness, scalar and requested level-zero entries in cone order. -/
abbrev Factor0In (F : Type) := (List Bool × List Bool) × (Label F × List P1P5.KW.PosCode)

namespace SolCone

abbrev SwitchSettings :=
  ∀ (m : ℕ) [NeZero m], Equiv.Perm (P1Net.Routing.Addr m) → P1Net.Routing.Settings m

def factor0Agreement {F : Type} [CommRing F] (evaluate : Factor0In F → List (Label F))
    (V : C1Challenge.Machine) (a B I : ℕ) [NeZero B] [NeZero I]
    {a₀ h : ℕ} (ha₀ : 4 ≤ 2 ^ a₀) (σ : RoutedSkeleton V I h)
    (x u : List Bool) (bset : SwitchSettings) : Prop :=
  let X := P1Net.rnState (h := h) (toOAI V) B I σ ha₀
  ∀ (c : F) (entries : List (Σ s : X.network.Site, X.network.Half s)),
    let requests := entries.map fun z =>
      ((P1P7.addr X z.1.1, P1ChkFinal.bwNum z.1.2), P1P5.KW.halfCode X z.1 z.2)
    evaluate ((x, u), (⟨c⟩, requests)) = entries.map fun z =>
      let ok := P1Net.rnSiteOK (h := h) (toOAI V) B (netLayout V a x) I σ ha₀ bset z.1 z.2
      ⟨c * @ite F ok (Classical.propDecidable ok) 1 0⟩

end SolCone

/-- The pending factor0 interface. A single program reads the required level-zero data in
batch and produces the factors in request order. Setting the scalar to one gives `netF1`. -/
def Factor0Hyp {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F]
    (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ) (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K))
    (bset : SolCone.SwitchSettings) : Prop :=
  ∃ (evaluate : Factor0In F → List (Label F)) (e : ℕ),
    Computes (fun p : Factor0In F => p.1.1.length + p.1.2.length +
      (size p.2 + Nat.log 2 (p.1.1.length + 1) + 1) ^ e) evaluate ∧
    ∀ (x : List Bool),
      let t := lpTime a b x.length
      let B := P1Wrap.Params.B t
      let I := P1Wrap.Params.I 1 t
      let h := P1Wrap.Params.h t
      let T := P1Wrap.Params.T (portConsts Bt) t
      let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
      ∀ (H : FixedRecords Bt κ hκ V a b x d bigBias termBias),
        (∀ tape, (H.tape_order tape).val = (ρ tape).val) →
        let C := netData Bt κ hκ V a x B I (h := h) T hn (netSiteOrder Bt κ hκ V B I (h := h) T hn)
        let A := p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H
        ∀ (q : C.toCountData.Tup d) (m : ℕ),
          (fixedDims Bt V a b x d bigBias termBias).fixedLen + (tuplePayload A q).length ≤ m →
          SolCone.factor0Agreement evaluate V a B I (h := h) (four_le_baseDegree S) q.1
            x (List.ofFn (encTuple A m q)) bset

end P1P5.F0


