import P1Int.ComposeD5

/-!
# The field `form` of `D5Steps`: vocabulary and the cut (P1-lean-integ, statements only)

At the fixed parameters (`fixedDims`, `fixedEnc .. H`) the witness is `u : Fin m → Bool`, `w = List.ofFn u`.

* `SecEq u t s`: section `s` of the stored witness (`P1Wit.dec`) equals section `s` of the fields of tuple `t`
  (`P1Wit.ofTuple` of witfill's records `H`), at every entry `i < count s`.
* `LevUpTo u t L`: all sections of the levels `ℓ < L` agree.
* THE LEVEL GROUPS (the vocabulary of `D5Groups.greedy` and `D5Groups.c10`, fixed here by the integration lane):
  - `greedyG l u` = some tuple agrees with `u` on the trit section and on ALL sections of the levels `0 .. l`;
  - `c10G l u` = the same, and moreover on the PANEL sections (`panelKind`: outAddr .. width) of level `l + 1`.
* `FormStmt X G` = the type of the field `D5Steps.form`.
* The cut: `FormSound` (every valid tuple's code satisfies all groups), `FormFix` (all groups give a tuple that
  agrees with `u` on every fixed section except the chain), `FormClose` (the payload, the tail, the chain and the
  chain check give a valid tuple with code `u`). `form_of_cut` (proved here) assembles them.
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- The count data at the fixed parameters (the domain of `fixedEnc`). -/
abbrev fixedCD : P1Count.CountData F :=
  (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
    (P1Wrap.Params.I 1 (lpTime a b x.length))
    (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
    (fixedOrd Bt κ hκ V a b x)).toCountData

/-- The witness length at the fixed parameters. -/
abbrev fixedM : ℕ := lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length

variable (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)

/-- Witfill's tuple records at the fixed parameters (the records inside `fixedEnc .. H`). -/
abbrev fixedTR :=
  P1Wit.p11TupleRecords Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
    (P1Wrap.Params.I 1 (lpTime a b x.length)) (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length)) H

/-- **Section `s` of the stored witness `u` equals section `s` of the fields of the tuple `t`.** -/
def SecEq (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d) (s : ℕ) : Prop :=
  ∀ i < (fixedDims Bt V a b x d bigBias termBias).count s,
    (P1Wit.dec (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u)).val
        (fixedDims Bt V a b x d bigBias termBias) s i =
      (P1Wit.ofTuple (fixedTR Bt κ hκ V a b x d bigBias termBias H) t).val
        (fixedDims Bt V a b x d bigBias termBias) s i

/-- All sections of the levels `ℓ < L` agree. -/
def LevUpTo (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d) (L : ℕ) : Prop :=
  ∀ ℓ < L, ∀ kk : P1Wit.Mem, SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev ℓ kk)

/-- The panel kinds of a level (the fields set by checks C4 and C10). -/
def panelKind : P1Wit.Mem → Bool
  | .outAddr | .outDisp | .outFar | .inAddr | .inDisp | .inFar | .width => true
  | _ => false

/-- **Group `greedy l` (C5-C9 at level `l`)**: some tuple agrees with `u` on the trit section and on all sections of
the levels `0 .. l`. -/
def greedyG (l : ℕ) (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∃ t : (fixedCD Bt κ hκ V a b x).Tup d, SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit ∧
    LevUpTo Bt κ hκ V a b x d bigBias termBias H u t (l + 1)

/-- **Group `c10 l` (C10 at level `l`)**: as `greedyG l`, and moreover the panel sections of level `l + 1` agree. -/
def c10G (l : ℕ) (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∃ t : (fixedCD Bt κ hκ V a b x).Tup d, SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit ∧
    LevUpTo Bt κ hκ V a b x d bigBias termBias H u t (l + 1) ∧
    ∀ kk : P1Wit.Mem, panelKind kk = true →
      SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev (l + 1) kk)

variable {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

open scoped Classical in
/-- **The type of the field `D5Steps.form`** at the fixed parameters (chain dimension `D`). -/
def FormStmt (H : FixedRecords Bt κ hκ V a b x D bigBias termBias) (X : D5Index)
    (G : D5Groups (Fin (fixedM Bt a b x) → Bool)) : Prop :=
  ∀ u, (∀ j < X.K, G.P X.top j u) ↔
    ∃ t, (fixedCD Bt κ hκ V a b x).Valid bs l t ∧ fixedEnc Bt κ hκ V a b x D bigBias termBias H t = u

open scoped Classical in
/-- **Cut 1 (soundness)**: the code of every valid tuple satisfies every group. -/
def FormSound (H : FixedRecords Bt κ hκ V a b x D bigBias termBias) (X : D5Index)
    (G : D5Groups (Fin (fixedM Bt a b x) → Bool)) : Prop :=
  ∀ t, (fixedCD Bt κ hκ V a b x).Valid bs l t →
    ∀ j < X.K, G.P X.top j (fixedEnc Bt κ hκ V a b x D bigBias termBias H t)

/-- **Cut 2 (fixed fields)**: all groups give a tuple that agrees with `u` on every section except the chain. -/
def FormFix (H : FixedRecords Bt κ hκ V a b x D bigBias termBias) (X : D5Index)
    (G : D5Groups (Fin (fixedM Bt a b x) → Bool)) : Prop :=
  ∀ u, (∀ j < X.K, G.P X.top j u) → ∃ t : (fixedCD Bt κ hκ V a b x).Tup D,
    ∀ s < (fixedDims Bt V a b x D bigBias termBias).nSec, s ≠ (fixedDims Bt V a b x D bigBias termBias).secChain →
      SecEq Bt κ hκ V a b x D bigBias termBias H u t s

open scoped Classical in
/-- **Cut 3 (close)**: with the fixed sections settled, the payload, the tail, the chain section and the chain check
(groups C12, C13 and C14) give a valid tuple whose code is `u`. -/
def FormClose (H : FixedRecords Bt κ hκ V a b x D bigBias termBias) (X : D5Index)
    (G : D5Groups (Fin (fixedM Bt a b x) → Bool)) : Prop :=
  ∀ u (t : (fixedCD Bt κ hκ V a b x).Tup D), (∀ j < X.K, G.P X.top j u) →
    (∀ s < (fixedDims Bt V a b x D bigBias termBias).nSec, s ≠ (fixedDims Bt V a b x D bigBias termBias).secChain →
      SecEq Bt κ hκ V a b x D bigBias termBias H u t s) →
    ∃ t', (fixedCD Bt κ hκ V a b x).Valid bs l t' ∧ fixedEnc Bt κ hκ V a b x D bigBias termBias H t' = u

/-- **`form` from the cut.** -/
theorem form_of_cut (H : FixedRecords Bt κ hκ V a b x D bigBias termBias) (X : D5Index)
    (G : D5Groups (Fin (fixedM Bt a b x) → Bool))
    (h1 : FormSound Bt κ hκ V a b x bigBias termBias bs l H X G)
    (h2 : FormFix Bt κ hκ V a b x bigBias termBias H X G)
    (h3 : FormClose Bt κ hκ V a b x bigBias termBias bs l H X G) :
    FormStmt Bt κ hκ V a b x bigBias termBias bs l H X G := by
  intro u
  exact ⟨fun hu => Exists.elim (h2 u hu) (fun t ht => h3 u t hu ht),
    fun h => Exists.elim h (fun t ht =>
      Eq.subst (motive := fun v => ∀ j < X.K, G.P X.top j v) ht.2 (h1 t ht.1))⟩

/-! ## Targets of the Sol prover `formlev` (statements as `Prop`s; the prover proves `theorem .. : <Target>`) -/

/-- The fixed part and the payload of every tuple fit into the `m` witness bits. -/
def EncFits (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  ∀ t : (fixedCD Bt κ hκ V a b x).Tup d, (fixedDims Bt V a b x d bigBias termBias).fixedLen +
    (P1Wit.SolWitfill.tuplePayload (fixedTR Bt κ hκ V a b x d bigBias termBias H) t).length ≤ fixedM Bt a b x

/-- T1: every section of the code of `t` holds the fields of `t`. -/
def SecEqEncTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (s : ℕ), s < (fixedDims Bt V a b x d bigBias termBias).nSec →
      SecEq Bt κ hκ V a b x d bigBias termBias H (fixedEnc Bt κ hκ V a b x d bigBias termBias H t) t s

/-- T2: the code of every tuple satisfies the level groups at every level below `top`. -/
def LevelsSoundTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (l : ℕ), l < (fixedDims Bt V a b x d bigBias termBias).top →
      greedyG Bt κ hκ V a b x d bigBias termBias H l (fixedEnc Bt κ hκ V a b x d bigBias termBias H t) ∧
      c10G Bt κ hκ V a b x d bigBias termBias H l (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)

/-- T3: the final level holds only panel sections. -/
def FinalPanelOnlyTarget : Prop :=
  ∀ kk : P1Wit.Mem, panelKind kk = false →
    (fixedDims Bt V a b x d bigBias termBias).count
      (P1Wit.secLev (fixedDims Bt V a b x d bigBias termBias).top kk) = 0

/-- T4: agreement on every section, the payload of `t` at the start of the payload area and zeros after it give
`fixedEnc .. H t = u`. -/
def EncOfAgreeTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  EncFits Bt κ hκ V a b x d bigBias termBias H →
    ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
      (∀ s < (fixedDims Bt V a b x d bigBias termBias).nSec, SecEq Bt κ hκ V a b x d bigBias termBias H u t s) →
      (P1Wit.rdPayload (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u)).take
          (P1Wit.SolWitfill.tuplePayload (fixedTR Bt κ hκ V a b x d bigBias termBias H) t).length =
        P1Wit.SolWitfill.tuplePayload (fixedTR Bt κ hκ V a b x d bigBias termBias H) t →
      (∀ i : Fin (fixedM Bt a b x), (fixedDims Bt V a b x d bigBias termBias).fixedLen +
          (P1Wit.SolWitfill.tuplePayload (fixedTR Bt κ hκ V a b x d bigBias termBias H) t).length ≤ i.val → u i = false) →
      fixedEnc Bt κ hκ V a b x d bigBias termBias H t = u

end

end P11

end P1Int

#print axioms P1Int.P11.form_of_cut
