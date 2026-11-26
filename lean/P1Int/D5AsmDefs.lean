import P1Int.FormC4Defs
import P1Int.FormCloseDefs
import P1Int.FormSoundDefs
import P1Int.FormFixAsm
import P1Int.ComposeDir
import P1ChkFinal.D5Steps
import P1ProgDir.C4Genuine

/-!
# The assembly of `D5Steps` at the fixed code (P1-lean-integ, statement only)

`D5StepsAsmTarget H`: for the fixed groups `fixedGroups H bs l Wof` and index `fixedIndex cnt`, the structure
`D5Steps (fixedEnc H) (Valid bs l) ck ni X G` holds, given
* the families of the checks as Bool deciders of the lanes' Props (`C1F`, `C2F`, `C3F`, `C4w`, `C14F`, `C11w`, `C12w`,
  `C13linkw`, `C13endsw` at the fixed dims; `ρ = H.tape_order`, tape numbering `τ` equal to it on values),
* the counts and their fit into the `ni` index words,
* the size facts that the lanes' stage lemmas take (`hP`, `hn` for C14, `hN` for C4),
* the fields `out`, `greedy`, `c10` (other lanes: P1-lean-greedy, P1-lean-c10wire; `out` from the `_out` lemmas),
* the bridge `C4BridgeTarget`, the form pieces `FormSoundAsmTarget`, `FormCloseAsmTarget` (Sol, running), the W link
  for `Wof`, `finP = P`, `EncFits H`.
The proved pieces used: `d5_dir_step` (ComposeDir), `P1ChkDir.d5_c14_step`, `P1ChkDir.d5_c4w_step`,
`P1ChkFinal.d5_c11_step`, `d5_c12_step`, `d5_c13_step`, `formFix_asm` with `c14_fix`, `c14_close`, `form_of_cut`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- The genuine dims as a function of the input length (`= fixedDims` at `|x|` by `rfl`). -/
abbrev gdims : ℕ → P1Wit.Dims := fun n =>
  P1Wit.SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1 (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias

/-- The genuine C4 dims (the instantiation of `famC4`). -/
abbrev c4dims : ℕ → P1ChkDir.C4Dims :=
  P1ProgDir.genuineC4Dims Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias

/-- **Target: `D5Steps` at the fixed code from the named inputs.** -/
def D5StepsAsmTarget [NeZero (fixedDims Bt V a b x d bigBias termBias).I]
    [NeZero ((fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).N)]
    [NeZero (P1Wrap.Params.B (lpTime a b x.length))]
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  0 < d →
  ∀ (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
    (ni : ℕ) (cnt : ℕ → ℕ) (ck : ℕ → (Fin (fixedM Bt a b x) → Bool) → ℕ → Bool) (τ : (toOAI V).K → ℕ),
  (∀ kk, (H.tape_order kk : ℕ) = τ kk) →
  -- the families
  (∀ u i, ck 0 u i = true ↔ P1ChkDir.C1F (fixedDims Bt V a b x d bigBias termBias) H.tape_order (List.ofFn u) i) →
  (∀ u i, ck 1 u i = true ↔ P1ChkDir.C2F (fixedDims Bt V a b x d bigBias termBias) H.tape_order (List.ofFn u) i) →
  (∀ u i, ck 2 u i = true ↔ P1ChkDir.C3F (fixedDims Bt V a b x d bigBias termBias) H.tape_order (List.ofFn u) i) →
  (∀ u i, ck 3 u i = true ↔
    P1ChkDir.C4w (four_le_baseDegree S) τ (c4dims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  (∀ u i, ck 14 u i = true ↔ P1ChkDir.C14F (fixedDims Bt V a b x d bigBias termBias) H.tape_order
    (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) (List.ofFn u) i) →
  (∀ u i, ck 10 u i = true ↔ P1ChkFinal.C11w (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  (∀ u i, ck 11 u i = true ↔ P1ChkFinal.C12w (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  (∀ u i, ck 12 u i = true ↔
    P1ChkFinal.C13linkw bs (gdims Bt V a b d bigBias termBias) Wof x (List.ofFn u) i) →
  (∀ u i, ck 13 u i = true ↔
    P1ChkFinal.C13endsw bs l (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  -- the counts and their fit
  cnt 0 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).N *
    (fixedDims Bt V a b x d bigBias termBias).r →
  cnt 1 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).r →
  cnt 2 = (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).r * 3 * 2 →
  cnt 3 = P1ChkDir.cnt4 (toOAI V).K (c4dims Bt V a b d bigBias termBias) x.length →
  cnt 14 = (fixedDims Bt V a b x d bigBias termBias).nGB →
  cnt 10 = P1ChkFinal.cnt11 (gdims Bt V a b d bigBias termBias) x.length →
  cnt 11 = P1ChkFinal.cnt12 (gdims Bt V a b d bigBias termBias) x.length →
  cnt 12 = P1ChkFinal.cnt13link (gdims Bt V a b d bigBias termBias) x.length →
  cnt 13 = P1ChkFinal.cnt13ends (gdims Bt V a b d bigBias termBias) x.length →
  (∀ c, c ≤ 3 ∨ (10 ≤ c ∧ c ≤ 14) → cnt c ≤ ni) →
  -- the size facts of the stage lemmas
  2 ≤ P1Wrap.Params.B (lpTime a b x.length) * (fixedDims Bt V a b x d bigBias termBias).N →
  (fixedDims Bt V a b x d bigBias termBias).nGB = P1ChkDir.nGuessBlocks (a * (x.length ^ 2 + 1))
    (P1Wrap.Params.B (lpTime a b x.length) * (fixedDims Bt V a b x d bigBias termBias).N) →
  (c4dims Bt V a b d bigBias termBias x.length).D.N = 2 ^ (c4dims Bt V a b d bigBias termBias x.length).h →
  -- the fields of the other lanes
  (∀ u, ∀ c < 16, ∀ i < ni, (fixedIndex Bt V a b x d bigBias termBias cnt).stg c i = 0 → ck c u i = true) →
  (∀ lv < (fixedIndex Bt V a b x d bigBias termBias cnt).top, ∀ u,
    (∀ j < 4 + 2 * lv, (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof).P
      (fixedIndex Bt V a b x d bigBias termBias cnt).top j u) →
    ((∀ c, 4 ≤ c → c ≤ 8 → ∀ i < ni, i < (fixedIndex Bt V a b x d bigBias termBias cnt).cnt c →
        (fixedIndex Bt V a b x d bigBias termBias cnt).lev c i = lv → ck c u i = true) ↔
      (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof).greedy lv u)) →
  (∀ lv < (fixedIndex Bt V a b x d bigBias termBias cnt).top, ∀ u,
    (∀ j < 5 + 2 * lv, (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof).P
      (fixedIndex Bt V a b x d bigBias termBias cnt).top j u) →
    ((∀ i < ni, i < (fixedIndex Bt V a b x d bigBias termBias cnt).cnt 9 →
        (fixedIndex Bt V a b x d bigBias termBias cnt).lev 9 i = lv → ck 9 u i = true) ↔
      (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof).c10 lv u)) →
  -- the bridge, the form pieces and the W link
  C4BridgeTarget Bt κ hκ V a b x d bigBias termBias H →
  FormSoundAsmTarget Bt κ hκ V a b x d bigBias termBias H →
  FormCloseAsmTarget Bt κ hκ V a b x d bigBias termBias H →
  EncFits Bt κ hκ V a b x d bigBias termBias H →
  (∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (i : Fin ((fixedCD Bt κ hκ V a b x).P t.1 t.2.1)),
    Wof x (List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)) i =
      (fixedCD Bt κ hκ V a b x).W t.1 t.2.1 t.2.2.1 i) →
  (∀ σ ι, P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias) = (fixedCD Bt κ hκ V a b x).P σ ι) →
  D5Steps (fixedEnc Bt κ hκ V a b x d bigBias termBias H) ((fixedCD Bt κ hκ V a b x).Valid bs l) ck ni
    (fixedIndex Bt V a b x d bigBias termBias cnt) (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof)

end

end P11

end P1Int
