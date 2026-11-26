import P1Int.FormDefs

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

theorem P1Int.P11.secEq_enc {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.SecEqEncTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit t s hs i hi
  let D := P1Int.P11.fixedDims Bt V a b x d bigBias termBias
  let m := P1Int.P11.fixedM Bt a b x
  let R := P1Int.P11.fixedTR Bt κ hκ V a b x d bigBias termBias H
  let f := P1Wit.ofTuple R t
  let z := P1Wit.SolWitfill.tuplePayload R t
  change (P1Wit.dec D (List.ofFn (P1Wit.encFn D m f z))).val D s i = f.val D s i
  rw [P1Wit.ofFn_encFn D m f z (hfit t), P1Wit.dec_val D _ hi]
  exact P1Wit.decode_enc D m f z (P1Wit.ofTuple_inRange R t) hs hi

theorem P1Int.P11.levels_sound {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.LevelsSoundTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit t l hl
  let D := P1Int.P11.fixedDims Bt V a b x d bigBias termBias
  let u := P1Int.P11.fixedEnc Bt κ hκ V a b x d bigBias termBias H t
  have hsec := P1Int.P11.secEq_enc Bt κ hκ V a b x d bigBias termBias H hfit t
  have htrit : P1Wit.secTrit < D.nSec := by
    change 0 < 7 + 12 * (D.top + 1)
    omega
  have hnext : l + 1 ≤ D.top := Nat.succ_le_of_lt hl
  have hlev : P1Int.P11.LevUpTo Bt κ hκ V a b x d bigBias termBias H u t (l + 1) :=
    fun ℓ hℓ kk => hsec _ (D.secLev_lt_nSec kk ((Nat.le_of_lt hℓ).trans hnext))
  exact ⟨⟨t, hsec _ htrit, hlev⟩,
    ⟨t, hsec _ htrit, hlev, fun kk _ => hsec _ (D.secLev_lt_nSec kk hnext)⟩⟩

namespace P1Int.P11.SolFormLev

open P1Wit P1Wit.SolSpace
open private levelDims layoutRows from P1Wit.SpaceFacts

private theorem lastLayoutCount {k : Type*} [Field k] (S : BlockSchedule k)
    (phases : List Phase) (positions laneCount : ℕ) (fallback : LevelDims) (kk : Mem)
    (hkk : panelKind kk = false) :
    (((layoutRows S positions laneCount phases)[phases.length]?).getD fallback).count kk = 0 := by
  induction phases generalizing positions laneCount with
  | nil =>
    change (levelDims S.expanderExponent (S.degreeExponent 0) laneCount positions none).count kk = 0
    cases kk <;> first | rfl | contradiction
  | cons ph phases ih =>
    simpa only [layoutRows, List.length_cons, List.getElem?_cons_succ] using
      ih (positions / ph.divisor) (laneCount - ph.laneLoss)

end P1Int.P11.SolFormLev

theorem P1Int.P11.finalPanelOnly {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) :
    P1Int.P11.FinalPanelOnlyTarget Bt V a b x d bigBias termBias := by
  intro kk hkk
  let D := P1Int.P11.fixedDims Bt V a b x d bigBias termBias
  change D.count (P1Wit.secLev D.top kk) = 0
  rw [D.count_secLev kk le_rfl]
  exact P1Int.P11.SolFormLev.lastLayoutCount S _ _ _ _ kk hkk

theorem P1Int.P11.encOfAgree {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.EncOfAgreeTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit u t hsec hpay htail
  let D := P1Int.P11.fixedDims Bt V a b x d bigBias termBias
  let m := P1Int.P11.fixedM Bt a b x
  let R := P1Int.P11.fixedTR Bt κ hκ V a b x d bigBias termBias H
  let f := P1Wit.ofTuple R t
  let z := P1Wit.SolWitfill.tuplePayload R t
  let decoded := P1Wit.dec D (List.ofFn u)
  have hagree : decoded.Agree D f := fun s hs => hsec s hs
  have hu : u = P1Wit.encFn D m decoded ((P1Wit.rdPayload D (List.ofFn u)).take z.length) :=
    P1Wit.encFn_dec D z.length u (hfit t) htail
  change P1Wit.encFn D m f z = u
  symm
  calc
    u = P1Wit.encFn D m decoded ((P1Wit.rdPayload D (List.ofFn u)).take z.length) := hu
    _ = P1Wit.encFn D m decoded z := congrArg (P1Wit.encFn D m decoded) hpay
    _ = P1Wit.encFn D m f z :=
      congrArg (fun w : List Bool => fun i : Fin m => w.getD i false)
        (P1Wit.enc_congr D m hagree z)

#print axioms P1Int.P11.secEq_enc
#print axioms P1Int.P11.levels_sound
#print axioms P1Int.P11.finalPanelOnly
#print axioms P1Int.P11.encOfAgree
