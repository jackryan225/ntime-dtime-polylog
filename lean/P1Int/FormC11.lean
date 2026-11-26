import P1Int.FormC11Defs
import P1Int.FormLev

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

namespace P1Int.P11.SolFormC11

open P1Wit P1Wit.SolWitfill P1ChkFinal

private theorem arcW_eq_readField (D : Dims) (w : List Bool) (y t : ℕ) :
    arcW D w y t = readField D w (secLev D.top .width) (y * finArcs D + t) := by
  unfold arcW rdWidth finArcs
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, div_mul_add_mod]

private theorem widthPrefix_blocks (w : ℕ → ℕ) (A y : ℕ) :
    widthPrefix w (y * A) = pre (fun b => pre (fun t => w (b * A + t)) A) y := by
  induction y with
  | zero => simp only [Nat.zero_mul, widthPrefix, Finset.range_zero, Finset.sum_empty, pre_zero]
  | succ y ih =>
    rw [Nat.succ_mul, pre_succ, ← ih]
    exact Finset.sum_range_add w (y * A) A

private theorem pre_wsOf_eq (D : Dims) (w : List Bool) (y : ℕ) :
    pre (wsOf D w) y =
      widthPrefix (readField D w (secLev D.top .width)) (y * finArcs D) := by
  rw [widthPrefix_blocks]
  unfold pre
  apply Finset.sum_congr rfl
  intro b _
  unfold wsOf pre
  apply Finset.sum_congr rfl
  intro t _
  exact arcW_eq_readField D w b t

private theorem count_secOmega (D : Dims) : D.count D.secOmega = finN D := by
  simp only [Dims.count, D.kind_Omega, finN]

private theorem omega_val_eq_pre {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (w : List Bool)
    (hw : ∀ i < D.count (secLev D.top .width),
      readField D w (secLev D.top .width) i = (ofTuple R t).val D (secLev D.top .width) i)
    (y : ℕ) (hy : y < finN D) :
    (ofTuple R t).val D D.secOmega y = pre (wsOf D w) y := by
  let widths := finValue (R.level t.1 t.2.1 (finalLevel D)).width
  have hΩ : (ofTuple R t).val D D.secOmega y = widthPrefix widths (y * finArcs D) := by
    simp only [Fields.val, D.kind_Omega]
    exact atIndex_fin (fun z : Fin (finN D) => widthPrefix widths (z.val * finArcs D)) ⟨y, hy⟩
  rw [hΩ, pre_wsOf_eq, widthPrefix, widthPrefix]
  apply Finset.sum_congr rfl
  intro i hi
  have hcount : i < (D.lv D.top).count .width := by
    calc
      i < y * finArcs D := Finset.mem_range.mp hi
      _ ≤ finN D * finArcs D := Nat.mul_le_mul_right _ (Nat.le_of_lt hy)
      _ = (D.lv D.top).count .width := by
        simp only [finN, finArcs, LevelDims.count, Nat.mul_assoc]
  have hsec : i < D.count (secLev D.top .width) := by
    rw [D.count_secLev .width le_rfl]
    exact hcount
  rw [hw i hsec]
  simp only [Fields.val, D.kind_secLev .width le_rfl, ofTuple_levVal R t _ _ _ hcount,
    levelAt, dif_pos (Nat.lt_succ_self D.top), LevelRecords.code, widths, finalLevel, Fin.last]

end P1Int.P11.SolFormC11

open P1Int.P11 P1Int.P11.SolFormC11

theorem P1Int.P11.c11_sound {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C11SoundTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit t y hy
  let D := fixedDims Bt V a b x d bigBias termBias
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let w := List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias H t)
  change P1Wit.rdOmega D w y = P1ChkFinal.pre (P1ChkFinal.wsOf D w) y
  have hsec := secEq_enc Bt κ hκ V a b x d bigBias termBias H hfit t
  have hy' : y < D.count D.secOmega := by
    rw [count_secOmega]
    exact hy
  have hΩ : (P1Wit.dec D w).val D D.secOmega y = (P1Wit.ofTuple R t).val D D.secOmega y :=
    hsec _ D.secOmega_lt_nSec y hy'
  have hw : ∀ i < D.count (P1Wit.secLev D.top .width),
      P1Wit.readField D w (P1Wit.secLev D.top .width) i =
        (P1Wit.ofTuple R t).val D (P1Wit.secLev D.top .width) i := by
    intro i hi
    exact (P1Wit.dec_val D w hi).symm.trans (hsec _ (D.secLev_lt_nSec .width le_rfl) i hi)
  calc
    P1Wit.rdOmega D w y = (P1Wit.dec D w).val D D.secOmega y := (P1Wit.dec_val D w hy').symm
    _ = (P1Wit.ofTuple R t).val D D.secOmega y := hΩ
    _ = P1ChkFinal.pre (P1ChkFinal.wsOf D w) y := omega_val_eq_pre R t w hw y hy

theorem P1Int.P11.c11_fix {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C11FixTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro u t hlev hc y hy
  let D := fixedDims Bt V a b x d bigBias termBias
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let w := List.ofFn u
  change y < D.count D.secOmega at hy
  change (P1Wit.dec D w).val D D.secOmega y = (P1Wit.ofTuple R t).val D D.secOmega y
  have hy' : y < P1ChkFinal.finN D := by
    rw [← count_secOmega]
    exact hy
  have hw : ∀ i < D.count (P1Wit.secLev D.top .width),
      P1Wit.readField D w (P1Wit.secLev D.top .width) i =
        (P1Wit.ofTuple R t).val D (P1Wit.secLev D.top .width) i := by
    intro i hi
    exact (P1Wit.dec_val D w hi).symm.trans (hlev D.top (Nat.lt_succ_self _) .width i hi)
  calc
    (P1Wit.dec D w).val D D.secOmega y = P1Wit.rdOmega D w y := P1Wit.dec_val D w hy
    _ = P1ChkFinal.pre (P1ChkFinal.wsOf D w) y := hc y hy'
    _ = (P1Wit.ofTuple R t).val D D.secOmega y := (omega_val_eq_pre R t w hw y hy').symm

#print axioms P1Int.P11.c11_sound
#print axioms P1Int.P11.c11_fix
