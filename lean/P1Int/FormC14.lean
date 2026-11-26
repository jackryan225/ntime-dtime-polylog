import P1Int.FormC14Defs
import P1Int.RecordsFitProof
import P1Net.Owners

noncomputable section

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkDir P1Net

namespace P1Int.P11.SolFormC14

open OAI.DepthThreeLowerBound

private theorem tritAgreement {K : Type} (D : Dims) (ρ : K ≃ Fin D.r)
    (u : List Bool) (W : Fields) :
    (∀ i < D.count secTrit, (P1Wit.dec D u).val D secTrit i = W.val D secTrit i) ↔
      ∀ (i : Fin (D.I * D.N)) (k : K), rdTrit D u i (ρ k) = W.trit i (ρ k) := by
  constructor
  · intro h i k
    have hr := (ρ k).isLt
    have hi : (i : ℕ) * D.r + ρ k < D.count secTrit := by
      simpa only [Dims.count, D.kind_trit] using idx_lt i.isLt hr
    simpa only [Fields.val, D.kind_trit, idx_div hr, idx_mod hr, P1Wit.dec] using h _ hi
  · intro h i hi
    have hi' : i < D.I * D.N * D.r := by
      simpa only [Dims.count, D.kind_trit] using hi
    have hr : 0 < D.r := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp only [hz, Nat.mul_zero, Nat.not_lt_zero] at hi'
    let j : Fin (D.I * D.N) := ⟨i / D.r, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
    let tape : Fin D.r := ⟨i % D.r, Nat.mod_lt _ hr⟩
    simpa only [Fields.val, D.kind_trit, P1Wit.dec, Equiv.apply_symm_apply, j, tape] using
      h j (ρ.symm tape)

private theorem readValidTrit {K : Type} (D : Dims) (ρ : K ≃ Fin D.r) (u : List Bool)
    (hDir : DirTrue (dirP6 D ρ) u) (i : Fin (D.I * D.N)) (k : K) :
    ((dirP6 D ρ).sigmaS u i k : ℕ) = rdTrit D u i (ρ k) := by
  have h := (dirP6_C1_iff D ρ u i k).mp (hDir.1 i k)
  simp only [dirP6_sigmaS, tritOfN, dite_eq_left h, Option.getD_some]

private theorem skeletonOfAgreement {K : Type} (D : Dims) (ρ : K ≃ Fin D.r) (u : List Bool)
    (W : Fields) (σ : Fin (D.I * D.N) → K → Fin 3)
    (hAgree : ∀ i < D.count secTrit, (P1Wit.dec D u).val D secTrit i = W.val D secTrit i)
    (hTrit : ∀ (i : Fin (D.I * D.N)) (k : K), W.trit i (ρ k) = (σ i k : ℕ)) :
    (dirP6 D ρ).sigmaS u = σ := by
  funext i k
  rw [dirP6_sigmaS, (tritAgreement D ρ u W).mp hAgree i k, hTrit i k,
    tritOfN_val, Option.getD_some]

/-- Simultaneous renumbering of the intervals and their lengths preserves the count. -/
private theorem unownedCount_cast {M : FiniteMultiTapeMachine} {B g I N I' N' : ℕ}
    [NeZero B] (L : GuessLayout M g) (hI : I = I') (hN : N = N')
    (σ : Fin (I' * N') → M.K → Fin 3) :
    unownedCount (B := B) L (fun i k => σ (finCongr (congrArg₂ Nat.mul hI hN) i) k) N I =
      unownedCount (B := B) L σ N' I' := by
  cases hI
  cases hN
  rfl

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)

omit [Algebra (ZMod 2) F] in
private theorem fixedUnowned (σ : (fixedCD Bt κ hκ V a b x).Sk) :
    (fixedCD Bt κ hκ V a b x).unowned σ =
      unownedCount (B := P1Wrap.Params.B (lpTime a b x.length)) (netLayout V a x)
        (dimSkel Bt κ hκ V _ _ _ _ H σ)
        (fixedDims Bt V a b x d bigBias termBias).N
        (fixedDims Bt V a b x d bigBias termBias).I := by
  let B := P1Wrap.Params.B (lpTime a b x.length)
  let I := P1Wrap.Params.I 1 (lpTime a b x.length)
  let N := 2 ^ P1Wrap.Params.h (lpTime a b x.length)
  let D := fixedDims Bt V a b x d bigBias termBias
  calc
    (fixedCD Bt κ hκ V a b x).unowned σ =
        unownedCount (B := B) (netLayout V a x) σ N I :=
      uOwned_eq_unownedCount (toOAI V) B (netLayout V a x) I σ
    _ = unownedCount (B := B) (netLayout V a x) (dimSkel Bt κ hκ V _ _ _ _ H σ) D.N D.I :=
      (unownedCount_cast (B := B) (netLayout V a x) H.interval_count H.initial_lanes σ).symm

private theorem storedSkeleton (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d)
    (hTrit : SecEq Bt κ hκ V a b x d bigBias termBias H u t secTrit) :
    (dirP6 (fixedDims Bt V a b x d bigBias termBias) H.tape_order).sigmaS (List.ofFn u) =
      dimSkel Bt κ hκ V _ _ _ _ H t.1 :=
  skeletonOfAgreement _ H.tape_order (List.ofFn u) _ _ hTrit (dirLink Bt κ hκ V a x _ _ _ _ H t).1

open private live_choices live_execute from P1Int.RecordsFitProof

omit [Algebra (ZMod 2) F] in
private theorem fixedChoices (σ : (fixedCD Bt κ hκ V a b x).Sk) :
    Nonempty ((fixedCD Bt κ hκ V a b x).Ch σ) := by
  change Nonempty (fixedExec Bt κ hκ V a b x σ).Choices
  exact live_choices _ (live_execute Bt κ hκ _ _ _)

end P1Int.P11.SolFormC14

open P1Int.P11 P1Int.P11.SolFormC14

theorem P1Int.P11.dir_exists {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.DirExistsTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hd u hDir
  let D := fixedDims Bt V a b x d bigBias termBias
  let U := List.ofFn u
  let e := finCongr (congrArg₂ Nat.mul H.interval_count H.initial_lanes)
  let σ : (fixedCD Bt κ hκ V a b x).Sk :=
    fun i k => (dirP6 D H.tape_order).sigmaS U (e.symm i) k
  exact (fixedChoices Bt κ hκ V a b x σ).elim fun ι => by
    let t : (fixedCD Bt κ hκ V a b x).Tup d := ⟨σ, ι, (fun _ _ => false), (fun _ => ⟨0, hd⟩)⟩
    refine ⟨t, (tritAgreement D H.tape_order U _).mpr ?_⟩
    intro i k
    rw [(dirLink Bt κ hκ V a x _ _ _ _ H t).1 i k]
    change rdTrit D U i (H.tape_order k) = ((dirP6 D H.tape_order).sigmaS U (e.symm (e i)) k : ℕ)
    rw [e.symm_apply_apply]
    exact (readValidTrit D H.tape_order U hDir i k).symm

theorem P1Int.P11.c14_sound {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C14SoundTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hFits t hOwned
  let D := fixedDims Bt V a b x d bigBias termBias
  let m := fixedM Bt a b x
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let W := P1Wit.ofTuple R t
  let z := P1Wit.SolWitfill.tuplePayload R t
  let σ := dimSkel Bt κ hκ V _ _ _ _ H t.1
  let G := guessP6 D (toOAI V).inputTape fun q => ((q : ℕ) : ℤ)
  let B := P1Wrap.Params.B (lpTime a b x.length)
  have h := dirLink Bt κ hκ V a x _ _ _ _ H t
  have hRange : W.InRange D := P1Wit.ofTuple_inRange R t
  have hσ := (dirTrue_enc D m W z hRange H.tape_order σ h.1 h.2.1 h.2.2.1 h.2.2.2.1).2
  change
    (∀ q, gOwnS (dirP6 D H.tape_order) G (List.ofFn (P1Wit.encFn D m W z)) q =
        some (gOwnT G D.N ((dirP6 D H.tape_order).sigmaS (List.ofFn (P1Wit.encFn D m W z))) q)) ∧
      unownedCount (B := B) (netLayout V a x)
        ((dirP6 D H.tape_order).sigmaS (List.ofFn (P1Wit.encFn D m W z))) D.N D.I = 0
  rw [P1Wit.ofFn_encFn D m W z (hFits t), hσ]
  refine ⟨fun q => ?_, (fixedUnowned Bt κ hκ V a b x d bigBias termBias H t.1).symm.trans hOwned⟩
  rw [guessP6_gOwnS, rdGuess_enc D m W z hRange q.isLt, h.2.2.2.2 q, ownOfN_toN]

theorem P1Int.P11.c14_fix {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C14FixTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro u t _ hC14 hTrit i hi
  let D := fixedDims Bt V a b x d bigBias termBias
  have hσ := storedSkeleton Bt κ hκ V a b x d bigBias termBias H u t hTrit
  change i < D.count secGuess at hi
  let q : Fin D.nGB := ⟨i, by simpa only [Dims.count, D.kind_guess] using hi⟩
  have hOwner := hC14.1 q
  rw [hσ, guessP6_gOwnS] at hOwner
  have hGuess := (dirLink Bt κ hκ V a x _ _ _ _ H t).2.2.2.2 q
  change (P1Wit.dec D (List.ofFn u)).val D secGuess i =
    (P1Wit.ofTuple (fixedTR Bt κ hκ V a b x d bigBias termBias H) t).val D secGuess i
  simp only [Fields.val, D.kind_guess, P1Wit.dec]
  exact (ownOfN_eq hOwner).symm.trans hGuess.symm

theorem P1Int.P11.c14_close {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C14CloseTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro u t _ hC14 hTrit
  have hσ := storedSkeleton Bt κ hκ V a b x d bigBias termBias H u t hTrit
  have hOwned := hC14.2
  rw [hσ] at hOwned
  exact (fixedUnowned Bt κ hκ V a b x d bigBias termBias H t.1).trans hOwned

#print axioms P1Int.P11.dir_exists
#print axioms P1Int.P11.c14_sound
#print axioms P1Int.P11.c14_fix
#print axioms P1Int.P11.c14_close
