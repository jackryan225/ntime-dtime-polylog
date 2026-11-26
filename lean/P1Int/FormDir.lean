import P1Int.FormDirDefs

noncomputable section

namespace P1Int.P11.SolFormDir

open P1Wit P1ChkDir

private theorem tapeIndices {K : Type} {n r i : ℕ} (ρ : K ≃ Fin r) (hi : i < n * r) :
    ∃ (j : Fin n) (k : K), (j : ℕ) = i / r ∧ (ρ k : ℕ) = i % r := by
  have hr : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro h
    simp only [h, Nat.mul_zero, Nat.not_lt_zero] at hi
  let j : Fin n := ⟨i / r, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
  let tape : Fin r := ⟨i % r, Nat.mod_lt _ hr⟩
  exact ⟨j, ρ.symm tape, rfl, congrArg Fin.val (ρ.apply_symm_apply tape)⟩

theorem fixSections {K : Type} (D : Dims) (ρ : K ≃ Fin D.r) (u : List Bool) (W : Fields)
    (σ : Fin (D.I * D.N) → K → Fin 3)
    (hDir : DirTrue (dirP6 D ρ) u)
    (hTrits : ∀ i < D.count secTrit, (dec D u).val D secTrit i = W.val D secTrit i)
    (htrit : ∀ (i : Fin (D.I * D.N)) (k : K), W.trit i (ρ k) = (σ i k : ℕ))
    (hstart : ∀ (ι : Fin D.I) (k : K), W.start ι (ρ k) = zigzag (betaT D.N σ ι k))
    (hnext : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), W.nextOwn ι (ρ k) δ = ownToN (nextT D.N σ ι k δ))
    (hprev : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), W.prevOwn ι (ρ k) δ = ownToN (prevT D.N σ ι k δ)) :
    (∀ i < D.count secStart, (dec D u).val D secStart i = W.val D secStart i) ∧
      (∀ i < D.count secPrev, (dec D u).val D secPrev i = W.val D secPrev i) ∧
      (∀ i < D.count secNext, (dec D u).val D secNext i = W.val D secNext i) := by
  have hσ : (dirP6 D ρ).sigmaS u = σ := by
    funext i k
    have hr := (ρ k).isLt
    have hi : (i : ℕ) * D.r + ρ k < D.count secTrit := by
      simpa only [Dims.count, D.kind_trit] using idx_lt i.isLt hr
    have h := hTrits _ hi
    simp only [Fields.val, D.kind_trit, idx_div hr, idx_mod hr] at h
    change rdTrit D u i (ρ k) = _ at h
    rw [dirP6_sigmaS, h, htrit i k, tritOfN_val, Option.getD_some]
  have hs (ι : Fin D.I) (k : K) : rdStart D u ι (ρ k) = W.start ι (ρ k) := by
    have h := hDir.2.1 ι k
    rw [dirP6_betaS, hσ] at h
    rw [hstart, ← Option.some.inj h, zigzag_unzigzag]
  have hp (ι : Fin D.I) (k : K) (δ : Fin 3) :
      rdPrev D u ι (ρ k) δ = W.prevOwn ι (ρ k) δ := by
    have h := (hDir.2.2 ι k δ).2
    rw [dirP6_prevS, hσ] at h
    rw [hprev, ownOfN_eq h]
  have hn (ι : Fin D.I) (k : K) (δ : Fin 3) :
      rdNext D u ι (ρ k) δ = W.nextOwn ι (ρ k) δ := by
    have h := (hDir.2.2 ι k δ).1
    rw [dirP6_nextS, hσ] at h
    rw [hnext, ownOfN_eq h]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h : i < D.I * D.r := by simpa only [Dims.count, D.kind_start] using hi
    obtain ⟨ι, k, hι, hk⟩ := tapeIndices ρ h
    simpa only [Fields.val, D.kind_start, ← hι, ← hk, dec] using hs ι k
  · intro i hi
    have h : i < 3 * (D.I * D.r) := by
      simpa only [Dims.count, D.kind_prev, Nat.mul_comm 3] using hi
    obtain ⟨ι, k, hι, hk⟩ := tapeIndices ρ (Nat.div_lt_of_lt_mul h)
    let δ : Fin 3 := ⟨i % 3, Nat.mod_lt _ (by decide)⟩
    simpa only [Fields.val, D.kind_prev, ← hι, ← hk, dec] using hp ι k δ
  · intro i hi
    have h : i < 3 * (D.I * D.r) := by
      simpa only [Dims.count, D.kind_next, Nat.mul_comm 3] using hi
    obtain ⟨ι, k, hι, hk⟩ := tapeIndices ρ (Nat.div_lt_of_lt_mul h)
    let δ : Fin 3 := ⟨i % 3, Nat.mod_lt _ (by decide)⟩
    simpa only [Fields.val, D.kind_next, ← hι, ← hk, dec] using hn ι k δ

end P1Int.P11.SolFormDir

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

theorem P1Int.P11.dir_sound {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.DirSoundTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hFits t
  let D := fixedDims Bt V a b x d bigBias termBias
  let m := fixedM Bt a b x
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let W := P1Wit.ofTuple R t
  let z := P1Wit.SolWitfill.tuplePayload R t
  change P1ChkDir.DirTrue (P1ChkDir.dirP6 D H.tape_order) (List.ofFn (P1Wit.encFn D m W z))
  rw [P1Wit.ofFn_encFn D m W z (hFits t)]
  have h := dirLink Bt κ hκ V a x _ _ _ _ H t
  exact (P1ChkDir.dirTrue_enc D m W z (P1Wit.ofTuple_inRange R t) H.tape_order
    (dimSkel Bt κ hκ V _ _ _ _ H t.1) h.1 h.2.1 h.2.2.1 h.2.2.2.1).1

theorem P1Int.P11.dir_fix {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.DirFixTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro u t hDir hTrit
  have h := dirLink Bt κ hκ V a x _ _ _ _ H t
  exact SolFormDir.fixSections (fixedDims Bt V a b x d bigBias termBias) H.tape_order (List.ofFn u)
    (P1Wit.ofTuple (fixedTR Bt κ hκ V a b x d bigBias termBias H) t)
    (dimSkel Bt κ hκ V _ _ _ _ H t.1) hDir hTrit h.1 h.2.1 h.2.2.1 h.2.2.2.1

#print axioms P1Int.P11.dir_sound
#print axioms P1Int.P11.dir_fix
