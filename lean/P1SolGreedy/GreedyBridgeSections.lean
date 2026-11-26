import P1ChkFinal.GreedyBridge

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1Int P1Int.P11

def SectionAgrees (D : Dims) (u : List Bool) (W : Fields) (s : ℕ) : Prop :=
  ∀ i < D.count s, (dec D u).val D s i = W.val D s i

def ReadsKind (D : Dims) (u : List Bool) (ℓ : ℕ) (r : LevelRecords D (D.lv ℓ)) (k : Mem) : Prop :=
  ∀ i < (D.lv ℓ).count k, readField D u (secLev ℓ k) i = r.code k i

variable {D : Dims} {F : Type*} {C : P1Count.CountData F} {d : ℕ}

theorem section_iff_reads (R : TupleRecords D C d) (u : List Bool) (t : C.Tup d)
    (j : Fin (D.top + 1)) (k : Mem) :
    SectionAgrees D u (ofTuple R t) (secLev j.val k) ↔
      ReadsKind D u j.val (R.level t.1 t.2.1 j) k := by
  have hj : j.val ≤ D.top := Nat.le_of_lt_succ j.isLt
  have hcount := D.count_secLev k hj
  have hval (i : ℕ) (hi : i < (D.lv j.val).count k) :
      (ofTuple R t).val D (secLev j.val k) i = (R.level t.1 t.2.1 j).code k i := by
    simp only [Fields.val, D.kind_secLev k hj, ofTuple_levVal R t _ k i hi, levelAt,
      dite_eq_left j.isLt]
  constructor
  · intro h i hi
    have hi' : i < D.count (secLev j.val k) := hcount.symm ▸ hi
    exact (dec_val D u hi').symm.trans ((h i hi').trans (hval i hi))
  · intro h i hi
    have hi' : i < (D.lv j.val).count k := hcount ▸ hi
    exact (dec_val D u hi).trans ((h i hi').trans (hval i hi').symm)

theorem terms_eq_of_reads {u : List Bool} {ℓ : ℕ} {r s : LevelRecords D (D.lv ℓ)}
    (hr : ReadsKind D u ℓ r .terms) (hs : ReadsKind D u ℓ s .terms) : r.terms = s.terms := by
  funext y
  apply termValue_injective
  intro c
  have hi := idx_lt y.isLt c.isLt
  have h := (hr _ hi).symm.trans (hs _ hi)
  simpa only [LevelRecords.code, idx_div c.isLt, idx_mod c.isLt, atIndex_fin] using h

theorem skeleton_eq_of_trits (R : TupleRecords D C d) {u : List Bool} {t t' : C.Tup d}
    (h : SectionAgrees D u (ofTuple R t) secTrit)
    (h' : SectionAgrees D u (ofTuple R t') secTrit) : t.1 = t'.1 := by
  apply R.skeleton.injective
  funext i k
  apply Fin.ext
  have hi : i.val * D.r + k.val < D.count secTrit := by
    simpa only [Dims.count, D.kind_trit] using idx_lt i.isLt k.isLt
  have he := (h _ hi).symm.trans (h' _ hi)
  simpa only [Fields.val, D.kind_trit, idx_div k.isLt, idx_mod k.isLt, ofTuple, atIndex_fin,
    finValue_fin] using he

/-- The new branch can use a constant payload and one chain entry from the original tuple. -/
theorem tuple_extension_iff (R : TupleRecords D C d) (u : List Bool) (t : C.Tup d)
    (L : ℕ) (hL : L ≤ D.top + 1) (ht : SectionAgrees D u (ofTuple R t) secTrit) :
    (∃ t' : C.Tup d, SectionAgrees D u (ofTuple R t') secTrit ∧
      ∀ j < L, ∀ k : Mem, SectionAgrees D u (ofTuple R t') (secLev j k)) ↔
    ∃ c : C.Ch t.1, ∀ (j : Fin (D.top + 1)), j.val < L →
      ∀ k : Mem, ReadsKind D u j.val (R.level t.1 c j) k := by
  constructor
  · rintro ⟨⟨σ, c, z, q⟩, htrit, hlev⟩
    have he := skeleton_eq_of_trits R htrit ht
    change σ = t.1 at he
    subst σ
    exact ⟨c, fun j hj k =>
      (section_iff_reads R u ⟨t.1, c, z, q⟩ j k).mp (hlev j.val hj k)⟩
  · rintro ⟨c, hc⟩
    let z := (R.payload t.1 c).symm (fun _ _ => false)
    let t' : C.Tup d := ⟨t.1, c, z, fun _ => t.2.2.2 0⟩
    refine ⟨t', ?_, ?_⟩
    · intro i hi
      apply (ht i hi).trans
      simp only [Fields.val, D.kind_trit, ofTuple, t']
    · intro j hj k
      let jf : Fin (D.top + 1) := ⟨j, hj.trans_le hL⟩
      exact (section_iff_reads R u t' jf k).mpr (hc jf hj k)

theorem greedy_iff_branch {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)
    (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d)
    {ℓ : ℕ} (hℓ : ℓ ≤ (fixedDims Bt V a b x d bigBias termBias).top)
    (ht : SecEq Bt κ hκ V a b x d bigBias termBias H u t secTrit) :
    greedyG Bt κ hκ V a b x d bigBias termBias H ℓ u ↔
      ∃ c : (fixedCD Bt κ hκ V a b x).Ch t.1,
        ∀ (j : Fin ((fixedDims Bt V a b x d bigBias termBias).top + 1)), j.val < ℓ + 1 →
          ∀ z : Mem, ReadsKind (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) j.val
            ((fixedTR Bt κ hκ V a b x d bigBias termBias H).level t.1 c j) z :=
  tuple_extension_iff (fixedTR Bt κ hκ V a b x d bigBias termBias H) (List.ofFn u) t
    (ℓ + 1) (Nat.succ_le_succ hℓ) ht

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.terms_eq_of_reads
#print axioms P1SolGreedy.SolBridge.greedy_iff_branch
