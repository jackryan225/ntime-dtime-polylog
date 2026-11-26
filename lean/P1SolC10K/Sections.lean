import P1C10.Field

namespace P1SolC10K.Sol

open P1Wit P1Wit.SolWitfill

def ReadsSection (D : Dims) (w : List Bool) (ℓ : ℕ) (R : LevelRecords D (D.lv ℓ)) (k : Mem) : Prop :=
  ∀ i < (D.lv ℓ).count k, readField D w (secLev ℓ k) i = R.code k i

theorem tupleSection_iff {F : Type*} {C : P1Count.CountData F} {D : Dims} {d : ℕ}
    (w : List Bool) (R : TupleRecords D C d) (t : C.Tup d) (ℓ : Fin (D.top + 1)) (k : Mem) :
    (∀ i < D.count (secLev ℓ.val k),
      (dec D w).val D (secLev ℓ.val k) i = (ofTuple R t).val D (secLev ℓ.val k) i) ↔
    ReadsSection D w ℓ.val (R.level t.1 t.2.1 ℓ) k := by
  have hl := Nat.le_of_lt_succ ℓ.isLt
  have hc := D.count_secLev k hl
  have he (i : ℕ) (hi : i < (D.lv ℓ.val).count k) :
      (ofTuple R t).val D (secLev ℓ.val k) i = (R.level t.1 t.2.1 ℓ).code k i := by
    simp only [Fields.val, D.kind_secLev k hl, ofTuple_levVal R t ℓ.val k i hi,
      levelAt, dite_eq_left ℓ.isLt]
  constructor
  · intro h i hi
    have hi' : i < D.count (secLev ℓ.val k) := hc.symm ▸ hi
    simpa only [dec_val D w hi', he i hi] using h i hi'
  · intro h i hi
    have hi' : i < (D.lv ℓ.val).count k := hc ▸ hi
    rw [dec_val D w hi, he i hi']
    exact h i hi'

theorem readTerm {D : Dims} {w : List Bool} {ℓ : ℕ} {R : LevelRecords D (D.lv ℓ)}
    (h : ReadsSection D w ℓ R .terms) {y key t : ℕ}
    (ha : y * (D.lv ℓ).termKeys + key < (D.lv ℓ).bases * (D.lv ℓ).termKeys)
    (ht : t < (D.lv ℓ).termArity + 1) :
    rdTerms D w ℓ y key t = termValue (R.terms ⟨y * (D.lv ℓ).termKeys + key, ha⟩) t := by
  let s : Fin ((D.lv ℓ).bases * (D.lv ℓ).termKeys) := ⟨_, ha⟩
  have he := h (s.val * ((D.lv ℓ).termArity + 1) + t) (idx_lt s.isLt ht)
  rw [LevelRecords.code, idx_div ht, idx_mod ht, atIndex_fin] at he
  exact he

end P1SolC10K.Sol
