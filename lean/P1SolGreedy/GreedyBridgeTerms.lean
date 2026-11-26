import P1SolGreedy.GreedyBridgeSections

namespace P1SolGreedy.SolBridge

open P1Wit P1Wit.SolWitfill P1ChkGreedy P1Int.SolTrueRecords

def termCell (D : Dims) (u : List Bool) (ℓ slot field : ℕ) : ℕ :=
  readField D u (secLev ℓ .terms) (slot * ((D.lv ℓ).termArity + 1) + field)

def termFields {I : Type} (f : ℕ → ℕ) (entry : I → ℕ) : ℕ × (I → ℕ) :=
  (f 0, fun i => f (1 + entry i))

private theorem terms_by_cell {D : Dims} (u : List Bool) {ℓ : ℕ} (r : LevelRecords D (D.lv ℓ)) :
    ReadsKind D u ℓ r .terms ↔
      ∀ (q : Fin ((D.lv ℓ).bases * (D.lv ℓ).termKeys)) (c : Fin ((D.lv ℓ).termArity + 1)),
        termCell D u ℓ q.val c.val = termValue (r.terms q) c.val := by
  constructor
  · intro h q c
    simpa only [termCell, LevelRecords.code, idx_div c.isLt, idx_mod c.isLt, atIndex_fin] using
      h _ (idx_lt q.isLt c.isLt)
  · intro h j hj
    let keyCount := (D.lv ℓ).bases * (D.lv ℓ).termKeys
    let fieldCount := (D.lv ℓ).termArity + 1
    obtain ⟨⟨q, c⟩, hq⟩ := (ord keyCount fieldCount).surjective ⟨j, hj⟩
    have hj' : q.val * fieldCount + c.val = j := congrArg Fin.val hq
    rw [← hj']
    simpa only [termCell, fieldCount, LevelRecords.code, idx_div c.isLt, idx_mod c.isLt, atIndex_fin]
      using h q c

private theorem index_onto {A : Type} [Fintype A] {n : ℕ} (v : A → ℕ)
    (hi : Function.Injective v) (hb : ∀ a, v a < n) (hc : Fintype.card A = n) :
    Function.Surjective (fun a : A => (⟨v a, hb a⟩ : Fin n)) := by
  refine ((Fintype.bijective_iff_injective_and_card _).mpr ?_).2
  exact ⟨fun _ _ h => hi (congrArg Fin.val h), hc.trans (Fintype.card_fin n).symm⟩

private theorem termFields_eq_iff {I : Type} {n : ℕ} {entry : I → ℕ}
    (hb : ∀ i, entry i < n)
    (hs : Function.Surjective (fun i : I => (⟨entry i, hb i⟩ : Fin n))) (f g : ℕ → ℕ) :
    termFields f entry = termFields g entry ↔ ∀ c : Fin (n + 1), f c.val = g c.val := by
  constructor
  · intro h c
    refine Fin.cases ?_ (fun j => ?_) c
    · exact congrArg Prod.fst h
    · obtain ⟨i, hi⟩ := hs j
      have he : entry i = j.val := congrArg Fin.val hi
      have hh : f (1 + entry i) = g (1 + entry i) := congrFun (congrArg Prod.snd h) i
      simpa only [he, Nat.add_comm 1, Fin.val_succ] using hh
  · intro h
    apply Prod.ext
    · exact h 0
    · funext i
      exact h ⟨1 + entry i, by have := hb i; omega⟩

private theorem termFields_numbered {D : Dims} {ℓ : ℕ} {A I : Type}
    (address : A → ℕ) (entry : I → ℕ)
    (ha : Function.Injective address) (he : Function.Injective entry)
    (hib : ∀ i, entry i < (D.lv ℓ).termArity)
    (terms : A → Option (I → ℕ)) (a : A)
    (hab : address a < (D.lv ℓ).bases * (D.lv ℓ).termKeys)
    (hf : ∀ v, terms a = some v → ∀ i, v i < 2 ^ D.wW) :
    termFields (termValue (numberedTerms D ℓ address entry terms ⟨address a, hab⟩)) entry =
      termCode (terms a) := by
  unfold numberedTerms
  rw [readNumbered_at ha]
  cases h : terms a with
  | none =>
    apply Prod.ext
    · rfl
    · funext i
      change termValue (none : TermSlot D (D.lv ℓ)) (1 + entry i) = 0
      rw [Nat.add_comm 1]
      exact atIndex_fin (fun _ => 0) (⟨entry i, hib i⟩ : Fin (D.lv ℓ).termArity)
  | some v =>
    apply Prod.ext
    · rfl
    · funext i
      change termValue (some (fun j : Fin (D.lv ℓ).termArity =>
        fieldValue D.wW (readNumbered entry v 0 j.val)) : TermSlot D (D.lv ℓ)) (1 + entry i) = v i
      rw [Nat.add_comm 1, termValue]
      calc
        _ = (fieldValue D.wW (readNumbered entry v 0 (entry i))).val :=
          atIndex_fin _ (⟨entry i, hib i⟩ : Fin (D.lv ℓ).termArity)
        _ = v i := by rw [readNumbered_at he, fieldValue_val (hf v h i)]

/-- With full address and entry ranges, the raw flags and coordinates characterize the whole term section. -/
theorem numbered_reads_iff {D : Dims} (u : List Bool) {ℓ : ℕ} (r : LevelRecords D (D.lv ℓ))
    {A I : Type} [Fintype A] [Fintype I] (address : A → ℕ) (entry : I → ℕ)
    (terms : A → Option (I → ℕ)) (hr : r.terms = numberedTerms D ℓ address entry terms)
    (ha : Function.Injective address) (he : Function.Injective entry)
    (hab : ∀ a, address a < (D.lv ℓ).bases * (D.lv ℓ).termKeys)
    (hib : ∀ i, entry i < (D.lv ℓ).termArity)
    (hA : Fintype.card A = (D.lv ℓ).bases * (D.lv ℓ).termKeys)
    (hI : Fintype.card I = (D.lv ℓ).termArity)
    (hf : ∀ a v, terms a = some v → ∀ i, v i < 2 ^ D.wW) :
    ReadsKind D u ℓ r .terms ↔ ∀ a, termFields (termCell D u ℓ (address a)) entry = termCode (terms a) := by
  let number (a : A) : Fin ((D.lv ℓ).bases * (D.lv ℓ).termKeys) := ⟨address a, hab a⟩
  have hsa : Function.Surjective number := index_onto address ha hab hA
  have hsi := index_onto entry he hib hI
  have code (a : A) : termFields (termValue (r.terms (number a))) entry = termCode (terms a) := by
    rw [hr]
    exact termFields_numbered address entry ha he hib terms a (hab a) (hf a)
  rw [terms_by_cell]
  constructor
  · intro h a
    exact ((termFields_eq_iff hib hsi _ _).mpr (h (number a))).trans (code a)
  · intro h q
    obtain ⟨a, rfl⟩ := hsa q
    exact (termFields_eq_iff hib hsi _ _).mp ((h a).trans (code a).symm)

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.numbered_reads_iff
