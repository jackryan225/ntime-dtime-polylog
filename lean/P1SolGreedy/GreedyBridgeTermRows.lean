import P1SolGreedy.GreedyBridgeTerms

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1Int.P11 P1Int.SolTrueRecords P1ChkGreedy

private theorem word_card (n : ℕ) : Fintype.card (BitWord n) = 2 ^ n :=
  (Fintype.card_congr (bitWordFinEquiv n)).trans (Fintype.card_fin _)

theorem shrink_term_reads {D : Dims} (u : List Bool) {ℓ a g : ℕ}
    (X : State a (packingLaneBits a g)) (r : LevelRecords D (D.lv ℓ))
    (terms : OldArc X → Option (Bool × Fin 4 → ℕ))
    (hr : r.terms = numberedTerms D ℓ (shrinkAddress X (D.lv ℓ).termKeys) termIdx terms)
    (hb : (D.lv ℓ).bases = Fintype.card X.Base)
    (hk : (D.lv ℓ).termKeys = 2 ^ packingLaneBits a g * 2 ^ a) (he : (D.lv ℓ).termArity = 8)
    (hv : ∀ e v, terms e = some v → ∀ i, v i < 2 ^ D.wW) :
    ReadsKind D u ℓ r .terms ↔ ∀ e, rawOf D u ℓ X e = termCode (terms e) := by
  apply numbered_reads_iff u r (shrinkAddress X (D.lv ℓ).termKeys) termIdx terms hr
    (shrinkAddress_injective X hk.ge) shrinkEntry_injective
  · intro e
    apply packed_lt
    · rw [hb]
      exact (X.baseIndex ((packingArcEquiv X.Base a g).symm e).1.1).isLt
    · rw [hk]
      exact shrinkKey_lt X e
  · intro i
    rw [he]
    exact shrinkEntry_lt i
  · rw [hb, hk]
    calc
      _ = Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord (packingLaneBits a g)) :=
        Fintype.card_congr (packingArcEquiv X.Base a g).symm
      _ = _ := by simp only [Fintype.card_prod, Fintype.card_fin, word_card]; ac_rfl
  · rw [he, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  · exact hv

theorem refresh_term_reads {D : Dims} (u : List Bool) {ℓ a g dH : ℕ}
    (X : State a (a + g)) (r : LevelRecords D (D.lv ℓ))
    (v : X.Base × BitWord g → Fin (2 ^ a) × Fin dH → ℕ)
    (hr : r.terms = numberedTerms D ℓ (refreshAddress X (D.lv ℓ).termKeys)
      (fun j : Fin (2 ^ a) × Fin dH => j.1.val * dH + j.2.val) (fun s => some (v s)))
    (hb : (D.lv ℓ).bases = Fintype.card X.Base) (hk : (D.lv ℓ).termKeys = 2 ^ g)
    (he : (D.lv ℓ).termArity = 2 ^ a * dH) (hv : ∀ s j, v s j < 2 ^ D.wW) :
    ReadsKind D u ℓ r .terms ↔ P1ChkFinal.C7R.storedTm (dH := dH) D u ℓ X = fun s => some (v s) := by
  let address := refreshAddress X (D.lv ℓ).termKeys
  let entry := fun j : Fin (2 ^ a) × Fin dH => j.1.val * dH + j.2.val
  have ha (s : X.Base × BitWord g) : address s < (D.lv ℓ).bases * (D.lv ℓ).termKeys := by
    apply packed_lt
    · rw [hb]
      exact (X.baseIndex s.1).isLt
    · rw [hk]
      exact (bitWordFinEquiv g s.2).isLt
  have hi (j : Fin (2 ^ a) × Fin dH) : entry j < (D.lv ℓ).termArity := by
    rw [he]
    exact idx_lt j.1.isLt j.2.isLt
  have hcode := numbered_reads_iff u r address entry (fun s => some (v s)) hr
    (refreshAddress_injective X hk.ge) refreshEntry_injective ha hi
    (by rw [hb, hk, Fintype.card_prod, word_card])
    (by rw [he, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])
    (fun s w hw j => (Option.some.inj hw) ▸ hv s j)
  rw [hcode]
  constructor
  · intro h
    funext s
    have hflag : rdTerms D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) 0 = 1 :=
      congrArg Prod.fst (h s)
    have hvec : P1ChkFinal.C7R.storedVec a dH D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) = v s :=
      congrArg Prod.snd (h s)
    simp only [P1ChkFinal.C7R.storedTm, hflag, ite_true, hvec]
  · intro h s
    have hs := congrFun h s
    unfold P1ChkFinal.C7R.storedTm at hs
    split at hs
    · rename_i hflag
      exact Prod.ext hflag (Option.some.inj hs)
    · contradiction

theorem refresh_kinds_iff {D : Dims} {u : List Bool} {ℓ : ℕ} (r : LevelRecords D (D.lv ℓ))
    (hs : (D.lv ℓ).shrink = false)
    (hp : ∀ m, panelKind m = true → ReadsKind D u ℓ r m) :
    (∀ m, ReadsKind D u ℓ r m) ↔ ReadsKind D u ℓ r .terms := by
  constructor
  · exact fun h => h .terms
  · intro ht m
    cases m <;> first
      | exact hp _ rfl
      | exact ht
      | (intro i hi; simp only [LevelDims.count, hs, Bool.false_eq_true, ite_false, Nat.not_lt_zero] at hi)

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.shrink_term_reads
#print axioms P1SolGreedy.SolBridge.refresh_term_reads
