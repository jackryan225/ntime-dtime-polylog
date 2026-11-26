import P1ChkFinal.C10Bits
import P1ChkGreedy.Bind

/-!
# P1, wave 2: C10's term decoders agree with the codes of the greedy lane (lane P1-lean-W2-chkfinal)

`P1ChkGreedy.level_u_iff` (shrink) and `P1ChkGreedy.refresh_u_iff` (refresh) end with the stored term slots equal to
`termCode` of the true terms of a selection `s` (resp. a refresh choice `c`). These two lemmas turn that conclusion
into the hypothesis `hterm` of `C10sU_stage` / `C10rU_stage`. Imports `P1ChkGreedy.Bind` read-only.
-/

namespace P1ChkFinal

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open P1P7 P1Wit

section Shrink

variable {a g : ℕ} {factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- The greedy lane's stored term codes give C10's decoded term data = `P1P7.choiceAt`. -/
theorem termsDec_of_greedy (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B)
    (h : ∀ e, P1ChkGreedy.rawOf D u ℓ X e = P1ChkGreedy.termCode (P1ChkGreedy.trueTerms B X s e)) (y : X.Base) :
    termsDec D u ℓ (addr X y) = choiceAt B X s y := by
  funext i t l w hh
  have he := h (((y, (t, l)), i), (w, hh))
  have h1 : (P1ChkGreedy.rawOf D u ℓ X (((y, (t, l)), i), (w, hh))).1 =
      rdTerms D u ℓ (addr X y) (bwNum ((packingFields a g).symm (w, hh, (t, l))) * 2 ^ a + i) 0 := rfl
  have h2 : ∀ p, (P1ChkGreedy.rawOf D u ℓ X (((y, (t, l)), i), (w, hh))).2 p =
      rdTerms D u ℓ (addr X y) (bwNum ((packingFields a g).symm (w, hh, (t, l))) * 2 ^ a + i) (1 + tIdx p) :=
    fun _ => rfl
  rw [he] at h1 h2
  rw [P1ChkGreedy.choiceAt_eq_trueTerms]
  unfold termsDec
  cases htt : P1ChkGreedy.trueTerms B X s (((y, (t, l)), i), (w, hh)) with
  | none =>
    rw [htt] at h1
    simp only [P1ChkGreedy.termCode] at h1
    rw [← h1]
    simp
  | some v =>
    rw [htt] at h1 h2
    simp only [P1ChkGreedy.termCode] at h1 h2
    rw [← h1, if_pos rfl]
    congr 1
    funext p
    exact (h2 p).symm

end Shrink

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

/-- The greedy lane's stored block-term codes give the hypothesis `hterm` of `C10rU_stage`. -/
theorem rterm_of_greedy (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F)
    (h : ∀ s, P1ChkGreedy.rawR (dH := dH) D u ℓ X s =
      P1ChkGreedy.termCode (P1ChkGreedy.trueBlockTerms P hdH hconn F X c s))
    (y : X.Base) (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH) :
    rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh := by
  have he := congrArg (fun r => r.2 jh) (h (y, l))
  exact he

end Refresh

end P1ChkFinal
