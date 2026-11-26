import P1ChkFinal.C10RcRefreshProof
import P1C10.Code

/-!
# P1, check C10, REFRESH substep: closed (lane P1-lean-c10)

The refresh program of the prover P1-astra-c10 (`P1ChkFinal.c10_refresh_program`, files
`P1ChkFinal/C10Rc{Codes,Poly,Refresh,RefreshRead,RefreshProof}.lean` compiled UNCHANGED) has exactly the type of
the target `P1C10.RefreshProgram` (statement check `refreshProgram_proved`). With it the refresh stage lemma on codes
holds for one explicit polynomial-time recomputation, with no hypothesis on the recomputation left.
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

section Refresh

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- Statement check: the prover's theorem has exactly the type of the target T1. -/
theorem refreshProgram_proved : RefreshProgram P hdH hconn F hD hd :=
  P1ChkFinal.c10_refresh_program P hdH hconn F hD hd

/-- **C10 at a refresh substep, closed**: one polynomial-time recomputation on codes for which C10 on codes passes at
every level-`ℓ+1` address iff the stored level-`ℓ+1` panels are the true ones (for every lane dimension `g`). -/
theorem refresh_code_stage_closed :
    ∃ rcR : RefreshIn → Option PanelCode, Poly rcR ∧ RefreshCodeOK P hdH hconn F hD hd rcR ∧
      ∀ (g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
        (c : DyadicRefreshChoice X P hdH hconn F),
        (D.lv ℓ).bases = Fintype.card X.Base →
        (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) →
        (∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
          rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) →
        ((∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base, C10rCode rcR a a₀ g dH D u ℓ Y) ↔
          ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
            (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y)) := by
  obtain ⟨rcR, hp, hok⟩ := refreshProgram_proved P hdH hconn F hD hd
  exact ⟨rcR, hp, hok, fun g D u ℓ X c hN hP hterm =>
    C10rCode_stage P hdH hconn F hD hd hok g D u ℓ X c hN hP hterm⟩

end Refresh

end P1C10
