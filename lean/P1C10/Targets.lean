import P1C10.Rc
import P1ChkFinal.C10RcCodes
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-!
# P1, check C10: the two program targets of the outside prover, as fixed Props (lane P1-lean-c10)

The codes are those of `P1ChkFinal/C10RcCodes.lean` (prover P1-astra-c10, compiled unchanged, job c10-3, sha256
827754eddf712a5ab07a2f29f3a614ee16260b8dc292f05460b2853a6fc7fe06): numbers are binary words (scoped instance
`P1ChkFinal.AstraC10.binaryCodec`), a panel is `codePanel`, a ball is the list `ballList` in BFS order.

* `RefreshCodeOK rcC` / `ShrinkCodeOK rcC`: the recomputation `rcC` on CODES returns the code of OpenAI's child
  panel on the codes of the true data of every state, for every lane dimension `g` (one function for all `g`).
* `RefreshProgram` / `ShrinkProgram`: such an `rcC` exists and is `Poly` (one fixed tape program, polynomial time
  in the size of the input tree). These two Props are the exact statements that the prover's theorems
  `c10_refresh_program` and `c10_shrink_program` must have (targets T1, T2 of
  research/p1/lean/OaiReuse/C10-PROVER-BRIEF.md with the codes written out).
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-- Input of a refresh recomputation on codes: (parent address, ball list of radius 1), child index. -/
abbrev RefreshIn : Type := (ℕ × List (ℕ × Option RefreshDatumCode)) × ℕ

/-- Input of a shrink recomputation on codes: ((parent address, ball list of radius 6), layout bit), child index. -/
abbrev ShrinkIn : Type := ((ℕ × List (ℕ × Option ShrinkDatumCode)) × Bool) × ℕ

section Shrink

variable {a b : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- `rcC` is right on the codes of the true data of every state of a shrinking substep, for every `g`. -/
def ShrinkCodeOK (rcC : ShrinkIn → Option PanelCode) : Prop :=
  ∀ (g : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
    (j : BitWord (packingTagBits (2 ^ a))),
    rcC (((addr X x, ballList (nbrAt X) (fun y => (shrinkOld B X s y).map codeShrinkDatum) (addr X x) 6),
      layoutBit B X s), bwNum j) = some (codePanel (panel (X.shrinkNext B ready s) (x, j)))

/-- **Target T2** (shrink, radius 6): one polynomial-time program for all `g`. -/
def ShrinkProgram : Prop :=
  ∃ rcC : ShrinkIn → Option PanelCode, Poly rcC ∧ ShrinkCodeOK B ready rcC

end Shrink

section Refresh

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- `rcC` is right on the codes of the true data of every state of a refresh substep, for every `g`. -/
def RefreshCodeOK (rcC : RefreshIn → Option PanelCode) : Prop :=
  ∀ (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base) (j : Fin (2 ^ a)),
    rcC ((addr X x, ballList (nbrAt X) (fun y => (refreshOld P hdH hconn F X c y).map codeRefreshDatum)
      (addr X x) 1), j.val) = some (codePanel (panel (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j)))

/-- **Target T1** (refresh, radius 1, no layout bit): one polynomial-time program for all `g`. -/
def RefreshProgram : Prop :=
  ∃ rcC : RefreshIn → Option PanelCode, Poly rcC ∧ RefreshCodeOK P hdH hconn F hD hd rcC

end Refresh

end P1C10
