import P1P7.Defs
import P1P7.ShrinkLocal
import P1P7.ShrinkPanel
import P1P7.RefreshLocal

/-!
# P7: one-substep locality of OpenAI's compression substeps (STATEMENTS; all three PROVED)

Problem P1 (C1, wall card W-ntime-dtime-polylog), Lean plan research/g3/leanplan/PLAN.md, task P7.
Paper: research/papers/ntime-dtime-polylog.tex, Lemma lem:locality (l.874-890).
OpenAI library: research/lean/openai-math/lean (commit 3344da5), folder OAI/Computability/VPVNP.

The definitions (`addr`, `panel`, `nearPanel`, `baseGraph`, `choiceAt`, `shrinkData`, `layoutBit`, ...) and the proved
lemmas on the layout bit and the greedy scans are in `P1P7.Defs` (the former content of this file). The three theorem
statements below are character for character those of the earlier version of this file (where they were `sorry`):
* `shrink_records_local` (paper (a)(i), radius 3): proof `shrink_records_local'` (P1P7/ShrinkLocal.lean);
* `shrink_panel_local` (paper (a)(ii), radius 6): proof `shrink_panel_local'` (P1P7/ShrinkPanel.lean);
* `refresh_panel_local` (paper (b), radius 1): proof `refresh_panel_local'` (P1P7/RefreshLocal.lean).
Checks: P1P7/Check.lean, P1P7/CheckShrink.lean (same statement by `rfl` and syntactic type equality; axioms).
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

section Shrink

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- P7, shrinking substep, paper (a)(i): radius 3. -/
theorem shrink_records_local (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 3 →
      shrinkData B X s y = shrinkData B X' s' y')
    (hlayout : layoutBit B X s = layoutBit B X' s')
    (j : BitWord (packingTagBits (2 ^ a))) :
    nearPanel (X.shrinkNext B ready s) (x, j) = nearPanel (X'.shrinkNext B ready s') (x', j) := by
  exact shrink_records_local' B ready X X' s s' x x' hx hagree hlayout j

/-- P7, shrinking substep, paper (a)(ii): the full panel, radius 6. -/
theorem shrink_panel_local (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 6 →
      shrinkData B X s y = shrinkData B X' s' y')
    (hlayout : layoutBit B X s = layoutBit B X' s')
    (j : BitWord (packingTagBits (2 ^ a))) :
    panel (X.shrinkNext B ready s) (x, j) = panel (X'.shrinkNext B ready s') (x', j) := by
  exact shrink_panel_local' B ready X X' s s' x x' hx hagree hlayout j

end Shrink

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)


/-- P7, refresh substep, paper (b): radius 1 and the block terms at `x` (one per remaining lane). -/
theorem refresh_panel_local (X X' : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) (c' : DyadicRefreshChoice X' P hdH hconn F)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 1 → panel X y = panel X' y')
    (hterm : ∀ l : BitWord g, (c (x, l)).val = (c' (x', l)).val)
    (j : Fin (2 ^ a)) :
    panel (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j) =
      panel (dyadicRefreshNext X' P hdH hconn F hD hd c') (x', j) := by
  exact refresh_panel_local' P hdH hconn F hD hd X X' c c' x x' hx hagree hterm j

end Refresh

end P1P7
