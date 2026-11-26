import P1P5.KernelWriter
import P1OaiReuse.Plan
import P1P7.SolKernloc
import P1P7.SolRKernel
import P1Wit.Decode

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifSelector
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.PairSimulation.LocalHistory
open OAI.Computability.MultitapeWeakETH
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.IntegerMultiplication.Code
open P1Wit P1P7 P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10

noncomputable section

/-- Compose one exact kernel writer with the Poly evaluator of the written motif entries. -/
theorem evalWrittenEntries {X k J D E R : Type} [Codec X] [Field k] [Fintype J] [Fintype D]
    [Fintype E] [DecidableEq J] [CommRing R] [Fintype R]
    {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
    (B : FixedBlock k a b P (realWidths p) (realWidths q) H H') (hp : ∀ i, 0 < p i)
    (κ : (parameterData B).Entry → R)
    (wr : X → List (List (MotifFields.FixedInput J))) (hwr : Poly wr) :
    ∃ evaluate : X → Label R, Poly evaluate ∧ ∀ x (I : List (List (EntryInput B))),
      wr x = I.map (List.map (MotifFields.fixedInput B)) →
        (evaluate x).val = entriesValue B hp κ I := by
  obtain ⟨val, hv, hspec⟩ := P1OaiReuse.entry_poly B hp κ
  refine ⟨fun x => P1OaiReuse.planVal val (wr x), hwr.compose (P1OaiReuse.planVal_poly hv), ?_⟩
  intro x I he
  change (P1OaiReuse.planVal val (wr x)).val = _
  rw [he, P1OaiReuse.planVal_val, entriesValue, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row _
  simp only [Function.comp_apply, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e _
  exact hspec e

/-- Number of internal words enumerated by the padded shrink writer at one site. -/
def shrinkWordCount {a g : ℕ} {factor : ℝ} {k : Type} [Field k]
    (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass)
      (realWidths supplyMass) (31 / 16) factor)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (x : X.Base) (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) : ℕ :=
  Nat.card (NetworkKernel.Placed (X.packingData.shrinkInternalOwner (layoutBit B X s))
    (internalLabel (selW B X s) (layoutBit B X s)) ((x, j), l))

/-- Numerical payload supplied to the padded shrink writer. -/
abbrev ShrinkPayload :=
  (((ℕ × List (ℕ × Option ShrinkDatumCode)) × Bool) × (ℕ × ℕ)) ×
    (List PosCode × (List (List Bool) × List (List Bool)))

def packShrinkKIn (payload : ShrinkPayload) (pad : Tally) : ShrinkKIn :=
  (payload, pad)

/-- Read the specified radius-three C10 data at a shrinking phase. -/
def readShrinkKIn (pad : Tally) (D : Dims) (u : List Bool) (ℓ a g : ℕ) (site : ℕ × ℕ)
    (ps : List PosCode) (z : List (List Bool) × List (List Bool)) : ShrinkKIn :=
  let count := 2 ^ packingTagBits (2 ^ a)
  let old := decS a g D u ℓ
  let parent := site.1 / count
  let records := ballList (nbOf shrinkNbrs old) (fun y => (old y).map codeShrinkDatum) parent 3
  packShrinkKIn ((((parent, records), layoutOf D u ℓ), (site.1 % count, site.2)), (ps, z)) pad

/-- Read the specified radius-one C10 data at a refresh phase. -/
def readRefreshKIn (D : Dims) (u : List Bool) (ℓ a g dH : ℕ) (site : ℕ × ℕ)
    (ps : List PosCode) (z : List (List Bool) × List (List Bool)) : RefreshKIn :=
  let count := 2 ^ a
  let old := decR a g dH D u ℓ
  let parent := site.1 / count
  let records := ballList (nbOf refreshNbrs old) (fun y => (old y).map codeRefreshDatum) parent 1
  (((parent, records), (site.1 % count, site.2)), (ps, z))

section Shrinking

variable {a b g : ℕ} {δ factor : ℝ} {k : Type} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- The genuine shrink input for the writer, including the padding tally. -/
def paddedShrinkInput (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (x : X.Base) (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) (ps : List PosCode)
    (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) (pad : Tally) : ShrinkKIn :=
  shrinkKIn B ready g X s x j l ps z pad

theorem readShrinkKIn_eq (pad : Tally) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout D u ℓ = if layoutBit B X s then 1 else 0)
    (x : X.Base) (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) (ps : List PosCode)
    (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) :
    readShrinkKIn pad D u ℓ a g (addr X x * 2 ^ packingTagBits (2 ^ a) + bwNum j, bwNum l) ps
      (halfCode (X.shrinkNext B ready s) ((x, j), l) z) = paddedShrinkInput B ready X s x j l ps z pad := by
  have hj : bwNum j < 2 ^ packingTagBits (2 ^ a) := (bitWordFinEquiv _ j).isLt
  simp only [readShrinkKIn, idx_div hj, idx_mod hj,
    decS_eq B D u ℓ X s hN hP hcol hoff hterm, nbOf_shrinkOld, layoutOf_eq D u ℓ hlay]
  rfl

theorem shrinkKernel_poly {R : Type} [CommRing R] [Fintype R]
    (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
    (hwriter : ShrinkKernelProgram B ready) :
    ∃ evaluate : ShrinkKIn → Label R, Poly evaluate ∧
      ∀ (g : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
        (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g)
        (pa : NetworkKernel.Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place
          X.network.Half ((x, j), l))
        (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) (ps : List PosCode) (pad : Tally),
        PlacedList X _ _ pa ps → shrinkWordCount B X s x j l ≤ pad.length →
        (evaluate (paddedShrinkInput B ready X s x j l ps z pad)).val =
          ((X.shrinkStatePass B κ hκ ready).step.term s).kernel ((x, j), l) pa z := by
  obtain ⟨wr, hwr, hspec⟩ := hwriter
  obtain ⟨evaluate, hev, hvalue⟩ := evalWrittenEntries B demandMass_pos κ wr hwr
  refine ⟨evaluate, hev, fun g X s x j l pa z ps pad hps hpad => ?_⟩
  have hentry : ∃ I, wr (paddedShrinkInput B ready X s x j l ps z pad) =
      I.map (List.map (MotifFields.fixedInput B)) ∧
      entriesValue B demandMass_pos κ I =
        ((X.shrinkStatePass B κ hκ ready).step.term s).kernel ((x, j), l) pa z := by
    exact hspec R κ hκ g X s x j l pa z ps pad hps hpad
  obtain ⟨I, hI, he⟩ := hentry
  exact (hvalue _ I hI).trans he

end Shrinking

section Refreshing

variable {a a₀ g dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

theorem readRefreshKIn_eq (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh)
    (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) (ps : List PosCode)
    (z : (dyadicRefreshNext X P hdH hconn F hD hd c).network.Half ((x, j), l)) :
    readRefreshKIn D u ℓ a g dH (addr X x * 2 ^ a + j.val, bwNum l) ps
      (halfCode (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) z) =
      refreshKIn P hdH hconn F hD hd g X c x j l ps z := by
  simp only [readRefreshKIn, refreshKIn, idx_div j.isLt, idx_mod j.isLt,
    decR_eq P hdH hconn F D u ℓ X c hN hP hterm, nbOf_refreshOld]

theorem refreshKernel_poly {R : Type} [CommRing R] [Fintype R]
    (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)
    (hwriter : RefreshKernelProgram P hdH hconn F hD hd) :
    ∃ evaluate : RefreshKIn → Label R, Poly evaluate ∧
      ∀ (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base)
        (j : Fin (2 ^ a)) (l : BitWord g)
        (pa : NetworkKernel.Placed ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place
          X.network.Half ((x, j), l))
        (z : (dyadicRefreshNext X P hdH hconn F hD hd c).network.Half ((x, j), l)) (ps : List PosCode),
        PlacedList X _ _ pa ps →
        (evaluate (refreshKIn P hdH hconn F hD hd g X c x j l ps z)).val =
          ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).kernel ((x, j), l) pa z := by
  obtain ⟨wr, hwr, hspec⟩ := hwriter
  obtain ⟨evaluate, hev, hvalue⟩ := evalWrittenEntries F (fun _ => zero_lt_one) κ wr hwr
  refine ⟨evaluate, hev, fun g X c x j l pa z ps hps => ?_⟩
  obtain ⟨I, hI, he⟩ := hspec R κ hκ g X c x j l pa z ps hps
  exact (hvalue _ I hI).trans he

end Refreshing

end

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.readShrinkKIn_eq
#print axioms P1SolCone.SolCone.readRefreshKIn_eq
#print axioms P1SolCone.SolCone.shrinkKernel_poly
#print axioms P1SolCone.SolCone.refreshKernel_poly
