import P1P7.KernelPos
import P1P7.KernelForm
import P1ChkFinal.C10RcCodes
import OAI.Computability.MultitapeWeakETH.MotifFixed

/-!
# P1, kernel entries from LOCAL STORED DATA: the plan writers (STATEMENTS; lane P1-lean-eval)

The cone program (`WHyp` of C13link, Sol P1-sol-cone) needs every kernel entry `t.kernel w x z` of a level as a
value it can COMPUTE from the witness. The Poly evaluation of a plan is proved (`P1P5.plan_poly`,
`P1ProgEng.kernel_entry_poly_cost`); kernel locality is proved (`P1P7.shrink_kernel_local`, radius 3;
`P1P7.refresh_kernel_local`, radius 1). What is missing is a program that WRITES the plan from local data.

Input: the data that check C10 reads (codes of P1-astra-c10, `P1ChkFinal.C10RcCodes`, numbers in binary): the address of
the base, the ball list of the true level data around it (radius 3 = the radius of `shrink_kernel_local`, with
`shrinkOld` = `P1P7.shrinkData` by address; radius 1 for a refresh with `refreshOld`), the layout bit (shrink), the
child index `j` and the lane `l` of the new site, then the CODES of the kernel arguments:
* `halfCode Y v z`: the words of the out-slots and of the in-slots of the half-assignment `z` at `v`, slot order;
* a placed half-assignment as a list `ps` of (address, lane number, half code) of its old positions, each position
  exactly once, in ANY order (`PlacedList`).
Output: a list of lists of OpenAI's encoded entry inputs (`MotifFields.fixedInput`), read as a sum of products of
motif map entries; its value is the kernel entry. With `P1OaiReuse.planVal_poly` / `entry_poly` the value is then
`Poly` too.

* `ShrinkKernelProgram B ready`, `RefreshKernelProgram P hdH hconn F hD hd`: one `Poly` writer for every lane
  dimension `g` and every parameter solution `κ`.
* 13:00Z REVISION (shrink only; refresh part unchanged, proved by Sol kwr): the shrink kernel entry is a SUM over the internal
  words owned by the site (`P1P7.shrink_kernel_resident'`), whose number can be exponential in the input size (P1-sol-kws,
  board 2089: zero-one integer solutions force that many output terms). So the shrink writer also reads a PAD tally and must
  be right when the pad is at least the number of internal words (`Nat.card` of the `Placed` type summed over in
  `shrink_kernel_resident'`). The cone supplies a pad of length `2^(c C Mbar)` (P5 plan-size bounds). Old text:
  research/p1/lean/P5/archive/KernelWriter-before-1300Z.lean.txt.
-/

namespace P1P5.KW

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifSelector
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.PairSimulation.LocalHistory
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH
open P1P7 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

noncomputable section

/-- Code of a half-assignment: (out-slot words, in-slot words), each in slot order. -/
def halfCode {a G : ℕ} (Y : State a G) (v : Y.network.Site) (z : Y.network.Half v) :
    List (List Bool) × List (List Bool) :=
  (List.ofFn fun k => List.ofFn (z.1 (outEdge Y v k) (outEdge_src Y v k)),
    List.ofFn fun k => List.ofFn (z.2 (inEdge Y v k) (inEdge_dst Y v k)))

/-- Code of one old position of a placed half-assignment: ((address, lane number), half code). -/
abbrev PosCode : Type := (ℕ × ℕ) × (List (List Bool) × List (List Bool))

/-- `ps` lists every old position placed at `w` exactly once (any order) with the code of its half-assignment. -/
def PlacedList {a G : ℕ} (X : State a G) {N' : Network} (place : X.network.Site → N'.Site) (w : N'.Site)
    (pa : Placed place X.network.Half w) (ps : List PosCode) : Prop :=
  ∃ us : List {u : X.network.Site // w = place u}, us.Nodup ∧ (∀ u, u ∈ us) ∧
    ps = us.map fun u => ((addr X u.1.1, bwNum u.1.2), halfCode X u.1 (pa u.1 u.2))

/-- The value of a list of lists of entry inputs of a fixed block: the sum of the products of the entries. -/
def entriesValue {k J D E : Type} [Field k] [Fintype J] [Fintype D] [Fintype E] [DecidableEq J]
    {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
    (B : FixedBlock k a b P (realWidths p) (realWidths q) H H') (hp : ∀ i, 0 < p i)
    {R : Type} [CommRing R] (κ : (parameterData B).Entry → R) (I : List (List (EntryInput B))) : R :=
  (I.map fun tm => (tm.map fun e => evalEntry κ (entry B hp e.demand e.payload e.party e.demandBits e.supplyBits)).prod).sum

section Shrink

variable {a b : ℕ} {δ factor : ℝ} {k : Type} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- Input of the shrink plan writer; the last component is a PAD (a tally at least as long as the number of internal
words owned by the site: the plan is a sum over these words, so its length is not polynomial in the rest of the input;
counterexample of P1-sol-kws, board 2089). -/
abbrev ShrinkKIn : Type :=
  ((((ℕ × List (ℕ × Option ShrinkDatumCode)) × Bool) × (ℕ × ℕ)) ×
    (List PosCode × (List (List Bool) × List (List Bool)))) × Tally

/-- The input of the writer for the kernel entry at `((x, j), l)`, arguments `ps` (placed) and `z`. -/
def shrinkKIn (g : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
    (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) (ps : List PosCode)
    (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) (pad : Tally) : ShrinkKIn :=
  (((((addr X x, ballList (nbrAt X) (fun y => (shrinkOld B X s y).map codeShrinkDatum) (addr X x) 3),
    layoutBit B X s), (bwNum j, bwNum l)), (ps, halfCode (X.shrinkNext B ready s) ((x, j), l) z)), pad)

/-- `wr` writes, for every state, selection, site and argument, entry inputs whose value is the kernel entry. -/
def ShrinkKernelOK (wr : ShrinkKIn → List (List (MotifFields.FixedInput (Fin 6)))) : Prop :=
  ∀ (R : Type) [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
    (g : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
    (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g)
    (pa : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half ((x, j), l))
    (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) (ps : List PosCode) (pad : Tally),
    PlacedList X _ _ pa ps →
    Nat.card (Placed (X.packingData.shrinkInternalOwner (layoutBit B X s))
      (internalLabel (selW B X s) (layoutBit B X s)) ((x, j), l)) ≤ pad.length →
    ∃ I : List (List (EntryInput B)),
      wr (shrinkKIn B ready g X s x j l ps z pad) = I.map (List.map (MotifFields.fixedInput B)) ∧
      entriesValue B demandMass_pos κ I = ((X.shrinkStatePass B κ hκ ready).step.term s).kernel ((x, j), l) pa z

/-- **Shrink plan writer** (radius 3): one polynomial-time program for all `g` and `κ`. -/
def ShrinkKernelProgram : Prop :=
  ∃ wr : ShrinkKIn → List (List (MotifFields.FixedInput (Fin 6))), Poly wr ∧ ShrinkKernelOK B ready wr

end Shrink

section Refresh

variable {a a₀ dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- Input of the refresh plan writer (no layout bit). -/
abbrev RefreshKIn : Type :=
  ((ℕ × List (ℕ × Option RefreshDatumCode)) × (ℕ × ℕ)) ×
    (List PosCode × (List (List Bool) × List (List Bool)))

/-- The input of the writer for the kernel entry at `((x, j), l)`. -/
def refreshKIn (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base)
    (j : Fin (2 ^ a)) (l : BitWord g) (ps : List PosCode)
    (z : (dyadicRefreshNext X P hdH hconn F hD hd c).network.Half ((x, j), l)) : RefreshKIn :=
  (((addr X x, ballList (nbrAt X) (fun y => (refreshOld P hdH hconn F X c y).map codeRefreshDatum) (addr X x) 1),
    (j.val, bwNum l)), (ps, halfCode (dyadicRefreshNext X P hdH hconn F hD hd c) ((x, j), l) z))

/-- `wr` writes entry inputs whose value is the refresh kernel entry. -/
def RefreshKernelOK (wr : RefreshKIn → List (List (MotifFields.FixedInput (Fin (2 ^ a))))) : Prop :=
  ∀ (R : Type) [CommRing R] (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)
    (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base)
    (j : Fin (2 ^ a)) (l : BitWord g)
    (pa : Placed ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place X.network.Half ((x, j), l))
    (z : (dyadicRefreshNext X P hdH hconn F hD hd c).network.Half ((x, j), l)) (ps : List PosCode),
    PlacedList X _ _ pa ps →
    ∃ I : List (List (EntryInput F)),
      wr (refreshKIn P hdH hconn F hD hd g X c x j l ps z) = I.map (List.map (MotifFields.fixedInput F)) ∧
      entriesValue F (fun _ => zero_lt_one) κ I =
        ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).kernel ((x, j), l) pa z

/-- **Refresh plan writer** (radius 1): one polynomial-time program for all `g` and `κ`. -/
def RefreshKernelProgram : Prop :=
  ∃ wr : RefreshKIn → List (List (MotifFields.FixedInput (Fin (2 ^ a)))), Poly wr ∧
    RefreshKernelOK P hdH hconn F hD hd wr

end Refresh

end

end P1P5.KW
