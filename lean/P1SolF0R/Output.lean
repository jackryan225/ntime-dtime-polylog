import P1P5.Factor0Target
import P1ChkDir.C4
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Net P1P5.F0
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

abbrev Header := List Tally
abbrev HalfCode := List (List Bool) × List (List Bool)
abbrev EntryCode := Header × HalfCode

/-- Convert a Boolean site decision to its scalar-weighted factor. -/
def weight {F : Type} [CommRing F] (p : Label F × Bool) : Label F :=
  ⟨p.1.val * (if p.2 then 1 else 0)⟩

theorem weight_poly {F : Type} [CommRing F] [Fintype F] :
    Poly (weight (F := F)) :=
  (Easy.finite _).poly

/-- Evaluate a list of prepared entries in the order in which they were requested. -/
def finish {F : Type} [CommRing F] (test : EntryCode → Bool)
    (p : Label F × List EntryCode) : List (Label F) :=
  p.2.map fun entry => weight (p.1, test entry)

theorem finish_poly {F : Type} [CommRing F] [Fintype F] {test : EntryCode → Bool}
    (htest : Poly test) : Poly (finish (F := F) test) := by
  change Poly (polyPush (fun p : Label F × EntryCode => weight (p.1, test p.2)))
  exact Poly.push (⟨0⟩ : Label F) (([] : Header), (([], []) : HalfCode))
    ((Easy.fst.poly.pair (Easy.snd.poly.compose htest)).compose weight_poly)

theorem finish_nil {F : Type} [CommRing F] (test : EntryCode → Bool) (c : Label F) :
    finish test (c, []) = [] := rfl

/-- A twin site always contributes the scalar. -/
theorem twin_factor {F : Type} [CommRing F] (c : F)
    (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
    (I : ℕ) [NeZero I] {h a : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
    (bset : P1P5.F0.SolCone.SwitchSettings) (ι : Fin I) (l : Loc V.K h) (lane : BitWord h)
    (z : (rnState V B I σ ha).network.Half (((ι, l), true), lane)) :
    (⟨c * @ite F (rnSiteOK V B L I σ ha bset (((ι, l), true), lane) z)
      (Classical.propDecidable _) 1 0⟩ : Label F) = ⟨c⟩ := by
  simp only [rnSiteOK, ite_true, mul_one]

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.finish_poly
#print axioms P1SolF0R.SolReader.twin_factor
