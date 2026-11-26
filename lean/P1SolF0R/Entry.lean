import P1SolF0R.Output
import P1SolFactor.Factor0Poly
import P1ChkDir.C4
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Net P1P5.F0 P1SolFactor P1SolFactor.Owner
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

theorem halfCode0_eq {a h : ℕ} (X : State a h) (s : X.network.Site) (z : X.network.Half s) :
    halfCode0 X s z = P1P5.KW.halfCode X s z := rfl

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h a : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings)

/-- The header at a twin site contains only the free-rule tag. -/
theorem twin_header (ι : Fin I) (l : Loc V.K h) (lane : BitWord h) :
    ruleCode V (P1SolFactor.siteRuleWith V B L I σ ha bset (((ι, l), true), lane)) = [tally 0] := by
  simp only [P1SolFactor.siteRuleWith, if_true, ruleCode]

/-- Pointwise header agreement suffices for agreement on an arbitrary list of requests. -/
theorem finish_eq {F : Type} [CommRing F] (test : EntryCode → Bool)
    (htest : ∀ (s : (rnState V B I σ ha).network.Site) (z : (rnState V B I σ ha).network.Half s),
      test (ruleCode V (P1SolFactor.siteRuleWith V B L I σ ha bset s),
        halfCode0 (rnState V B I σ ha) s z) = decide (rnSiteOK V B L I σ ha bset s z))
    (c : F)
    (entries : List (Σ s : (rnState V B I σ ha).network.Site, (rnState V B I σ ha).network.Half s))
    (headers : P1P5.KW.PosCode → Header)
    (hheaders : ∀ z ∈ entries, headers ((P1P7.addr (rnState V B I σ ha) z.1.1, P1ChkFinal.bwNum z.1.2),
      P1P5.KW.halfCode (rnState V B I σ ha) z.1 z.2) =
      ruleCode V (P1SolFactor.siteRuleWith V B L I σ ha bset z.1)) :
    finish test (⟨c⟩, (entries.map fun z => ((P1P7.addr (rnState V B I σ ha) z.1.1,
      P1ChkFinal.bwNum z.1.2), P1P5.KW.halfCode (rnState V B I σ ha) z.1 z.2)).map
      (fun q => (headers q, q.2))) =
    entries.map (fun z => ⟨c * @ite F (rnSiteOK V B L I σ ha bset z.1 z.2)
      (Classical.propDecidable _) 1 0⟩) := by
  simp only [finish, List.map_map]
  apply List.map_congr_left
  intro z hz
  dsimp only [Function.comp_def]
  rw [hheaders z hz, ← halfCode0_eq, htest]
  unfold weight
  split <;> simp_all

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.finish_eq
