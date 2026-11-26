import P1SolFactor.RouteChoices

namespace P1SolFactor

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open scoped Classical

noncomputable section

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings)

private def routedRule {m : ℕ} [NeZero m] (settings : Routing.Settings m) (column : ℕ)
    (address : Routing.Addr m) : SiteRule V :=
  .route (routeInChoice settings column address) (routeOutChoice settings column address)

/-- The rule used by the scalar-parametrized contract, including the supplied switch settings. -/
def siteRuleWith (u : (rnState V B I σ ha).network.Site) : SiteRule V :=
  if u.1.2 then .free else
    match u.1.1.2 with
    | .rt k j π => routedRule V (bset (3 + h) (accAddr I σ u.1.1.1 k)) j (addrOf π u.2)
    | .st j π => routedRule V (bset (1 + h) (stAddr h)) j (addrOf π u.2)
    | _ => siteRule V B L I σ ha u

theorem factorRegsWith_header {R : Type} [CommRing R] (u : (rnState V B I σ ha).network.Site) (c : R) :
    factorRegsWith V B L I σ ha bset u c 2 = encRule V (siteRuleWith V B L I σ ha bset u) := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin
  · cases loc with
    | rt k j π => exact factorRegsWith_rt_header V B L I σ ha bset ι k j π lane c
    | st j π => exact factorRegsWith_st_header V B L I σ ha bset ι j π lane c
    | _ => simp [factorRegsWith, factor0Regs, siteRuleWith]
  · simp [factorRegsWith, factor0Regs, siteRuleWith, siteRule]

end

end P1SolFactor
