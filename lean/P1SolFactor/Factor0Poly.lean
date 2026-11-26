import P1SolFactor.FactorTableTest

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

namespace P1SolFactor.SolFactor

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1SolFactor.Owner P1SolFactor.SolHalf P1SolFactor.SolPolyWords
open scoped Classical

noncomputable section

def entry (V : FiniteMultiTapeMachine) (p : Query) : Bool :=
  bif isTag 0 p then true
  else bif isTag 1 p then tableTest V p
  else bif isTag 2 p then pathTest V p
  else bif isTag 3 p then pinTest V p
  else bif isTag 4 p then copyTest p
  else bif isTag 5 p then routeTest p
  else fixedTest p

theorem entry_poly (V : FiniteMultiTapeMachine) : Poly (entry V) := by
  unfold entry
  fun_prop

def runRule (V : FiniteMultiTapeMachine) : SiteRule V → Query → Bool
  | .free => fun _ => true
  | .table .. => tableTest V
  | .path .. => pathTest V
  | .pins _ => pinTest V
  | .copy .. => copyTest
  | .route .. => routeTest
  | .fixed _ => fixedTest

theorem entry_rule (V : FiniteMultiTapeMachine) (r : SiteRule V) (x : Fields) :
    entry V (ruleCode V r, x) = runRule V r (ruleCode V r, x) := by
  cases r <;> rfl

section Routed

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h a : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings)

local notation "X" => rnState V B I σ ha
local notation "slot" n => Fin.castLE ha (n : Fin 4)

omit [NeZero B] in
private theorem outBits_full (u : (X).network.Site) (z : (X).network.Half u)
    (j : Fin (2 ^ a)) (w : ℕ) (hw : slotWidth X u false j = w) :
    fieldBits X u z false j = List.ofFn (outWord X u z j w) := by
  rw [← wordAtWidth_out]
  unfold fieldBits
  rw [← hw, wordAtWidth_ofFn, asWord_self]

private theorem eval_basic (u : (X).network.Site) (z : (X).network.Half u)
    (hb : IsBasicRule (siteRuleWith V B L I σ ha bset u)) :
    entry V (ruleCode V (siteRuleWith V B L I σ ha bset u), halfCode0 X u z) = true ↔
      rnSiteOK V B L I σ ha bset u z := by
  rw [rnSiteOK_iff_basic (R := Bool) V B L I σ ha bset u z hb, entry_rule]
  generalize siteRuleWith V B L I σ ha bset u = r at hb ⊢
  cases r with
  | free => exact iff_true_intro rfl
  | copy o i => exact copyTest_correct X u z V ha o i
  | fixed w => exact fixedTest_correct X u z V ha w
  | table _ _ _ => exact False.elim hb
  | path _ _ => exact False.elim hb
  | pins _ => exact False.elim hb
  | route _ _ => exact False.elim hb

private theorem eval_pin (ι : Fin I) (k : V.K) (δ : Fin 3) (lane : BitWord h)
    (z : (X).network.Half (((ι, .portIn k δ), false), lane))
    (hm : netMate I σ ((ι, Loc.portIn k δ), 1) = none) :
    let u : (X).network.Site := (((ι, Loc.portIn k δ), false), lane)
    entry V (ruleCode V (siteRuleWith V B L I σ ha bset u), halfCode0 X u z) = true ↔
      rnSiteOK V B L I σ ha bset u z := by
  intro u
  let Z := portBlock I σ ι k δ (laneEquiv h lane)
  let o (j : Fin B) : Option V.Γ :=
    let cell := Z * (B : ℤ) + (j : ℤ)
    if (L.guessAt k cell).isSome then none else some (L.base k cell)
  have hh : siteRuleWith V B L I σ ha bset u = .pins (List.ofFn o) := by
    simp [u, siteRuleWith, siteRule, hm, o, Z]
  rw [hh, entry_rule]
  change pinTest V (ruleCode V (.pins (List.ofFn o)), halfCode0 X u z) = true ↔ _
  have hw := pin_slot_width V B I σ ha ι k δ lane
  have hword := outSlot_half X u z (slot 0)
  change outSlot (halfCode0 X u z, tally 0) = _ at hword
  rw [outBits_full V B I σ ha u z _ _ hw] at hword
  have hp : dropT (tally 1, ruleCode V (.pins (List.ofFn o))) =
      List.ofFn (fun j => pinCode V (o j)) := by
    simp only [ruleCode, dropT_tally, List.drop_succ_cons, List.drop_zero, List.map_ofFn,
      Function.comp_def, pinCode]
  rw [pinTest_word V B o _ List.length_ofFn _ hp hword]
  simp only [ofFn_eq_iff]
  simp [rnSiteOK, u, hm, PinOK, o, Z, pinValue_iff]

private theorem eval_table (ι : Fin I) (lane : BitWord h)
    (z : (X).network.Half (((ι, .tabC), false), lane)) :
    let u : (X).network.Site := (((ι, Loc.tabC), false), lane)
    entry V (ruleCode V (siteRuleWith V B L I σ ha bset u), halfCode0 X u z) = true ↔
      rnSiteOK V B L I σ ha bset u z := by
  intro u
  let i : ℕ := ι.val * 2 ^ h + (laneEquiv h lane).val
  have hi : i < I * 2 ^ h := by
    unfold i
    calc
      _ < ι.val * 2 ^ h + 2 ^ h := Nat.add_lt_add_left (laneEquiv h lane).isLt _
      _ = (ι.val + 1) * 2 ^ h := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ I * 2 ^ h := Nat.mul_le_mul_right _ ι.isLt
  let idx : Fin (I * 2 ^ h) := ⟨i, hi⟩
  let last : Bool := decide (i + 1 = I * 2 ^ h)
  let moves : V.K → Fin 3 := σ idx
  let word := List.ofFn (outWord X u z (slot 0) (tupWidth V B))
  have hh : siteRuleWith V B L I σ ha bset u =
      .table B last (List.ofFn (fun j => moves ((kIdx V.K).symm j))) := rfl
  have he : outSlot (halfCode0 X u z, tally 0) = word := by
    have hp := outSlot_half X u z (slot 0)
    change outSlot (halfCode0 X u z, tally 0) = _ at hp
    exact hp.trans (outBits_full V B I σ ha u z _ _ (center_slot_width V B I σ ha ι lane))
  rw [hh, entry_rule]
  change tableCore V (tally B, (flag (tally (if last then 1 else 0)),
    ((List.ofFn (fun j => moves ((kIdx V.K).symm j))).map (fun m => tally m.val),
      outSlot (halfCode0 X u z, tally 0)))) = true ↔ _
  simp only [flag_tally, List.map_ofFn, Function.comp_def, he]
  rw [tableCore_correct]
  simp only [word, ofFn_eq_iff, last, decide_eq_true_eq]
  change (∃ d : LocalIn V B, outWord X u z (slot 0) (tupWidth V B) =
      tupleWord V B (extData V B d (evolve d)) ∧ (evolve d).move = moves ∧
        (i + 1 = I * 2 ^ h → Accepts B (evolve d))) ↔
    (∃ d : LocalIn V B, outWord X u z (slot 0) (tupWidth V B) =
      tupleWord V B (extData V B d (evolve d)) ∧ (∀ hh : i < I * 2 ^ h, (evolve d).move = σ ⟨i, hh⟩) ∧
        (i + 1 = I * 2 ^ h → Accepts B (evolve d)))
  refine exists_congr (fun d => and_congr_right (fun _ => and_congr_left (fun _ => ?_)))
  exact ⟨fun h _ => h, fun h => h hi⟩

theorem entry_correct (u : (X).network.Site) (z : (X).network.Half u) :
    entry V (ruleCode V (siteRuleWith V B L I σ ha bset u), halfCode0 X u z) = true ↔
      rnSiteOK V B L I σ ha bset u z := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin
  · cases loc with
    | tabC => exact eval_table V B L I σ ha bset ι lane z
    | tabP c =>
      let site : (X).network.Site := (((ι, Loc.tabP c), false), lane)
      let linked := netMate I σ ((ι, Loc.tabP c), 1) ≠ none
      have hh : siteRuleWith V B L I σ ha bset site = .path (decide linked) c := rfl
      change entry V (ruleCode V (siteRuleWith V B L I σ ha bset site), _) = true ↔ _
      rw [hh, entry_rule]
      exact pathTest_correct V B L I σ ha bset ι c lane z
    | portIn k δ =>
      by_cases hm : netMate I σ ((ι, Loc.portIn k δ), 1) = none
      · exact eval_pin V B L I σ ha bset ι k δ lane z hm
      · exact eval_basic V B L I σ ha bset _ z (by simp [siteRuleWith, siteRule, hm, IsBasicRule])
    | portOut k δ =>
      apply eval_basic V B L I σ ha bset _ z
      by_cases hm : netMate I σ ((ι, Loc.portOut k δ), 1) = none <;>
        simp [siteRuleWith, siteRule, hm, IsBasicRule]
    | rt k j π =>
      let site : (X).network.Site := (((ι, Loc.rt k j π), false), lane)
      let settings := bset (3 + h) (accAddr I σ ι k)
      let address := addrOf π lane
      have hh : siteRuleWith V B L I σ ha bset site =
          .route (routeInChoice settings j address) (routeOutChoice settings j address) := rfl
      change entry V (ruleCode V (siteRuleWith V B L I σ ha bset site), _) = true ↔ _
      rw [hh, entry_rule]
      exact (routeTest_correct X site z V ha _ _).trans
        (rnSiteOK_rt_fields (R := Bool) V B L I σ ha bset ι k j π lane z).symm
    | st j π =>
      let site : (X).network.Site := (((ι, Loc.st j π), false), lane)
      let settings := bset (1 + h) (stAddr h)
      let address := addrOf π lane
      have hh : siteRuleWith V B L I σ ha bset site =
          .route (routeInChoice settings j address) (routeOutChoice settings j address) := rfl
      change entry V (ruleCode V (siteRuleWith V B L I σ ha bset site), _) = true ↔ _
      rw [hh, entry_rule]
      exact (routeTest_correct X site z V ha _ _).trans
        (rnSiteOK_st_fields (R := Bool) V B L I σ ha bset ι j π lane z).symm
    | eIn =>
      apply eval_basic V B L I σ ha bset _ z
      by_cases hx : ι.val = 0 <;> simp [siteRuleWith, siteRule, IsBasicRule, hx]
    | eOut =>
      apply eval_basic V B L I σ ha bset _ z
      by_cases hm : netMate I σ ((ι, Loc.eOut), 1) = none <;>
        simp [siteRuleWith, siteRule, hm, IsBasicRule]
  · exact eval_basic V B L I σ ha bset _ z (by simp [siteRuleWith, IsBasicRule])

end Routed

end

end P1SolFactor.SolFactor

theorem P1SolFactor.factor0EntryPoly (V : FiniteMultiTapeMachine) (a : ℕ) (ha : 4 ≤ 2 ^ a) : P1SolFactor.Owner.Factor0EntryPoly V a ha := by
  open scoped Classical in
  refine ⟨SolFactor.entry V, SolFactor.entry_poly V, ?_⟩
  intro g h B hB L I hI σ bset u z
  have hh := SolFactor.entry_correct V B L I σ ha bset u z
  by_cases hp : P1Net.rnSiteOK V B L I σ ha bset u z
  · simpa only [hp, decide_true] using hh.mpr hp
  · have hn := Bool.eq_false_iff.mpr (fun h => hp (hh.mp h))
    simpa only [hp, decide_false] using hn

#print axioms P1SolFactor.factor0EntryPoly
