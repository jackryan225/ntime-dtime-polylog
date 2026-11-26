import P1SolF0R.HeaderPlan
import P1SolF0R.ChunkFacts
import P1SolF0R.Links
import P1SolF0R.Entry

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1Wit P1ChkFinal.AstraC10 P1SolFactor P1SolFactor.Owner
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

def resolveHeader (V : FiniteMultiTapeMachine) (x : List Bool) (p : HeaderPlan) : Header :=
  p.1 ++ p.2.map (fun q => tally (resolvePin V q (P1Batch.fetch x (pinReq q))))

theorem headerPlan_pin_bound (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (cross : CrossIn → Bool) (p : LocalInput) :
    (headerPlan V tape cross p).2.length ≤ p.1.1.2.2.1.length := by
  simp only [headerPlan, Bool.cond_eq_ite, noPins_eq]
  split_ifs <;> simp only [List.length_nil, Nat.zero_le, portPlan, pinColumn_length, le_refl]

def canonicalLocal {K : Type} [Fintype K] [DecidableEq K] (B I : ℕ) {h : ℕ} (w g : ℕ)
    (i : Fin I) (l : Loc K h) (twin : Bool) (lane : BitWord h) (fields : IntervalChunk) : LocalInput :=
  ((((I, 2 ^ h, B, h, w, g), tally (2 ^ h), tally B, tally h), ((locCode l, i.val), twin)),
    (P1ChkFinal.bwNum lane, fields))

private theorem canonicalLane {K : Type} [Fintype K] [DecidableEq K] (B I : ℕ) {h : ℕ} (w g : ℕ)
    (i : Fin I) (l : Loc K h) (twin : Bool) (lane : BitWord h) (fields : IntervalChunk) :
    laneOfRequest (canonicalLocal B I w g i l twin lane fields) = (laneEquiv h lane).val :=
  reverseNum_request lane

section SiteSound

variable (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (x : List Bool) (B I : ℕ) [NeZero B] [NeZero I] {h a : ℕ} (w g : ℕ)
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
    (i : Fin I) (lane : BitWord h) (fields : IntervalChunk)

private def planCorrect (l : Loc V.K h) (twin : Bool) : Prop :=
  resolveHeader V x (headerPlan V tape cross (canonicalLocal B I w g i l twin lane fields)) =
    ruleCode V (siteRuleWith V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset
      (((i, l), twin), lane))

variable (hf : ChunkFacts σ i tape w fields)

variable (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
    cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
      (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)

include hf in
set_option maxHeartbeats 650000 in
private theorem plan_tabC  :
    planCorrect V tape cross x B I w g σ ha i lane fields .tabC false := by
  unfold planCorrect
  have hl := canonicalLane (K := V.K) B I w g i .tabC false lane fields
  simp only [canonicalLocal, headerPlan, locCode, Bool.cond_false, decide_true, Bool.cond_true,
    noPins_eq, resolveHeader, List.map_nil, List.append_nil, siteRuleWith, Bool.false_eq_true,
    ite_false, siteRule]
  unfold tablePlan
  change tableHeader V tape
    (tally B, decide (i.val * 2 ^ h + laneOfRequest (canonicalLocal B I w g i
      (.tabC : Loc V.K h) false lane fields) + 1 = I * 2 ^ h), fields.1,
      laneOfRequest (canonicalLocal B I w g i (.tabC : Loc V.K h) false lane fields)) = _
  rw [hl]
  exact tableHeader_eq V tape B _ _ _ (σ (smallAt i (laneEquiv h lane)))
    (hf.trit (laneEquiv h lane))

set_option maxHeartbeats 650000 in
private theorem plan_tabP (c : Ext V.K) :
    planCorrect V tape cross x B I w g σ ha i lane fields (.tabP c) false := by
  unfold planCorrect
  have hl := propext (path_link σ i c)
  simp only [canonicalLocal, headerPlan, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
    decide_true, Bool.cond_true, noPins_eq, resolveHeader, List.map_nil, List.append_nil,
    pathHeader_eq, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hl]
  all_goals rfl

include hf in
set_option maxHeartbeats 650000 in
private theorem plan_portIn (k : V.K) (δ : Fin 3) :
    planCorrect V tape cross x B I w g σ ha i lane fields (.portIn k δ) false := by
  unfold planCorrect
  have hl := canonicalLane B I w g i (.portIn k δ) false lane fields
  let owner := P1ChkDir.ownToN (prevOwner I σ k i (portQ I σ k i δ))
  have howner : linkOwner V tape true (canonicalLocal B I w g i (.portIn k δ) false lane fields) =
      owner := by
    simp only [linkOwner, canonicalLocal, locCode, directoryTape_eq, Bool.cond_true, hf.prev, owner]
  have hlink : (netMate I σ ((i, .portIn k δ), 1) ≠ none) = (owner ≠ 0) :=
    propext (portIn_link σ i k δ)
  have hport : portPlan V tape (canonicalLocal B I w g i (.portIn k δ) false lane fields) =
      pinColumn V ((tally B, decide (k = V.inputTape)),
        (g, 2 ^ h, startInChunk (fields.2.1, w, tape k), δ.val, (laneEquiv h lane).val)) := by
    simp only [portPlan, canonicalLocal, locCode, directoryTape_eq, laneOfRequest, reverseNum_request]
  simp only [canonicalLocal, locCode] at howner hport
  by_cases ho : owner = 0
  · have hn : ¬ owner ≠ 0 := fun hne => hne ho
    simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true,
      howner, ho, hport, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hlink, hn,
      resolveHeader, List.singleton_append]
    exact pinColumn_header V B g σ i k δ (laneEquiv h lane)
      (startInChunk (fields.2.1, w, tape k)) x (hf.start k)
  · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true,
      howner, ho, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hlink, ne_eq, ho,
      not_false_eq_true, decide_true, ite_true, resolveHeader, noPins_eq, List.map_nil, List.append_nil]
    all_goals rfl

include hf in
set_option maxHeartbeats 650000 in
private theorem plan_portOut (k : V.K) (δ : Fin 3) :
    planCorrect V tape cross x B I w g σ ha i lane fields (.portOut k δ) false := by
  unfold planCorrect
  let owner := P1ChkDir.ownToN (nextOwner I σ k i (portQ I σ k i δ))
  have howner : linkOwner V tape false
      (canonicalLocal B I w g i (.portOut k δ) false lane fields) = owner := by
    simp only [linkOwner, canonicalLocal, locCode, directoryTape_eq, Bool.cond_false, hf.next, owner]
  have hlink : (netMate I σ ((i, .portOut k δ), 1) ≠ none) = (owner ≠ 0) :=
    propext (portOut_link σ i k δ)
  simp only [canonicalLocal, locCode] at howner
  by_cases ho : owner = 0
  · have hn : ¬ owner ≠ 0 := fun hne => hne ho
    simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true,
      howner, ho, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hlink, hn,
      resolveHeader, noPins_eq, List.map_nil, List.append_nil, ruleCode]
    all_goals rfl
  · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true,
      howner, ho, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hlink, ne_eq, ho,
      not_false_eq_true, decide_true, ite_true, resolveHeader, noPins_eq, List.map_nil, List.append_nil]
    all_goals rfl

include hf hc in
set_option maxHeartbeats 650000 in
private theorem plan_rt (k : V.K) (c : Fin (2 * (h + 3))) (typ : BitWord 3) :
    planCorrect V tape cross x B I w g σ ha i lane fields (.rt k c typ) false := by
  unfold planCorrect
  simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
    decide_true, Bool.cond_true, resolveHeader, noPins_eq, List.map_nil, List.append_nil]
  unfold contentHeader
  dsimp only
  let col : Fin (2 * (3 + h)) := Fin.cast (by rw [Nat.add_comm h 3]) c
  rw [directoryTape_eq, hf.centers, contentTables_eq, type3_number]
  refine (congrArg (routeHeader cross) (routeArgs_eq (t := 3) (h := h) (by decide) col typ lane _)).trans ?_
  exact routeHeader_eq_dimension cross hc V (3 + h) col (accAddr I σ i k) (addrOf typ lane)

include hc in
set_option maxHeartbeats 650000 in
private theorem plan_st (c : Fin (2 * (h + 1))) (typ : BitWord 1) :
    planCorrect V tape cross x B I w g σ ha i lane fields (.st c typ) false := by
  unfold planCorrect
  simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
    decide_true, Bool.cond_true, resolveHeader, noPins_eq, List.map_nil, List.append_nil]
  unfold stateHeader
  dsimp only
  let col : Fin (2 * (1 + h)) := Fin.cast (by rw [Nat.add_comm h 1]) c
  rw [stateTables_eq, type1_number]
  refine (congrArg (routeHeader cross) (routeArgs_eq (t := 1) (h := h) (by decide) col typ lane _)).trans ?_
  exact routeHeader_eq_dimension cross hc V (1 + h) col (stAddr h) (addrOf typ lane)

set_option maxHeartbeats 650000 in
private theorem plan_eIn  :
    planCorrect V tape cross x B I w g σ ha i lane fields .eIn false := by
  unfold planCorrect
  by_cases hi : i.val = 0
  · by_cases hj : (laneEquiv h lane).val = 0
    · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
        decide_true, Bool.cond_true,
        hi, laneOfRequest, reverseNum_request, hj, siteRuleWith, siteRule, Bool.false_eq_true, ite_false,
        ite_true, resolveHeader,
        noPins_eq, List.map_nil, List.append_nil, initHeader_eq]
    · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
        decide_true, Bool.cond_true,
        hi, laneOfRequest, reverseNum_request, hj, siteRuleWith, siteRule, Bool.false_eq_true, ite_false,
        ite_true, resolveHeader,
        noPins_eq, List.map_nil, List.append_nil, ruleCode]
  · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true, hi, siteRuleWith, siteRule, Bool.false_eq_true, ite_false,
      resolveHeader, noPins_eq, List.map_nil, List.append_nil]
    all_goals rfl

set_option maxHeartbeats 650000 in
private theorem plan_eOut  :
    planCorrect V tape cross x B I w g σ ha i lane fields .eOut false := by
  unfold planCorrect
  have hl := propext (end_link σ i)
  by_cases hi : i.val + 1 < I
  · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true, hi, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hl,
      ite_true, resolveHeader, noPins_eq, List.map_nil, List.append_nil]
    all_goals rfl
  · simp only [headerPlan, canonicalLocal, locCode, Bool.cond_false, Nat.reduceEqDiff, decide_false,
      decide_true, Bool.cond_true, hi, siteRuleWith, siteRule, Bool.false_eq_true, ite_false, hl,
      resolveHeader, noPins_eq, List.map_nil, List.append_nil, ruleCode]

end SiteSound

theorem headerPlan_sound (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (cross : CrossIn → Bool)
    (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
      cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
        (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)
    (x : List Bool) (B I : ℕ) [NeZero B] [NeZero I] {h a : ℕ} (w g : ℕ)
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
    (i : Fin I) (l : Loc V.K h) (twin : Bool) (lane : BitWord h) (fields : IntervalChunk)
    (hf : ChunkFacts σ i tape w fields) :
    resolveHeader V x (headerPlan V tape cross (canonicalLocal B I w g i l twin lane fields)) =
      ruleCode V (siteRuleWith V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset
        (((i, l), twin), lane)) := by
  cases twin
  case true => rfl
  case false =>
    cases l with
    | tabC => exact plan_tabC V tape cross x B I w g σ ha i lane fields hf
    | tabP c => exact plan_tabP V tape cross x B I w g σ ha i lane fields c
    | portIn k δ => exact plan_portIn V tape cross x B I w g σ ha i lane fields hf k δ
    | portOut k δ => exact plan_portOut V tape cross x B I w g σ ha i lane fields hf k δ
    | rt k c typ => exact plan_rt V tape cross x B I w g σ ha i lane fields hf hc k c typ
    | st c typ => exact plan_st V tape cross x B I w g σ ha i lane fields hc c typ
    | eIn => exact plan_eIn V tape cross x B I w g σ ha i lane fields
    | eOut => exact plan_eOut V tape cross x B I w g σ ha i lane fields

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.headerPlan_sound
