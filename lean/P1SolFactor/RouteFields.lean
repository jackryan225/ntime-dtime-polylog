import P1SolFactor.PaddedViews
import P1SolFactor.RouteChoices
import P1SolFactor.RoutedWidths

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net SolRows
open scoped Classical

noncomputable section

/-- Test a route using the four physical fields, with implicit zero padding. -/
def routeFieldsOK {R : Type} (crossIn : Bool) (crossOut : Option Bool)
    (in2 in3 out0 out1 : List (P1P5.EvalSym R)) : Prop :=
  let item := if crossIn then in3 else in2
  match crossOut with
  | none => paddedAgree decodeInputBit item out0
  | some false => paddedAgree decodeInputBit item out0 ∧ paddedAgree decodeInputBit out1 []
  | some true => paddedAgree decodeInputBit item out1 ∧ paddedAgree decodeInputBit out0 []

section Half

variable {a h : ℕ} (X : State a h) (u : X.network.Site) (z : X.network.Half u)

theorem routeFieldsOK_iff_chosen {R : Type} (crossIn : Bool) (crossOut : Option Bool)
    (i2 i3 o0 o1 : Fin (2 ^ a)) (width : ℕ)
    (hi2 : slotWidth X u true i2 ≤ width) (hi3 : slotWidth X u true i3 ≤ width)
    (ho0 : slotWidth X u false o0 ≤ width) (ho1 : slotWidth X u false o1 ≤ width) :
    routeFieldsOK (R := R) crossIn crossOut
        ((fieldBits X u z true i2).map inputBit) ((fieldBits X u z true i3).map inputBit)
        ((fieldBits X u z false o0).map inputBit) ((fieldBits X u z false o1).map inputBit) ↔
      chosenRouteOK crossIn crossOut (inWord X u z i2 width) (inWord X u z i3 width)
        (outWord X u z o0 width) (outWord X u z o1 width) := by
  have h20 := paddedAgree_in_out (R := R) X u z i2 o0 width hi2 ho0
  have h21 := paddedAgree_in_out (R := R) X u z i2 o1 width hi2 ho1
  have h30 := paddedAgree_in_out (R := R) X u z i3 o0 width hi3 ho0
  have h31 := paddedAgree_in_out (R := R) X u z i3 o1 width hi3 ho1
  have h0 := paddedAgree_out_zero (R := R) X u z o0 width ho0
  have h1 := paddedAgree_out_zero (R := R) X u z o1 width ho1
  cases crossOut with
  | none => cases crossIn <;> simp [routeFieldsOK, chosenRouteOK, h20, h30, eq_comm]
  | some b =>
    cases crossIn <;> cases b <;>
      simp [routeFieldsOK, chosenRouteOK, h20, h21, h30, h31, h0, h1, eq_comm]

end Half

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings)

local notation "X" => rnState V B I σ ha
local notation "slot" s => Fin.castLE ha (s : Fin 4)

omit [NeZero B] in
/-- The physical inputs of a routing position implement the selected-arc test. -/
theorem routeFieldsOK_of_other {R : Type} (ι : Fin I) (loc : Loc V.K h) (lane : BitWord h)
    (z : (X).network.Half (((ι, loc), false), lane)) (crossIn : Bool) (crossOut : Option Bool)
    (hc : loc ≠ .tabC) (hp : ∀ c, loc ≠ .tabP c) :
    let u := (((ι, loc), false), lane)
    routeFieldsOK (R := R) crossIn crossOut
        ((fieldBits X u z true (slot 2)).map inputBit) ((fieldBits X u z true (slot 3)).map inputBit)
        ((fieldBits X u z false (slot 0)).map inputBit) ((fieldBits X u z false (slot 1)).map inputBit) ↔
      chosenRouteOK crossIn crossOut (inWord X u z (slot 2) (strWidth V B))
        (inWord X u z (slot 3) (strWidth V B)) (outWord X u z (slot 0) (strWidth V B))
        (outWord X u z (slot 1) (strWidth V B)) := by
  have hin (s : Fin 4) := slotWidth_in_le_string V B I σ ha (ι, loc) s lane (fun c he => (hp c he).elim)
  have hout (s : Fin 4) := slotWidth_out_le_string V B I σ ha (ι, loc) s lane
    (fun he => (hc he).elim) (fun c he => (hp c he).elim)
  exact routeFieldsOK_iff_chosen X _ z crossIn crossOut _ _ _ _ _ (hin 2) (hin 3) (hout 0) (hout 1)

theorem rnSiteOK_rt_fields {R : Type} (ι : Fin I) (k : V.K) (column : Fin (2 * (h + 3)))
    (π : BitWord 3) (lane : BitWord h) (z : (X).network.Half (((ι, .rt k column π), false), lane)) :
    let u := (((ι, Loc.rt k column π), false), lane)
    let settings := bset (3 + h) (accAddr I σ ι k)
    let address := addrOf π lane
    rnSiteOK V B L I σ ha bset u z ↔
      routeFieldsOK (R := R) (routeInChoice settings column address) (routeOutChoice settings column address)
        ((fieldBits X u z true (slot 2)).map inputBit) ((fieldBits X u z true (slot 3)).map inputBit)
        ((fieldBits X u z false (slot 0)).map inputBit) ((fieldBits X u z false (slot 1)).map inputBit) := by
  intro u settings address
  exact (routeOK_iff_chosen settings column address ..).trans
    (routeFieldsOK_of_other V B I σ ha ι (.rt k column π) lane z _ _ (by simp) (by simp)).symm

theorem rnSiteOK_st_fields {R : Type} (ι : Fin I) (column : Fin (2 * (h + 1)))
    (π : BitWord 1) (lane : BitWord h) (z : (X).network.Half (((ι, .st column π), false), lane)) :
    let u := (((ι, Loc.st column π), false), lane)
    let settings := bset (1 + h) (stAddr h)
    let address := addrOf π lane
    rnSiteOK V B L I σ ha bset u z ↔
      routeFieldsOK (R := R) (routeInChoice settings column address) (routeOutChoice settings column address)
        ((fieldBits X u z true (slot 2)).map inputBit) ((fieldBits X u z true (slot 3)).map inputBit)
        ((fieldBits X u z false (slot 0)).map inputBit) ((fieldBits X u z false (slot 1)).map inputBit) := by
  intro u settings address
  exact (routeOK_iff_chosen settings column address ..).trans
    (routeFieldsOK_of_other V B I σ ha ι (.st column π) lane z _ _ (by simp) (by simp)).symm

end RoutedSite

end

end P1SolFactor.SolHalf

#print axioms P1SolFactor.SolHalf.rnSiteOK_rt_fields
#print axioms P1SolFactor.SolHalf.rnSiteOK_st_fields
