import P1SolFactor.OwnerTargets
import P1SolFactor.BasicSiteCases
import P1SolFactor.RouteFields
import P1SolFactor.TupleViews
import P1SolFactor.PolyLists

namespace P1SolFactor.SolFactor

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1SolFactor.Owner P1SolFactor.SolHalf P1SolFactor.SolPolyWords
open scoped Classical

noncomputable section

abbrev Fields := List (List Bool) × List (List Bool)
abbrev Query := List Tally × Fields

def header (n : ℕ) (p : Query) : Tally := Iter.pick [] (p.1, tally n)

def outSlot (p : Fields × Tally) : List Bool := Iter.pick [] (p.1.1, p.2)

def inSlot (p : Fields × Tally) : List Bool := Iter.pick [] (p.1.2, p.2)

def isTag (n : ℕ) (p : Query) : Bool := eqT (header 0 p, tally n)

def flag (t : Tally) : Bool := eqT (t, tally 1)

@[fun_prop] theorem header_poly (n : ℕ) : Poly (header n) := by unfold header; fun_prop
@[fun_prop] theorem outSlot_poly : Poly outSlot := by unfold outSlot; fun_prop
@[fun_prop] theorem inSlot_poly : Poly inSlot := by unfold inSlot; fun_prop
@[fun_prop] theorem isTag_poly (n : ℕ) : Poly (isTag n) := by unfold isTag; fun_prop
@[fun_prop] theorem flag_poly : Poly flag := by unfold flag; fun_prop

@[simp] theorem flag_tally (b : Bool) : flag (tally (if b then 1 else 0)) = b := by
  cases b <;> rfl

@[simp] theorem header_pair (n : ℕ) (xs : List Tally) (p : Fields) :
    header n (xs, p) = xs.getD n [] := pick_getD _ _ _

variable {a h : ℕ} (X : State a h) (u : X.network.Site) (z : X.network.Half u)

@[simp] theorem outSlot_half (i : Fin (2 ^ a)) :
    outSlot (halfCode0 X u z, tally i.val) = fieldBits X u z false i := by
  unfold outSlot halfCode0
  rw [Iter.entry]
  rfl

@[simp] theorem inSlot_half (i : Fin (2 ^ a)) :
    inSlot (halfCode0 X u z, tally i.val) = fieldBits X u z true i := by
  unfold inSlot halfCode0
  rw [Iter.entry]
  rfl

theorem paddedEq_fields (xs ys : List Bool) :
    paddedEq (xs, ys) = true ↔ SolRows.paddedAgree (decodeInputBit (R := Bool)) (xs.map inputBit) (ys.map inputBit) := by
  rw [paddedEq_true]
  simp only [SolRows.paddedAgree, map_decodeInputBit_inputBit]

def copyTest (p : Query) : Bool :=
  paddedEq (inSlot (p.2, header 2 p), outSlot (p.2, header 1 p))

def fixedTest (p : Query) : Bool :=
  paddedEq (outSlot (p.2, tally 0), (dropT (tally 1, p.1)).map flag)

@[fun_prop] theorem copyTest_poly : Poly copyTest := by unfold copyTest; fun_prop

@[fun_prop] theorem fixedTest_poly : Poly fixedTest := by
  unfold fixedTest
  have hm : Poly (fun p : Query => (dropT (tally 1, p.1)).map flag) :=
    (show Poly (fun p : Query => dropT (tally 1, p.1)) by fun_prop).compose
      (Code.Poly.maps flag flag_poly)
  exact ((show Poly (fun p : Query => outSlot (p.2, tally 0)) by fun_prop).pair hm).compose paddedEq_poly

theorem copyTest_correct (V : FiniteMultiTapeMachine) (ha : 4 ≤ 2 ^ a) (o i : Fin 4) :
    copyTest (ruleCode V (.copy o i), halfCode0 X u z) = true ↔
      basicHalfOK (R := Bool) X u ha z (.copy o i : SiteRule V) := by
  change paddedEq (inSlot (_, tally (i.castLE ha).val), outSlot (_, tally (o.castLE ha).val)) = true ↔ _
  rw [inSlot_half, outSlot_half, paddedEq_fields]
  rfl

theorem fixedTest_correct (V : FiniteMultiTapeMachine) (ha : 4 ≤ 2 ^ a) (word : List Bool) :
    fixedTest (ruleCode V (.fixed word), halfCode0 X u z) = true ↔
      basicHalfOK (R := Bool) X u ha z (.fixed word : SiteRule V) := by
  have hw : (word.map (fun b => tally (if b then 1 else 0))).map flag = word := by
    simp only [List.map_map, Function.comp_def, flag_tally]
    exact List.map_id word
  change paddedEq (outSlot (_, tally ((0 : Fin 4).castLE ha).val),
    (word.map (fun b => tally (if b then 1 else 0))).map flag) = true ↔ _
  rw [outSlot_half, hw, paddedEq_fields]
  rfl

def routeTest (p : Query) : Bool :=
  let picked := inSlot (p.2, bif flag (header 1 p) then tally 3 else tally 2)
  let o0 := outSlot (p.2, tally 0)
  let o1 := outSlot (p.2, tally 1)
  let out := header 2 p
  bif eqT (out, tally 0) then paddedEq (picked, o0)
  else bif eqT (out, tally 1) then andB (paddedEq (picked, o0), paddedEq (o1, []))
  else andB (paddedEq (picked, o1), paddedEq (o0, []))

@[fun_prop] theorem routeTest_poly : Poly routeTest := by unfold routeTest; fun_prop

theorem routeTest_correct (V : FiniteMultiTapeMachine) (ha : 4 ≤ 2 ^ a) (i : Bool) (o : Option Bool) :
    routeTest (ruleCode V (.route i o), halfCode0 X u z) = true ↔
      routeFieldsOK (R := Bool) i o
        ((fieldBits X u z true ((2 : Fin 4).castLE ha)).map inputBit)
        ((fieldBits X u z true ((3 : Fin 4).castLE ha)).map inputBit)
        ((fieldBits X u z false ((0 : Fin 4).castLE ha)).map inputBit)
        ((fieldBits X u z false ((1 : Fin 4).castLE ha)).map inputBit) := by
  have ho0 := outSlot_half X u z ((0 : Fin 4).castLE ha)
  have ho1 := outSlot_half X u z ((1 : Fin 4).castLE ha)
  have hi2 := inSlot_half X u z ((2 : Fin 4).castLE ha)
  have hi3 := inSlot_half X u z ((3 : Fin 4).castLE ha)
  change outSlot (_, tally 0) = _ at ho0
  change outSlot (_, tally 1) = _ at ho1
  change inSlot (_, tally 2) = _ at hi2
  change inSlot (_, tally 3) = _ at hi3
  have f0 : flag (tally 0) = false := rfl
  have f1 : flag (tally 1) = true := rfl
  cases i <;> cases o with
  | none => simp [routeTest, ruleCode, -tally_succ, f0, f1, ho0, hi2, hi3,
      paddedEq_fields, routeFieldsOK]
  | some b =>
    cases b <;> simp [routeTest, ruleCode, -tally_succ, f0, f1, ho0, ho1, hi2, hi3,
      andB, paddedEq_fields, routeFieldsOK]

def sliceWord (p : List Bool × (Tally × Tally)) : List Bool :=
  takeT (p.2.2, dropT (mulT (p.2.1, p.2.2), p.1))

@[fun_prop] theorem sliceWord_poly : Poly sliceWord := by unfold sliceWord; fun_prop

@[simp] theorem sliceWord_tally (w : List Bool) (i n : ℕ) :
    sliceWord (w, (tally i, tally n)) = (w.drop (i * n)).take n := by
  simp only [sliceWord, mulT_tally, takeT_tally, dropT_tally]

def pathTest (V : FiniteMultiTapeMachine) (p : Query) : Bool :=
  let t := inSlot (p.2, tally 0)
  let s := sliceWord (t, (header 3 p, divConst (Fintype.card (Ext V.K)) (ruler t)))
  let x := bif flag (header 2 p) then inSlot (p.2, tally 2) else outSlot (p.2, tally 2)
  andB (bif flag (header 1 p) then paddedEq (outSlot (p.2, tally 1), t) else true,
    paddedEq (x, s))

@[fun_prop] theorem pathTest_poly (V : FiniteMultiTapeMachine) : Poly (pathTest V) := by
  unfold pathTest
  fun_prop

theorem paddedEq_width (w : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) :
    paddedEq (xs, ys) = true ↔ wordAtWidth w xs = wordAtWidth w ys := by
  rw [paddedEq_fields, paddedAgree_iff_wordAtWidth (width := w)]
  · simp only [map_decodeInputBit_inputBit]
  · simpa only [List.length_map] using hx
  · simpa only [List.length_map] using hy

theorem ofFn_eq_iff {n : ℕ} {f g : Fin n → Bool} : List.ofFn f = List.ofFn g ↔ f = g := by
  refine ⟨fun e => ?_, congrArg List.ofFn⟩
  funext j
  have hj := congrArg (fun (xs : List Bool) => xs.getD j.val false) e
  simpa only [getD_ofFn, dite_eq_left j.isLt, Fin.eta] using hj

theorem wordAtWidth_full {n : ℕ} (word : Fin n → Bool) :
    wordAtWidth n (List.ofFn word) = List.ofFn word := by
  rw [wordAtWidth_ofFn]
  congr 1
  funext j
  simp [asWord, j.isLt]

section Path

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h a : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings)

local notation "X" => rnState V B I σ ha
local notation "slot" n => Fin.castLE ha (n : Fin 4)
local notation "Wt" => tupWidth V B
local notation "Wx" => strWidth V B

theorem pathTest_correct (ι : Fin I) (c : Ext V.K) (lane : BitWord h)
    (z : (X).network.Half (((ι, .tabP c), false), lane)) :
    let u : (X).network.Site := (((ι, Loc.tabP c), false), lane)
    let linked := netMate I σ ((ι, Loc.tabP c), 1) ≠ none
    pathTest V (ruleCode V (.path (decide linked) c), halfCode0 X u z) = true ↔
      rnSiteOK V B L I σ ha bset u z := by
  intro u linked
  let t := fieldBits X u z true (slot 0)
  let s := List.ofFn (P1Net.segment V B c (inWord X u z (slot 0) Wt))
  have ht : t = List.ofFn (inWord X u z (slot 0) Wt) :=
    path_tuple_word V B I σ ha ι c lane z
  have htlen : t.length = Wt := by rw [ht, List.length_ofFn]
  have hs : sliceWord (t, (tally (extIdx V.K c).val, divConst (Fintype.card (Ext V.K)) (ruler t))) = s := by
    rw [← recover_tally (ruler t), ruler_length, htlen, divConst_tally]
    have hn : 0 < Fintype.card (Ext V.K) := Fintype.card_pos_iff.mpr ⟨Ext.stIn⟩
    rw [show Wt / Fintype.card (Ext V.K) = Wx by
      unfold tupWidth
      rw [Nat.mul_comm, Nat.mul_div_cancel _ hn]]
    rw [sliceWord_tally]
    exact path_tuple_segment V B I σ ha ι c lane z
  have ho1 : (fieldBits X u z false (slot 1)).length ≤ Wt := by
    rw [fieldBits_length, slotWidth_out_netWidth V B I σ ha (ι, .tabP c) 1 lane]
    unfold netWidth
    split
    · exact Nat.zero_le _
    · simp [baseWidth]
  have htie :
      paddedEq (fieldBits X u z false (slot 1), t) = true ↔
        outWord X u z (slot 1) Wt = inWord X u z (slot 0) Wt := by
    rw [paddedEq_width Wt _ _ ho1 htlen.le, wordAtWidth_out, ht, wordAtWidth_full, ofFn_eq_iff]
  have hi2 : (fieldBits X u z true (slot 2)).length ≤ Wx := by
    rw [fieldBits_length]
    exact slotWidth_in_le_string V B I σ ha (ι, .tabP c) 2 lane (fun _ _ => by decide)
  have ho2 : (fieldBits X u z false (slot 2)).length ≤ Wx := by
    rw [fieldBits_length]
    exact slotWidth_out_le_string V B I σ ha (ι, .tabP c) 2 lane
      (by simp) (fun _ _ => by decide)
  have hilen : s.length ≤ Wx := List.length_ofFn.le
  have hti :
      paddedEq (fieldBits X u z true (slot 2), s) = true ↔
        inWord X u z (slot 2) Wx = P1Net.segment V B c (inWord X u z (slot 0) Wt) := by
    rw [paddedEq_width Wx _ _ hi2 hilen, wordAtWidth_in]
    change _ = wordAtWidth Wx (List.ofFn _) ↔ _
    rw [wordAtWidth_full, ofFn_eq_iff]
  have hto :
      paddedEq (fieldBits X u z false (slot 2), s) = true ↔
        outWord X u z (slot 2) Wx = P1Net.segment V B c (inWord X u z (slot 0) Wt) := by
    rw [paddedEq_width Wx _ _ ho2 hilen, wordAtWidth_out]
    change _ = wordAtWidth Wx (List.ofFn _) ↔ _
    rw [wordAtWidth_full, ofFn_eq_iff]
  have hu0 := inSlot_half X u z (slot 0)
  have hu1 := outSlot_half X u z (slot 1)
  have hui := inSlot_half X u z (slot 2)
  have huo := outSlot_half X u z (slot 2)
  change inSlot (_, tally 0) = t at hu0
  change outSlot (_, tally 1) = _ at hu1
  change inSlot (_, tally 2) = _ at hui
  change outSlot (_, tally 2) = _ at huo
  simp only [pathTest, header_pair, ruleCode, List.getD_cons_succ, List.getD_cons_zero, flag_tally,
    hu0, hu1, hui, huo, hs, andB, Bool.and_eq_true]
  change _ ↔ (linked → _) ∧ (if Ext.isIn V c then _ else _)
  by_cases hl : linked <;> cases hc : Ext.isIn V c <;>
    simp [hl, htie, hti, hto]

end Path

end

end P1SolFactor.SolFactor
