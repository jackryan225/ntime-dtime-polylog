import P1ProgDir.C4ProgLocalMate
import P1ProgDir.C4ProgPublic

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP Compression
open P1Net P1Wit P1ChkDir NatCode

variable {K : Type} [Fintype K] [DecidableEq K]

def countCode (r e h : ℕ) : ℕ := chainStart r e h + 2

@[fun_prop] theorem poly_countCode (r e : ℕ) : Poly (countCode r e) := by unfold countCode; fun_prop

def isPortCode (v : LocCode) : Bool := eqb v.1 2 || eqb v.1 3

@[fun_prop] theorem poly_isPortCode : Poly isPortCode := by unfold isPortCode; fun_prop

/-- Compact public parameters, the length of the witness, interval, location,
and parity of the requested base. -/
abbrev NumericBase := PublicData × ℕ × ℕ × LocCode × ℕ

def baseAddressCode (r e : ℕ) (p : NumericBase) : ℕ :=
  let h := (small p.1 1).length
  p.2.2.2.2 + 2 * (locCodeRank r e (h, p.2.2.2.1) + countCode r e h * p.2.2.1)

@[fun_prop] theorem poly_baseAddressCode (r e : ℕ) : Poly (baseAddressCode r e) := by
  unfold baseAddressCode
  fun_prop

/-- The ordinary mate uses a local or adjacent-interval rule. An owner link
always uses the twin as its ordinary value. -/
noncomputable def ordinaryViewCode (K : Type) [Fintype K] [DecidableEq K]
    (r e : ℕ) (q : NumericBase × ℕ) : SlotView :=
  let p := q.1
  let s := q.2
  let format := p.1
  let h := small format 1
  let j := p.2.2.1
  let v := p.2.2.2.1
  let t := p.2.2.2.2
  let twin : SlotView := (baseAddressCode r e (format, p.2.1, j, v, 1 - t), 0, s, 0)
  let mt := localMateCode K (h.length, v, s)
  let width := bif eqb t 0 then
    baseWidthCode K ((big format 14, big format 15, big format 16), v, s) else 0
  bif ltb s 4 then
    (bif mt.1 then
      (baseAddressCode r e (format, p.2.1, j, mt.2.1, t),
        dispCode (h, v, s) + dispCode (h, mt.2),
        mt.2.2, width)
     else bif eqb s 1 && eqb v.1 6 && ltb 0 j then
      (baseAddressCode r e (format, p.2.1, j - 1, (7, 0, 0, 0), t), 0, 1, width)
     else bif eqb s 1 && eqb v.1 7 && ltb (j + 1) (big format 0) then
      (baseAddressCode r e (format, p.2.1, j + 1, (6, 0, 0, 0), t), 0, 1, width)
     else twin)
  else twin

@[fun_prop] theorem poly_ordinaryViewCode (K : Type) [Fintype K] [DecidableEq K]
    (r e : ℕ) : Poly (ordinaryViewCode K r e) := by
  unfold ordinaryViewCode
  fun_prop

noncomputable def tapeCode (τ : K → ℕ) (j : ℕ) : ℕ :=
  (List.ofFn fun i : Fin (Fintype.card K) => τ ((kIdx K).symm i)).getD j 0

@[fun_prop] theorem poly_tapeCode (τ : K → ℕ) : Poly (tapeCode τ) := poly_table _ _

def publicReq (offset width : ℕ) (q : PublicData × ℕ × ℕ) : P1Batch.Req :=
  numericRequest (q.2.1, big q.1 offset, (small q.1 width).length, q.2.2)

@[fun_prop] theorem poly_publicReq (offset width : ℕ) : Poly (publicReq offset width) := by
  unfold publicReq
  fun_prop

noncomputable def publicPort (τ : K → ℕ) (r e : ℕ) (p : NumericBase) :
    OwnerGeometry × StartGeometry :=
  let fmt := p.1
  let h := small fmt 1
  let v := p.2.2.2.1
  let t := p.2.2.2.2
  let idx := (packNumber (big fmt 0), h)
  let count := packNumber (countCode r e h.length)
  let twin := packNumber t
  let start := (packNumber (big fmt 4), packNumber (small fmt 2).length)
  let rr := packNumber (big fmt 1)
  bif isPortCode v then
    (let opposite := bif eqb v.1 3 then 2 else 3
     let remote := locCodeRank r e (h.length, opposite, v.2.1, 0, 0)
     ((idx, count, packNumber remote, packNumber v.2.2.2, twin),
      rr, packNumber (tapeCode τ v.2.1), start))
  else ((idx, count, [], [], twin), rr, [], start)

@[fun_prop] theorem poly_packNumber : Poly packNumber := poly_born

@[fun_prop] theorem poly_publicPort (τ : K → ℕ) (r e : ℕ) : Poly (publicPort τ r e) := by
  unfold publicPort
  fun_prop

noncomputable def publicFirstReqs (τ : K → ℕ) (p : NumericBase) : List P1Batch.Req :=
  let fmt := p.1
  let m := p.2.1
  let v := p.2.2.2.1
  let j := p.2.2.1 * big fmt 1 + tapeCode τ v.2.1
  let jOwner := j * 3 + v.2.2.2
  bif isPortCode v then
    [publicReq 4 2 (fmt, m, j),
     bif eqb v.1 3 then publicReq 6 4 (fmt, m, jOwner) else publicReq 5 3 (fmt, m, jOwner)]
  else []

@[fun_prop] theorem poly_publicFirstReqs (τ : K → ℕ) : Poly (publicFirstReqs τ) := by
  unfold publicFirstReqs
  fun_prop

abbrev FieldTest := P1Batch.Req × Expectation

def publicTest (offset width : ℕ) (q : (PublicData × ℕ × ℕ) × ℕ × Bool × ℕ) : FieldTest :=
  (publicReq offset width q.1, packNumber q.2.1, q.2.2.1, packNumber q.2.2.2)

@[fun_prop] theorem poly_publicTest (offset width : ℕ) : Poly (publicTest offset width) := by
  unfold publicTest
  fun_prop

def publicWidthTest (q : (PublicData × ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ) : FieldTest :=
  let fmt := q.1.1
  let m := q.1.2.1
  let base := q.1.2.2.1
  let slot := q.1.2.2.2.1
  let ordinary := q.1.2.2.2.2.1
  let owned := q.1.2.2.2.2.2
  let i := (base * big fmt 3 + q.2) * big fmt 2 + slot
  publicTest 13 11 ((fmt, m, i), ordinary, false, owned)

@[fun_prop] theorem poly_publicWidthTest : Poly publicWidthTest := by unfold publicWidthTest; fun_prop

private def publicWidthList : (PublicData × ℕ × ℕ × ℕ × ℕ × ℕ) × List ℕ → List FieldTest :=
  polyPush publicWidthTest

@[fun_prop] private theorem poly_publicWidthList : Poly publicWidthList :=
  Poly.push (f := publicWidthTest) ((([], []), 0, 0, 0, 0, 0) : PublicData × ℕ × ℕ × ℕ × ℕ × ℕ)
    (0 : ℕ) poly_publicWidthTest

private def appendTests (q : List FieldTest × List FieldTest) : List FieldTest := q.1 ++ q.2

@[fun_prop] private theorem poly_appendTests : Poly appendTests := Easy.append.poly

noncomputable def publicSlotPlan (K : Type) [Fintype K] [DecidableEq K] (r e : ℕ)
    (q : NumericBase × ℕ) : List FieldTest :=
  let p := q.1
  let fmt := p.1
  let m := p.2.1
  let v := p.2.2.2.1
  let a := baseAddressCode r e p
  let s := q.2
  let j := a * big fmt 2 + s
  let f := ordinaryViewCode K r e q
  let active := isPortCode v && eqb s 1
  let payload := bif eqb p.2.2.2.2 0 then
    baseWidthCode K ((big fmt 14, big fmt 15, big fmt 16), v, 1) else 0
  let owned := bif active then payload else f.2.2.2
  appendTests
    ([publicTest 7 5 ((fmt, m, j), f.1, active, f.1),
      publicTest 8 6 ((fmt, m, j), f.2.1, false, f.2.1),
      publicTest 9 7 ((fmt, m, j), f.2.2.1, false, f.2.2.1),
      publicTest 10 8 ((fmt, m, j), f.1, active, f.1),
      publicTest 11 9 ((fmt, m, j), f.2.1, false, f.2.1),
      publicTest 12 10 ((fmt, m, j), f.2.2.1, false, f.2.2.1)],
      publicWidthList ((fmt, m, a, s, f.2.2.2, owned), List.range (small fmt 0).length))

@[fun_prop] theorem poly_publicSlotPlan (K : Type) [Fintype K] [DecidableEq K] (r e : ℕ) :
    Poly (publicSlotPlan K r e) := by
  unfold publicSlotPlan
  dsimp only
  refine (Poly.pair ?_ ?_).compose poly_appendTests
  · fun_prop
  · refine (Poly.pair ?_ ?_).compose poly_publicWidthList
    · fun_prop
    · have hformat : Poly (fun q : NumericBase × ℕ => q.1.1) := by fun_prop
      exact hformat.compose ((poly_small 0).compose poly_range_of_tally)

private noncomputable def numericFieldList (K : Type) [Fintype K] [DecidableEq K]
    (a r e : ℕ) (p : NumericBase) : List FieldTest :=
  (polyPush (publicSlotPlan K r e) (p, List.range (2 ^ a))).flatten

@[fun_prop] private theorem poly_numericFieldList (K : Type) [Fintype K] [DecidableEq K]
    (a r e : ℕ) : Poly (numericFieldList K a r e) := by
  have h : Poly (polyPush (publicSlotPlan K r e)) :=
    Poly.push (f := publicSlotPlan K r e) ((([], []), 0, 0, (0, 0, 0, 0), 0) : NumericBase)
      (0 : ℕ) (poly_publicSlotPlan K r e)
  have hf : Poly (fun p : NumericBase × List ℕ => (polyPush (publicSlotPlan K r e) p).flatten) :=
    h.compose Easy.flatten.poly
  have harg : Poly (fun p : NumericBase => (p, List.range (2 ^ a))) := by fun_prop
  exact harg.compose hf

noncomputable def numericPrepare (τ : K → ℕ) (a r e : ℕ) (q : PublicData × ℕ × ℕ) : ReadPlan :=
  let h := (small q.1 1).length
  let count := countCode r e h
  let j := q.2.2 / 2 / count
  let loc := locCodeOfRank r e (h, q.2.2 / 2 % count)
  let p : NumericBase := (q.1, q.2.1, j, loc, q.2.2 % 2)
  let info := publicPort τ r e p
  bif ltb j (big q.1 0) then
    (packNumber q.2.1, info.1, info.2, publicFirstReqs τ p,
      numericFieldList K a r e p)
  else (packNumber q.2.1, (([], []), [], [], [], []), ([], [], ([], [])), [], [])

theorem poly_numericPrepare (τ : K → ℕ) (a r e : ℕ) : Poly (numericPrepare τ a r e) := by
  unfold numericPrepare
  fun_prop

section Correctness

local notation "rK" => Fintype.card K
local notation "eK" => Fintype.card (Ext K)

private noncomputable def numericBase (P : C4Dims) (m : ℕ)
    (y : (Fin P.D.I × Loc K P.h) × Bool) : NumericBase :=
  (publicData P, m, y.1.1.val, encodeLoc y.1.2, y.2.toNat)

private theorem small_height (P : C4Dims) : small (publicData P) 1 = tally P.h := rfl

private theorem small_lanes (P : C4Dims) : small (publicData P) 0 = tally (2 ^ P.h) := rfl

private theorem countCode_eq (h : ℕ) : countCode rK eK h = locCount K h := (locCount_eq K h).symm

theorem baseAddressCode_eq (P : C4Dims) (m : ℕ) (y : (Fin P.D.I × Loc K P.h) × Bool) :
    baseAddressCode rK eK (numericBase P m y) = addrL y := by
  rcases y with ⟨⟨j, l⟩, t⟩
  simp only [baseAddressCode, numericBase, small_height, tally_length, countCode_eq, locCodeRank_eq]
  exact ruleAddress_eq j l t

private theorem twinAddressCode_eq (P : C4Dims) (m : ℕ) (j : Fin P.D.I) (l : Loc K P.h) (t : Bool) :
    baseAddressCode rK eK (publicData P, m, j.val, encodeLoc l, 1 - t.toNat) = addrL ((j, l), !t) := by
  have ht : 1 - t.toNat = (!t).toNat := by cases t <;> rfl
  rw [ht]
  exact baseAddressCode_eq P m ((j, l), !t)

private theorem tapeCode_eq (τ : K → ℕ) (k : K) : tapeCode τ (kIdx K k).val = τ k := by
  unfold tapeCode
  rw [getD_ofFn_valid, Equiv.symm_apply_apply]

private theorem publicPort_eq (P : C4Dims) (τ : K → ℕ) (m : ℕ)
    (y : (Fin P.D.I × Loc K P.h) × Bool) :
    publicPort τ rK eK (numericBase P m y) = packPort P.D τ y.1.2 y.2 := by
  obtain ⟨⟨j, l⟩, t⟩ := y
  have ho (k : K) : locCodeRank rK eK (P.h, 3, (kIdx K k).val, 0, 0) =
      locNum K P.h (.portOut k 0) := locCodeRank_eq (.portOut k 0)
  have hi (k : K) : locCodeRank rK eK (P.h, 2, (kIdx K k).val, 0, 0) =
      locNum K P.h (.portIn k 0) := locCodeRank_eq (.portIn k 0)
  have hb0 : big (publicData P) 0 = P.D.I := rfl
  have hb1 : big (publicData P) 1 = P.D.r := rfl
  have hb4 : big (publicData P) 4 = P.D.off secStart := rfl
  have hs2 : (small (publicData P) 2).length = P.D.width secStart := tally_length _
  cases l <;> simp [publicPort, numericBase, isPortCode, eqb, encodeLoc, packPort, packSection,
    portQuery, small_height, tally_length, countCode_eq, tapeCode_eq, ho, hi, hb0, hb1, hb4, hs2]

private theorem publicFirstReqs_eq (P : C4Dims) (τ : K → ℕ) (m : ℕ)
    (y : (Fin P.D.I × Loc K P.h) × Bool) :
    publicFirstReqs τ (numericBase P m y) = firstReqs P.D τ m y := by
  obtain ⟨⟨j, l⟩, t⟩ := y
  cases l <;> simp [publicFirstReqs, numericBase, firstReqs, portQuery, isPortCode, eqb,
    encodeLoc, startReq, ownerReq, tapeCode_eq, publicReq] <;>
    simp only [publicData, big, small, fmtBig, fmtSmall, List.getD_cons_zero, List.getD_cons_succ,
      List.map_cons, List.map_nil, tally_length, numericRequest_eq, and_self]

private theorem Bool_if_toNat (t : Bool) (width : ℕ) :
    (bif eqb t.toNat 0 then width else 0) = (if t then 0 else width) := by
  cases t <;> rfl

private theorem ordinaryViewCode_local (P : C4Dims) (m : ℕ) (j : Fin P.D.I) (l : Loc K P.h)
    (t : Bool) (s : Fin 4) (l' : Loc K P.h) (s' : Fin 4) (hm : locMate l s = some (l', s')) :
    ordinaryViewCode K rK eK (numericBase P m ((j, l), t), s.val) =
      slotView P.Wc P.Ws P.Wt ⟨0, 0, 0⟩ ((j, l), t) s.val := by
  have hm' := localMateCode_eq l s
  rw [hm] at hm'
  have hsmall : ltb s.val 4 = true := ltb_iff.mpr s.isLt
  have hAddr := baseAddressCode_eq P m ((j, l'), t)
  change baseAddressCode rK eK (publicData P, m, j.val, encodeLoc l', t.toNat) = _ at hAddr
  simp only [ordinaryViewCode, numericBase, small_height, tally_length, hm', encodeMate, mateFound,
    Bool.cond_true, hsmall, hAddr, slotView, dite_eq_left s.isLt, ruleData, mateRule, hm,
    followRule, Option.bind_some, Option.map_some, ruleAddress_eq, disp_sum_of_mate hm,
    Bool_if_toNat]
  change (_, _, _, if t then 0 else baseWidthCode K ((P.Wc, P.Ws, P.Wt), encodeLoc l, s.val)) = _
  rw [baseWidthCode_eq]

private theorem ordinaryViewCode_outside (P : C4Dims) (m : ℕ) (j : Fin P.D.I) (l : Loc K P.h)
    (t : Bool) (s : ℕ) (hs : 4 ≤ s) :
    ordinaryViewCode K rK eK (numericBase P m ((j, l), t), s) =
      slotView P.Wc P.Ws P.Wt ⟨0, 0, 0⟩ ((j, l), t) s := by
  simp only [ordinaryViewCode, numericBase, ltb_false_iff.mpr hs, Bool.cond_false,
    slotView, dite_eq_right (Nat.not_lt.mpr hs), twinAddressCode_eq]

private theorem ordinaryViewCode_none (P : C4Dims) (m : ℕ) (j : Fin P.D.I) (l : Loc K P.h)
    (t : Bool) (s : Fin 4) (hm : locMate l s = none) :
    ordinaryViewCode K rK eK (numericBase P m ((j, l), t), s.val) =
      slotView P.Wc P.Ws P.Wt ⟨0, 0, 0⟩ ((j, l), t) s.val := by
  have hsmall : ltb s.val 4 = true := ltb_iff.mpr s.isLt
  have hc := localMateCode_eq l s
  rw [hm] at hc
  simp only [ordinaryViewCode, numericBase, small_height, tally_length, hc, encodeMate, mateAbsent,
    hsmall, Bool.cond_true, Bool.cond_false, twinAddressCode_eq, slotView, dite_eq_left s.isLt, ruleData, mateRule, hm]
  have width (l : Loc K P.h) :
      (bif eqb t.toNat 0 then
        baseWidthCode K ((big (publicData P) 14, big (publicData P) 15, big (publicData P) 16),
          encodeLoc l, s.val) else 0) = (if t then 0 else baseWidth P.Wc P.Ws P.Wt l s) := by
    change (bif eqb t.toNat 0 then baseWidthCode K ((P.Wc, P.Ws, P.Wt), encodeLoc l, s.val) else 0) = _
    rw [Bool_if_toNat, baseWidthCode_eq]
  rw [width]
  by_cases hs : s = 1
  · subst s
    cases l with
    | eIn =>
      by_cases hj : 0 < j.val
      · simp only [encodeLoc, eqb, Bool.and_true, Bool.true_and, Bool.cond_true, decide_true,
          ltb_iff.mpr hj, dite_eq_left rfl, followRule, colPred, dite_eq_left hj, Option.map_some,
          Option.bind_some]
        have h := baseAddressCode_eq P m ((⟨j.val - 1, by have := j.isLt; omega⟩, (.eOut : Loc K P.h)), t)
        exact congrArg (fun a => (a, 0, 1, if t then 0 else baseWidth P.Wc P.Ws P.Wt (.eIn : Loc K P.h) 1))
          (h.trans (ruleAddress_eq _ _ _).symm)
      · simp [encodeLoc, eqb, ltb_false_iff.mpr (Nat.le_of_not_lt hj), followRule, colPred, hj]
    | eOut =>
      have he : big (publicData P) 0 = P.D.I := rfl
      by_cases hj : j.val + 1 < P.D.I
      · simp only [encodeLoc, eqb, Bool.and_true, Bool.true_and, Bool.false_and, Bool.and_false,
          Bool.cond_true, Bool.cond_false, decide_true, decide_false, he, ltb_iff.mpr hj,
          dite_eq_left rfl, followRule, colSucc, dite_eq_left hj, Option.map_some, Option.bind_some]
        have h := baseAddressCode_eq P m ((⟨j.val + 1, hj⟩, (.eIn : Loc K P.h)), t)
        exact congrArg (fun a => (a, 0, 1, if t then 0 else baseWidth P.Wc P.Ws P.Wt (.eOut : Loc K P.h) 1))
          (h.trans (ruleAddress_eq _ _ _).symm)
      · simp [encodeLoc, eqb, he, ltb_false_iff.mpr (Nat.le_of_not_lt hj), followRule, colSucc, hj]
    | _ => simp [encodeLoc, eqb, followRule, decodedOwner_zero]
  · have hs' : eqb s.val 1 = false := eqb_false_iff.mpr (fun h => hs (Fin.ext h))
    simp [hs, hs']

theorem ordinaryViewCode_eq (P : C4Dims) (m : ℕ) (y : (Fin P.D.I × Loc K P.h) × Bool) (s : ℕ) :
    ordinaryViewCode K rK eK (numericBase P m y, s) =
      slotView P.Wc P.Ws P.Wt ⟨0, 0, 0⟩ y s := by
  obtain ⟨⟨j, l⟩, t⟩ := y
  by_cases hs : s < 4
  · let slot : Fin 4 := ⟨s, hs⟩
    cases hm : locMate l slot with
    | none => exact ordinaryViewCode_none P m j l t slot hm
    | some q => exact ordinaryViewCode_local P m j l t slot q.1 q.2 hm
  · exact ordinaryViewCode_outside P m j l t s (Nat.le_of_not_lt hs)

private theorem active_eq {h : ℕ} (l : Loc K h) (s : ℕ) :
    (isPortCode (encodeLoc l) && eqb s 1) = portActive l s := by
  cases l <;> simp [isPortCode, encodeLoc, portActive, portQuery, eqb]

private theorem payload_eq (P : C4Dims) (l : Loc K P.h) (t : Bool) :
    (bif eqb t.toNat 0 then
      baseWidthCode K ((P.Wc, P.Ws, P.Wt), encodeLoc l, 1) else 0) =
      (if t then 0 else baseWidth P.Wc P.Ws P.Wt l 1) := by
  rw [Bool_if_toNat]
  exact congrArg (fun w => if t then 0 else w) (baseWidthCode_eq P.Wc P.Ws P.Wt l 1)

private theorem finRange_values (f : ℕ → List FieldTest) (n : ℕ) :
    (List.range n).flatMap f = (List.finRange n).flatMap (fun k => f k.val) := by
  have hr : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intros
      simp
  rw [← hr, List.flatMap_map] <;> rfl

private theorem map_flatten (f : ℕ → List FieldTest) (xs : List ℕ) :
    (xs.map f).flatten = xs.flatMap f := by
  induction xs <;> simp [*]

private theorem publicSlotPlan_eq (P : C4Dims) (m : ℕ)
    (y : (Fin P.D.I × Loc K P.h) × Bool) {a : ℕ} (s : Fin (2 ^ a)) :
    publicSlotPlan K rK eK (numericBase P m y, s.val) = slotPlan P.D m P.Wc P.Ws P.Wt y s := by
  unfold publicSlotPlan appendTests publicWidthList slotPlan
  simp only [baseAddressCode_eq, ordinaryViewCode_eq, small_lanes, tally_length, polyPush]
  simp only [numericBase, active_eq, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil,
    publicWidthTest, publicTest, publicReq, big, small, publicData, fmtBig, fmtSmall, tally_length,
    numericRequest_eq, sectionTest, unchangedTest, payload_eq]
  cases hp : portActive y.1.2 s.val <;> simp only [Bool.cond_false, Bool.cond_true, hp,
    Bool.false_eq_true, ↓reduceIte]

theorem numericPrepare_eq (τ : K → ℕ) (P : C4Dims) (a m i : ℕ) :
    numericPrepare τ a rK eK (publicData P, m, i) =
      prepareC4 P.D τ a P.h m P.Wc P.Ws P.Wt i := by
  cases hi : baseAt K P.D.I P.h i with
  | none =>
    have hbad : ¬ i < P.D.I * locCount K P.h * 2 := by
      unfold baseAt at hi
      split at hi
      · contradiction
      · assumption
    have hp : 0 < locCount K P.h :=
      (Nat.zero_le _).trans_lt (locNum_lt (.tabC : Loc K P.h))
    have hq : P.D.I ≤ i / 2 / locCount K P.h := by
      apply Nat.le_of_not_lt
      intro h
      have h₁ := (Nat.div_lt_iff_lt_mul hp).1 h
      have h₂ := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).1 h₁
      exact hbad h₂
    unfold numericPrepare prepareC4
    simp only [hi, small_height, tally_length, countCode_eq, show big (publicData P) 0 = P.D.I from rfl,
      ltb_false_iff.mpr hq, Bool.cond_false]
  | some y =>
    obtain ⟨⟨j, l⟩, t⟩ := y
    have haddr := baseAt_eq_some_iff.mp hi
    obtain ⟨hj, hl⟩ := addrL_split j l t
    have ht := addrL_mod_two j l t
    rw [haddr] at hj hl ht
    unfold numericPrepare prepareC4
    simp only [hi, small_height, tally_length, countCode_eq, hj, hl, ht, locCodeOfRank_eq,
      show big (publicData P) 0 = P.D.I from rfl, ltb_iff.mpr j.isLt, Bool.cond_true]
    change (packNumber m, (publicPort τ rK eK (numericBase P m ((j, l), t))).1,
      (publicPort τ rK eK (numericBase P m ((j, l), t))).2,
      publicFirstReqs τ (numericBase P m ((j, l), t)),
      (polyPush (publicSlotPlan K rK eK) (numericBase P m ((j, l), t), List.range (2 ^ a))).flatten) = _
    rw [publicPort_eq, publicFirstReqs_eq]
    apply congrArg (fun fs : List FieldTest =>
      (packNumber m, (packPort P.D τ l t).1, (packPort P.D τ l t).2, firstReqs P.D τ m ((j, l), t), fs))
    simp only [polyPush, map_flatten, finRange_values]
    exact congrArg (fun f => (List.finRange (2 ^ a)).flatMap f)
      (funext (publicSlotPlan_eq P m ((j, l), t)))

end Correctness

end P1ProgDir.SolC4
