import P1ProgDir.C4ProgFlip

namespace P1ProgDir.SolC4

open P1Net NatCode
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K]

abbrev ExtCode := ℕ × ℕ × ℕ
abbrev MateCode := Bool × LocCode × ℕ

noncomputable def encodeExt : Ext K → ExtCode
  | .stIn => (0, 0, 0)
  | .stOut => (1, 0, 0)
  | .cIn k δ => (2, kIdx K k, δ)
  | .cOut k δ => (3, kIdx K k, δ)

private noncomputable def extTable (K : Type) [Fintype K] [DecidableEq K] : List ExtCode :=
  List.ofFn fun j : Fin (Fintype.card (Ext K)) => encodeExt ((extIdx K).symm j)

noncomputable def extCodeAt (K : Type) [Fintype K] [DecidableEq K] (j : ℕ) : ExtCode :=
  (((extTable K).map Prod.fst).getD j 0,
   ((extTable K).map (fun p => p.2.1)).getD j 0,
   ((extTable K).map (fun p => p.2.2)).getD j 0)

@[fun_prop] theorem poly_extCodeAt (K : Type) [Fintype K] [DecidableEq K] : Poly (extCodeAt K) :=
  (poly_table _ _).pair ((poly_table _ _).pair (poly_table _ _))

theorem getD_ofFn_valid {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i.val d = f i := by
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

theorem extCodeAt_eq (e : Ext K) : extCodeAt K (extIdx K e).val = encodeExt e := by
  rcases h : encodeExt e with ⟨tag, tape, δ⟩
  simp only [extCodeAt, extTable, List.map_ofFn, Function.comp_def, getD_ofFn_valid,
    Equiv.symm_apply_apply, h]

private noncomputable def tablePortIndex (K : Type) [Fintype K] [DecidableEq K] (input : Bool) : List ℕ :=
  List.ofFn fun j : Fin (Fintype.card K * 3) =>
    let (k, δ) := (kpEquiv K).symm j
    (extIdx K (if input then Ext.cIn k δ else Ext.cOut k δ)).val

noncomputable def extPortIndex (K : Type) [Fintype K] [DecidableEq K] (input : Bool) (q : ℕ × ℕ) : ℕ :=
  (tablePortIndex K input).getD (q.2 + 3 * q.1) 0

@[fun_prop] theorem poly_extPortIndex (K : Type) [Fintype K] [DecidableEq K] (input : Bool) :
    Poly (extPortIndex K input) := by
  have h : Poly (fun q : ℕ × ℕ => q.2 + 3 * q.1) := by fun_prop
  exact h.compose (poly_table 0 (tablePortIndex K input))

theorem extPortIndex_eq (input : Bool) (k : K) (δ : Fin 3) :
    extPortIndex K input ((kIdx K k).val, δ.val) =
      (extIdx K (if input then Ext.cIn k δ else Ext.cOut k δ)).val := by
  unfold extPortIndex tablePortIndex
  dsimp only
  rw [← kpEquiv_val K k δ, getD_ofFn_valid, Equiv.symm_apply_apply]

def mateFound (q : LocCode × ℕ) : MateCode := (true, q)

def mateAbsent : MateCode := (false, (0, 0, 0, 0), 0)

@[fun_prop] theorem poly_mateFound : Poly mateFound := by unfold mateFound; fun_prop

def attachCode (q : ℕ × ExtCode) : MateCode :=
  let h := q.1
  let ext := q.2
  bif eqb ext.1 0 then mateFound ((5, 0, 2 * (h + 1) - 1, 1), 0) else
  bif eqb ext.1 1 then mateFound ((5, 0, 0, 1), 2) else
  bif eqb ext.1 2 then mateFound ((4, ext.2.1, 2 * (h + 3) - 1, 3 + ext.2.2), 0) else
    mateFound ((4, ext.2.1, 0, 3 + ext.2.2), 2)

@[fun_prop] theorem poly_attachCode : Poly attachCode := by unfold attachCode; fun_prop

noncomputable def externalMateCode (K : Type) [Fintype K] [DecidableEq K] (q : ℕ × ℕ × ℕ) : MateCode :=
  let t := q.2.1
  let s := q.2.2
  bif eqb s 0 then
    (bif eqb t 0 then mateFound ((0, 0, 0, 0), 0) else mateFound ((1, t - 1, 0, 0), 1)) else
  bif eqb s 1 then
    (bif ltb (t + 1) (Fintype.card (Ext K)) then mateFound ((1, t + 1, 0, 0), 0) else mateAbsent) else
  bif eqb s 2 then attachCode (q.1, extCodeAt K t) else mateAbsent

@[fun_prop] theorem poly_externalMateCode (K : Type) [Fintype K] [DecidableEq K] : Poly (externalMateCode K) := by
  unfold externalMateCode
  fun_prop

noncomputable def rtEndCode (K : Type) [Fintype K] [DecidableEq K] (atLast : Bool) (q : ℕ × ℕ) : MateCode :=
  bif ltb q.2 3 then
    mateFound ((bif atLast then 3 else 2, q.1, 0, q.2), 0) else
  bif ltb q.2 6 then mateFound ((1, extPortIndex K atLast (q.1, q.2 - 3), 0, 0), 2) else mateAbsent

@[fun_prop] theorem poly_rtEndCode (K : Type) [Fintype K] [DecidableEq K] (atLast : Bool) :
    Poly (rtEndCode K atLast) := by
  unfold rtEndCode
  fun_prop

noncomputable def stEndCode (K : Type) [Fintype K] [DecidableEq K] (atLast : Bool) (p : ℕ) : MateCode :=
  bif eqb p 0 then mateFound ((bif atLast then 7 else 6, 0, 0, 0), 0) else
    mateFound ((1, (extIdx K (if atLast then Ext.stIn else Ext.stOut)).val, 0, 0), 2)

@[fun_prop] theorem poly_stEndCode (K : Type) [Fintype K] [DecidableEq K] (atLast : Bool) :
    Poly (stEndCode K atLast) := by
  unfold stEndCode
  fun_prop

noncomputable def routingMateCode (K : Type) [Fintype K] [DecidableEq K] (q : ℕ × LocCode × ℕ) : MateCode :=
  let h := q.1
  let v := q.2.1
  let s := q.2.2
  let tag := v.1
  let k := v.2.1
  let c := v.2.2.1
  let p := v.2.2.2
  let cnext := c + 1
  let cprev := c - 1
  let hasNext := ltb cnext (2 * (h + 3))
  let hasPrev := ltb 0 c
  bif eqb s 0 then (bif hasNext then mateFound ((tag, k, cnext, p), 2) else rtEndCode K true (k, p)) else
  bif eqb s 1 then (bif hasNext then mateFound ((tag, k, cnext, rtTypeNumber (h, c, p)), 3) else mateAbsent) else
  bif eqb s 2 then (bif hasPrev then mateFound ((tag, k, cprev, p), 0) else rtEndCode K false (k, p)) else
    (bif hasPrev then mateFound ((tag, k, cprev, rtTypeNumber (h, cprev, p)), 1) else mateAbsent)

@[fun_prop] theorem poly_routingMateCode (K : Type) [Fintype K] [DecidableEq K] : Poly (routingMateCode K) := by
  unfold routingMateCode
  fun_prop

noncomputable def stateMateCode (K : Type) [Fintype K] [DecidableEq K] (q : ℕ × LocCode × ℕ) : MateCode :=
  let h := q.1
  let v := q.2.1
  let s := q.2.2
  let tag := v.1
  let k := v.2.1
  let c := v.2.2.1
  let p := v.2.2.2
  let cnext := c + 1
  let cprev := c - 1
  let hasNext := ltb cnext (2 * (h + 1))
  let hasPrev := ltb 0 c
  bif eqb s 0 then (bif hasNext then mateFound ((tag, k, cnext, p), 2) else stEndCode K true p) else
  bif eqb s 1 then (bif hasNext then mateFound ((tag, k, cnext, stTypeNumber (h, c, p)), 3) else mateAbsent) else
  bif eqb s 2 then (bif hasPrev then mateFound ((tag, k, cprev, p), 0) else stEndCode K false p) else
    (bif hasPrev then mateFound ((tag, k, cprev, stTypeNumber (h, cprev, p)), 1) else mateAbsent)

@[fun_prop] theorem poly_stateMateCode (K : Type) [Fintype K] [DecidableEq K] : Poly (stateMateCode K) := by
  unfold stateMateCode
  fun_prop

noncomputable def localMateCode (K : Type) [Fintype K] [DecidableEq K] (q : ℕ × LocCode × ℕ) : MateCode :=
  let h := q.1
  let v := q.2.1
  let s := q.2.2
  bif eqb v.1 0 then (bif eqb s 0 then mateFound ((1, 0, 0, 0), 0) else mateAbsent) else
  bif eqb v.1 1 then externalMateCode K (h, v.2.1, s) else
  bif eqb v.1 2 then (bif eqb s 0 then mateFound ((4, v.2.1, 0, v.2.2.2), 2) else mateAbsent) else
  bif eqb v.1 3 then (bif eqb s 0 then mateFound ((4, v.2.1, 2 * (h + 3) - 1, v.2.2.2), 0) else mateAbsent) else
  bif eqb v.1 4 then routingMateCode K q else
  bif eqb v.1 5 then stateMateCode K q else
  bif eqb v.1 6 then (bif eqb s 0 then mateFound ((5, 0, 0, 0), 2) else mateAbsent) else
    (bif eqb s 0 then mateFound ((5, 0, 2 * (h + 1) - 1, 0), 0) else mateAbsent)

@[fun_prop] theorem poly_localMateCode (K : Type) [Fintype K] [DecidableEq K] : Poly (localMateCode K) := by
  unfold localMateCode
  fun_prop

noncomputable def encodeMate {h : ℕ} : Option (Loc K h × Fin 4) → MateCode
  | none => mateAbsent
  | some (l, s) => mateFound (encodeLoc l, s.val)

theorem attachCode_eq (h : ℕ) (ext : Ext K) :
    attachCode (h, encodeExt ext) = encodeMate (some (extAttach (h := h) ext)) := by
  cases ext <;> simp only [attachCode, encodeExt, encodeMate, extAttach, encodeLoc, eqb, decide_true,
    Bool.cond_true, Bool.cond_false, code1, Fin.val_mk, num3_code3_add] <;> rfl

private theorem extPortIndex_eq_of_lt (input : Bool) (k : K) {m : ℕ} (hm : m < 3) :
    extPortIndex K input ((kIdx K k).val, m) =
      (extIdx K (if input then Ext.cIn k ⟨m, hm⟩ else Ext.cOut k ⟨m, hm⟩)).val :=
  extPortIndex_eq input k ⟨m, hm⟩

theorem rtEndCode_eq (h : ℕ) (atLast : Bool) (k : K) (π : BitWord 3) :
    rtEndCode K atLast ((kIdx K k).val, num3 π) =
      encodeMate (h := h) (bif atLast then rtDst k π else rtSrc k π) := by
  by_cases h3 : num3 π < 3
  · cases atLast <;> simp only [rtEndCode, ltb_iff.mpr h3, Bool.cond_true, Bool.cond_false,
      rtDst, rtSrc, dite_eq_left h3, encodeMate, encodeLoc] <;> rfl
  · by_cases h6 : num3 π < 6
    · have hm : num3 π - 3 < 3 := by omega
      cases atLast <;> simp only [rtEndCode, ltb_false_iff.mpr (Nat.le_of_not_lt h3), ltb_iff.mpr h6,
        Bool.cond_false, Bool.cond_true, rtDst, rtSrc, dite_eq_right h3, dite_eq_left h6,
        encodeMate, encodeLoc, extPortIndex_eq_of_lt _ k hm] <;> rfl
    · cases atLast <;> simp only [rtEndCode, ltb_false_iff.mpr (Nat.le_of_not_lt h3),
        ltb_false_iff.mpr (Nat.le_of_not_lt h6), Bool.cond_false, Bool.cond_true, rtDst, rtSrc,
        dite_eq_right h3, dite_eq_right h6, encodeMate]

theorem stEndCode_eq (h : ℕ) (atLast : Bool) (π : BitWord 1) :
    stEndCode K atLast (π 0).val =
      encodeMate (h := h) (some (bif atLast then stDst (K := K) π else stSrc π)) := by
  rcases code1_cases π with rfl | rfl <;> cases atLast <;>
    simp only [stEndCode, code1, Bool.cond_false, Bool.cond_true, eqb, decide_true,
      stDst, stSrc, code1_true_ne, ite_eq_left rfl, encodeMate, encodeLoc] <;> rfl

theorem routingMateCode_eq (h : ℕ) (k : K) (c : Fin (2 * (h + 3))) (π : BitWord 3) (s : Fin 4) :
    routingMateCode K (h, encodeLoc (.rt k c π), s.val) = encodeMate (locMate (.rt k c π) s) := by
  have hh₁ (hs : c.val + 1 < 2 * (h + 3)) :
      colSucc c = some ⟨c.val + 1, hs⟩ := by simp only [colSucc, dite_eq_left hs]
  have hh₀ (hs : ¬ c.val + 1 < 2 * (h + 3)) : colSucc c = none := by simp only [colSucc, dite_eq_right hs]
  have hp₁ (hs : 0 < c.val) :
      colPred c = some ⟨c.val - 1, by have := c.isLt; omega⟩ := by simp only [colPred, dite_eq_left hs]
  have hp₀ (hs : ¬ 0 < c.val) : colPred c = none := by simp only [colPred, dite_eq_right hs]
  fin_cases s
  · by_cases hs : c.val + 1 < 2 * (h + 3)
    · simp only [routingMateCode, encodeLoc, locMate, hh₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, encodeMate] <;> rfl
    · simp only [routingMateCode, encodeLoc, locMate, hh₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb]
      change rtEndCode K true ((kIdx K k).val, num3 π) = encodeMate (rtDst k π)
      exact rtEndCode_eq h true k π
  · by_cases hs : c.val + 1 < 2 * (h + 3)
    · simp only [routingMateCode, encodeLoc, locMate, hh₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, Option.map_some, encodeMate, rtTypeNumber_eq] <;> rfl
    · simp only [routingMateCode, encodeLoc, locMate, hh₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb,
        Bool.cond_true, Bool.cond_false, Option.map_none, encodeMate] <;> rfl
  · by_cases hs : 0 < c.val
    · simp only [routingMateCode, encodeLoc, locMate, hp₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, encodeMate] <;> rfl
    · simp only [routingMateCode, encodeLoc, locMate, hp₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb]
      change rtEndCode K false ((kIdx K k).val, num3 π) = encodeMate (rtSrc k π)
      exact rtEndCode_eq h false k π
  · by_cases hs : 0 < c.val
    · simp only [routingMateCode, encodeLoc, locMate, hp₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, Option.map_some, encodeMate, rtTypeNumber_eq] <;> rfl
    · simp only [routingMateCode, encodeLoc, locMate, hp₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb,
        Bool.cond_true, Bool.cond_false, Option.map_none, encodeMate] <;> rfl

theorem stateMateCode_eq (h : ℕ) (c : Fin (2 * (h + 1))) (π : BitWord 1) (s : Fin 4) :
    stateMateCode K (h, encodeLoc (.st (K := K) c π), s.val) = encodeMate (locMate (.st (K := K) c π) s) := by
  have hh₁ (hs : c.val + 1 < 2 * (h + 1)) :
      colSucc c = some ⟨c.val + 1, hs⟩ := by simp only [colSucc, dite_eq_left hs]
  have hh₀ (hs : ¬ c.val + 1 < 2 * (h + 1)) : colSucc c = none := by simp only [colSucc, dite_eq_right hs]
  have hp₁ (hs : 0 < c.val) :
      colPred c = some ⟨c.val - 1, by have := c.isLt; omega⟩ := by simp only [colPred, dite_eq_left hs]
  have hp₀ (hs : ¬ 0 < c.val) : colPred c = none := by simp only [colPred, dite_eq_right hs]
  fin_cases s
  · by_cases hs : c.val + 1 < 2 * (h + 1)
    · simp only [stateMateCode, encodeLoc, locMate, hh₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, encodeMate] <;> rfl
    · simp only [stateMateCode, encodeLoc, locMate, hh₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb]
      change stEndCode K true (π 0).val = encodeMate (some (stDst (K := K) π))
      exact stEndCode_eq (K := K) h true π
  · by_cases hs : c.val + 1 < 2 * (h + 1)
    · simp only [stateMateCode, encodeLoc, locMate, hh₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, Option.map_some, encodeMate, stTypeNumber_eq] <;> rfl
    · simp only [stateMateCode, encodeLoc, locMate, hh₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb,
        Bool.cond_true, Bool.cond_false, Option.map_none, encodeMate] <;> rfl
  · by_cases hs : 0 < c.val
    · simp only [stateMateCode, encodeLoc, locMate, hp₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, encodeMate] <;> rfl
    · simp only [stateMateCode, encodeLoc, locMate, hp₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb]
      change stEndCode K false (π 0).val = encodeMate (some (stSrc (K := K) π))
      exact stEndCode_eq (K := K) h false π
  · by_cases hs : 0 < c.val
    · simp only [stateMateCode, encodeLoc, locMate, hp₁ hs, ltb_iff.mpr hs, eqb,
        Bool.cond_true, Bool.cond_false, Option.map_some, encodeMate, stTypeNumber_eq] <;> rfl
    · simp only [stateMateCode, encodeLoc, locMate, hp₀ hs, ltb_false_iff.mpr (Nat.le_of_not_lt hs), eqb,
        Bool.cond_true, Bool.cond_false, Option.map_none, encodeMate] <;> rfl


theorem externalMateCode_eq (h : ℕ) (e : Ext K) (s : Fin 4) :
    externalMateCode K (h, (extIdx K e).val, s.val) =
      encodeMate (locMate (.tabP (h := h) e) s) := by
  let t := (extIdx K e).val
  fin_cases s
  · by_cases ht : 0 < t
    · simp [externalMateCode, locMate, prevExt, ht, t, eqb_false_iff.mpr (show t ≠ 0 by omega),
        encodeMate, encodeLoc]
    · have ht' : t = 0 := by omega
      simp [externalMateCode, locMate, prevExt, ht, eqb_iff.mpr ht', encodeMate, encodeLoc, t]
  · by_cases ht : t + 1 < Fintype.card (Ext K)
    · simp [externalMateCode, locMate, nextExt, ht, ltb_iff.mpr ht, encodeMate, encodeLoc, t]
    · simp [externalMateCode, locMate, nextExt, ht, ltb_false_iff.mpr (Nat.le_of_not_lt ht),
        encodeMate, t]
  · simpa [externalMateCode, locMate, t, extCodeAt_eq] using attachCode_eq h e
  · simp [externalMateCode, locMate, encodeMate]

theorem localMateCode_eq {h : ℕ} (l : Loc K h) (s : Fin 4) :
    localMateCode K (h, encodeLoc l, s.val) = encodeMate (locMate l s) := by
  cases l with
  | tabP ext => simpa [localMateCode, encodeLoc, eqb] using externalMateCode_eq h ext s
  | rt k c π => simpa [localMateCode, encodeLoc, eqb] using routingMateCode_eq h k c π s
  | st c π => simpa [localMateCode, encodeLoc, eqb] using stateMateCode_eq (K := K) h c π s
  | tabC =>
    fin_cases s <;> simp [localMateCode, encodeLoc, locMate, encodeMate, firstExt, eqb] <;> rfl
  | portIn k δ =>
    fin_cases s <;> simp [localMateCode, encodeLoc, locMate, encodeMate, num3_code3_fin, eqb, rcol0] <;> rfl
  | portOut k δ =>
    fin_cases s <;> simp [localMateCode, encodeLoc, locMate, encodeMate, num3_code3_fin, eqb, rcolLast] <;> rfl
  | eIn =>
    fin_cases s <;> simp [localMateCode, encodeLoc, locMate, encodeMate, code1, eqb, scol0] <;> rfl
  | eOut =>
    fin_cases s <;> simp [localMateCode, encodeLoc, locMate, encodeMate, code1, eqb, scolLast] <;> rfl

/-- Width for each outgoing payload in the local pre-network. -/
noncomputable def baseWidthCode (K : Type) [Fintype K] [DecidableEq K]
    (q : (ℕ × ℕ × ℕ) × LocCode × ℕ) : ℕ :=
  let wc := q.1.1
  let ws := q.1.2.1
  let wt := q.1.2.2
  let tag := q.2.1.1
  let s := q.2.2
  bif eqb tag 0 then (bif eqb s 0 then wt else 0) else
  bif eqb tag 1 then
    (bif eqb s 1 then wt else
     bif eqb s 2 then
       (let e := extCodeAt K q.2.1.2.1
        bif eqb e.1 1 then ws else bif eqb e.1 3 then wc else 0)
     else 0) else
  bif eqb tag 2 then (bif eqb s 0 then wc else 0) else
  bif eqb tag 3 then (bif eqb s 1 then wc else 0) else
  bif eqb tag 4 then (bif ltb s 2 then wc else 0) else
  bif eqb tag 5 then (bif ltb s 2 then ws else 0) else
  bif eqb tag 6 then (bif eqb s 0 then ws else 0) else
    (bif eqb s 1 then ws else 0)

@[fun_prop] theorem poly_baseWidthCode (K : Type) [Fintype K] [DecidableEq K] : Poly (baseWidthCode K) := by
  unfold baseWidthCode
  fun_prop

theorem baseWidthCode_eq {h : ℕ} (wc ws wt : ℕ) (l : Loc K h) (s : Fin 4) :
    baseWidthCode K ((wc, ws, wt), encodeLoc l, s.val) = baseWidth wc ws wt l s := by
  cases l with
  | tabP ext =>
    fin_cases s <;> cases ext <;>
      simp [baseWidthCode, encodeLoc, baseWidth, extCodeAt_eq, encodeExt, eqb]
  | _ => fin_cases s <;> simp [baseWidthCode, encodeLoc, baseWidth, eqb, ltb]

def dispCode (q : Tally × LocCode × ℕ) : ℕ :=
  let tag := q.2.1.1
  let col := q.2.1.2.2.1
  bif eqb q.2.2 1 then
    (bif eqb tag 4 then laneFlipNumber 3 (q.1, col) else
     bif eqb tag 5 then laneFlipNumber 1 (q.1, col) else 0)
  else 0

@[fun_prop] theorem poly_dispCode : Poly dispCode := by unfold dispCode; fun_prop

theorem dispCode_eq {h : ℕ} (l : Loc K h) (s : Fin 4) :
    dispCode (tally h, encodeLoc l, s.val) = P1ChkDir.bwNum (disp1 1 ((0, l), s)) := by
  cases l <;> fin_cases s <;> simp [dispCode, disp1, eqb, encodeLoc, bwNum_zero, laneFlipNumber_eq]

theorem localMate_slot_one {h : ℕ} (l l' : Loc K h) (s : Fin 4)
    (hm : locMate l 1 = some (l', s)) : s ≠ 1 := by
  cases l with
  | tabP ext =>
    cases he : nextExt ext <;> simp [locMate, he] at hm
    have hs : s = 0 := hm.2.symm
    rw [hs]
    decide
  | rt k c π =>
    cases he : colSucc c <;> simp [locMate, he] at hm
    have hs : s = 3 := hm.2.symm
    rw [hs]
    decide
  | st c π =>
    cases he : colSucc c <;> simp [locMate, he] at hm
    have hs : s = 3 := hm.2.symm
    rw [hs]
    decide
  | _ => simp [locMate] at hm

theorem disp_sum_of_mate {h : ℕ} {l l' : Loc K h} {s s' : Fin 4}
    (hm : locMate l s = some (l', s')) :
    P1ChkDir.bwNum (disp1 1 ((0, l), s) + disp1 1 ((0, l'), s')) =
      dispCode (tally h, encodeLoc l, s.val) + dispCode (tally h, encodeLoc l', s'.val) := by
  rw [dispCode_eq, dispCode_eq]
  have hz (v : Loc K h) (j : Fin 4) (hn : j ≠ 1) : disp1 1 ((0, v), j) = 0 := by
    cases v <;> simp [disp1, hn]
  by_cases hs : s = 1
  · subst s
    rw [hz _ _ (localMate_slot_one _ _ _ hm), add_zero, bwNum_zero, Nat.add_zero]
  · rw [hz _ _ hs, zero_add, bwNum_zero, Nat.zero_add]

end P1ProgDir.SolC4
