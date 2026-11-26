import P1ProgDir.C4ProgGeometry
import P1ProgDir.C4ProgNat

namespace P1ProgDir.SolC4

open P1Net
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP Compression
open NatCode

/-- Tag, tape or table-path number, column, and type code. Tags follow the
constructor order of Loc. All four coordinates are encoded in binary. -/
abbrev LocCode := ℕ × ℕ × ℕ × ℕ

def portStart (e : ℕ) : ℕ := 1 + e

def routingStart (r e : ℕ) : ℕ := portStart e + r * 3 + r * 3

def stateStart (r e h : ℕ) : ℕ := routingStart r e + r * (2 * (h + 3)) * 8

def chainStart (r e h : ℕ) : ℕ := stateStart r e h + 2 * (h + 1) * 2

@[fun_prop] theorem poly_stateStart (r e : ℕ) : Poly (fun h => stateStart r e h) := by
  unfold stateStart routingStart portStart
  fun_prop

@[fun_prop] theorem poly_chainStart (r e : ℕ) : Poly (fun h => chainStart r e h) := by
  unfold chainStart
  fun_prop

def locCodeRank (r e : ℕ) (q : ℕ × LocCode) : ℕ :=
  let h := q.1
  let v := q.2
  bif eqb v.1 0 then 0 else
  bif eqb v.1 1 then 1 + v.2.1 else
  bif eqb v.1 2 then portStart e + (3 * v.2.1 + v.2.2.2) else
  bif eqb v.1 3 then portStart e + r * 3 + (3 * v.2.1 + v.2.2.2) else
  bif eqb v.1 4 then routingStart r e + (8 * (2 * (h + 3) * v.2.1 + v.2.2.1) + v.2.2.2) else
  bif eqb v.1 5 then stateStart r e h + (2 * v.2.2.1 + v.2.2.2) else
  bif eqb v.1 6 then chainStart r e h else chainStart r e h + 1

@[fun_prop] theorem poly_locCodeRank (r e : ℕ) : Poly (locCodeRank r e) := by
  unfold locCodeRank
  fun_prop

def locCodeOfRank (r e : ℕ) (q : ℕ × ℕ) : LocCode :=
  let h := q.1
  let j := q.2
  let p := portStart e
  let p' := p + r * 3
  let rt := routingStart r e
  let st := stateStart r e h
  let en := chainStart r e h
  bif eqb j 0 then (0, 0, 0, 0) else
  bif ltb j p then (1, j - 1, 0, 0) else
  bif ltb j p' then (2, (j - p) / 3, 0, (j - p) % 3) else
  bif ltb j rt then (3, (j - p') / 3, 0, (j - p') % 3) else
  bif ltb j st then
    let n := (j - rt) / 8
    (4, n / (2 * (h + 3)), n % (2 * (h + 3)), (j - rt) % 8) else
  bif ltb j en then (5, 0, (j - st) / 2, (j - st) % 2) else
  bif eqb j en then (6, 0, 0, 0) else (7, 0, 0, 0)

@[fun_prop] theorem poly_locCodeOfRank (r e : ℕ) : Poly (locCodeOfRank r e) := by
  unfold locCodeOfRank
  fun_prop

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

noncomputable def encodeLoc : Loc K h → LocCode
  | .tabC => (0, 0, 0, 0)
  | .tabP c => (1, extIdx K c, 0, 0)
  | .portIn k δ => (2, kIdx K k, 0, δ.val)
  | .portOut k δ => (3, kIdx K k, 0, δ.val)
  | .rt k c π => (4, kIdx K k, c.val, num3 π)
  | .st c π => (5, 0, c.val, (π 0).val)
  | .eIn => (6, 0, 0, 0)
  | .eOut => (7, 0, 0, 0)

theorem locCodeRank_eq (l : Loc K h) :
    locCodeRank (Fintype.card K) (Fintype.card (Ext K)) (h, encodeLoc l) = locNum K h l := by
  cases l <;> simp only [encodeLoc, locCodeRank, portStart, routingStart, stateStart, chainStart,
    locNum, eqb, decide_eq_false_iff_not, decide_true, Bool.cond_true, Bool.cond_false] <;> rfl

theorem locCount_eq (K : Type) [Fintype K] [DecidableEq K] (h : ℕ) :
    locCount K h = chainStart (Fintype.card K) (Fintype.card (Ext K)) h + 2 := by
  unfold chainStart stateStart routingStart portStart
  change 1 + (_ + (_ + (_ + (_ + (_ + 2))))) = _
  ring

private theorem pack_lt (w x j n : ℕ) (hx : x < w) (hj : j < n) :
    w * j + x < w * n := by
  calc
    w * j + x < w * (j + 1) := by rw [Nat.mul_succ]; exact Nat.add_lt_add_left hx _
    _ ≤ w * n := Nat.mul_le_mul_left w hj

private theorem unpack (w x j : ℕ) (hx : x < w) :
    (w * j + x) / w = j ∧ (w * j + x) % w = x := by
  rw [Nat.add_comm (w * j), Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  exact ⟨rfl, rfl⟩

theorem locCodeOfRank_eq (l : Loc K h) :
    locCodeOfRank (Fintype.card K) (Fintype.card (Ext K)) (h, locNum K h l) = encodeLoc l := by
  let r := Fintype.card K
  let e := Fintype.card (Ext K)
  let p := portStart e
  let p' := p + r * 3
  let rt := routingStart r e
  let st := stateStart r e h
  let en := chainStart r e h
  have hp : 1 ≤ p := by unfold p portStart; omega
  have hpp : p ≤ p' := Nat.le_add_right _ _
  have hpr : p' ≤ rt := by unfold p' rt routingStart p; omega
  have hrs : rt ≤ st := Nat.le_add_right _ _
  have hse : st ≤ en := Nat.le_add_right _ _
  have hzero {j : ℕ} (hj : p ≤ j) : eqb j 0 = false := eqb_false_iff.mpr (by omega)
  cases l with
  | tabC => rfl
  | tabP ext =>
    have hx := (extIdx K ext).isLt
    let v := (extIdx K ext).val
    have h₀ : eqb (1 + v) 0 = false := eqb_false_iff.mpr (by omega)
    have h₁ : ltb (1 + v) p = true := ltb_iff.mpr (by unfold p portStart; exact Nat.add_lt_add_left hx 1)
    change locCodeOfRank r e (h, 1 + v) = (1, v, 0, 0)
    dsimp only [p, p', rt, st, en] at h₀ h₁
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, Bool.cond_false, Bool.cond_true, Nat.add_sub_cancel_left]
  | portIn k δ =>
    let x := 3 * (kIdx K k).val + (δ : ℕ)
    have hx : x < r * 3 := by simpa only [Nat.mul_comm r 3] using pack_lt 3 δ (kIdx K k) r δ.isLt (kIdx K k).isLt
    have hu := unpack 3 (δ : ℕ) (kIdx K k).val δ.isLt
    have h₀ := hzero (Nat.le_add_right p x)
    have h₁ : ltb (p + x) p = false := ltb_false_iff.mpr (Nat.le_add_right _ _)
    have h₂ : ltb (p + x) p' = true := ltb_iff.mpr (Nat.add_lt_add_left hx p)
    change locCodeOfRank r e (h, p + x) = (2, (kIdx K k).val, 0, δ.val)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, Bool.cond_false, Bool.cond_true, Nat.add_sub_cancel_left,
      x, hu.1, hu.2]
  | portOut k δ =>
    let x := 3 * (kIdx K k).val + (δ : ℕ)
    have hx : x < r * 3 := by simpa only [Nat.mul_comm r 3] using pack_lt 3 δ (kIdx K k) r δ.isLt (kIdx K k).isLt
    have hu := unpack 3 (δ : ℕ) (kIdx K k).val δ.isLt
    have h₀ := hzero (show p ≤ p' + x by omega)
    have h₁ : ltb (p' + x) p = false := ltb_false_iff.mpr (by omega)
    have h₂ : ltb (p' + x) p' = false := ltb_false_iff.mpr (by omega)
    have h₃ : ltb (p' + x) rt = true := ltb_iff.mpr (by unfold rt routingStart; change p' + x < p' + r * 3; omega)
    change locCodeOfRank r e (h, p' + x) = (3, (kIdx K k).val, 0, δ.val)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂ h₃
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, h₃, Bool.cond_false, Bool.cond_true,
      Nat.add_sub_cancel_left, x, hu.1, hu.2]
  | rt k c π =>
    let w := 2 * (h + 3)
    let j := w * (kIdx K k).val + c.val
    let x := 8 * j + num3 π
    have hj : j < w * r := pack_lt w c (kIdx K k) r c.isLt (kIdx K k).isLt
    have hx : x < r * w * 8 := by
      have e := pack_lt 8 (num3 π) j (w * r) (num3_lt π) hj
      simpa only [Nat.mul_comm w r, Nat.mul_comm 8 (r * w)] using e
    have hu := unpack 8 (num3 π) j (num3_lt π)
    have hv := unpack w c.val (kIdx K k).val c.isLt
    have h₀ := hzero (show p ≤ rt + x by omega)
    have h₁ : ltb (rt + x) p = false := ltb_false_iff.mpr (by omega)
    have h₂ : ltb (rt + x) p' = false := ltb_false_iff.mpr (by omega)
    have h₃ : ltb (rt + x) rt = false := ltb_false_iff.mpr (by omega)
    have h₄ : ltb (rt + x) st = true := ltb_iff.mpr (Nat.add_lt_add_left hx rt)
    change locCodeOfRank r e (h, rt + x) = (4, (kIdx K k).val, c.val, num3 π)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂ h₃ h₄
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, h₃, h₄, Bool.cond_false,
      Bool.cond_true, Nat.add_sub_cancel_left, x, hu.1, hu.2]
    exact congrArg₂ (fun k c : ℕ => (4, k, c, num3 π)) hv.1 hv.2
  | st c π =>
    have hπ : (π 0).val < 2 := ZMod.val_lt _
    let x := 2 * c.val + (π 0).val
    have hx : x < 2 * (h + 1) * 2 := by
      have e := pack_lt 2 (π 0).val c.val (2 * (h + 1)) hπ c.isLt
      simpa only [Nat.mul_comm 2 (2 * (h + 1))] using e
    have hu := unpack 2 (π 0).val c.val hπ
    have h₀ := hzero (show p ≤ st + x by omega)
    have h₁ : ltb (st + x) p = false := ltb_false_iff.mpr (by omega)
    have h₂ : ltb (st + x) p' = false := ltb_false_iff.mpr (by omega)
    have h₃ : ltb (st + x) rt = false := ltb_false_iff.mpr (by omega)
    have h₄ : ltb (st + x) st = false := ltb_false_iff.mpr (by omega)
    have h₅ : ltb (st + x) en = true := ltb_iff.mpr (Nat.add_lt_add_left hx st)
    change locCodeOfRank r e (h, st + x) = (5, 0, c.val, (π 0).val)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂ h₃ h₄ h₅
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, h₃, h₄, h₅, Bool.cond_false,
      Bool.cond_true, Nat.add_sub_cancel_left, x, hu.1, hu.2]
  | eIn =>
    have h₀ := hzero (show p ≤ en by omega)
    have h₁ : ltb en p = false := ltb_false_iff.mpr (by omega)
    have h₂ : ltb en p' = false := ltb_false_iff.mpr (by omega)
    have h₃ : ltb en rt = false := ltb_false_iff.mpr (by omega)
    have h₄ : ltb en st = false := ltb_false_iff.mpr (by omega)
    have h₅ : ltb en en = false := ltb_false_iff.mpr le_rfl
    have h₆ : eqb en en = true := eqb_iff.mpr rfl
    change locCodeOfRank r e (h, en) = (6, 0, 0, 0)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, h₃, h₄, h₅, h₆,
      Bool.cond_false, Bool.cond_true]
  | eOut =>
    have h₀ := hzero (show p ≤ en + 1 by omega)
    have h₁ : ltb (en + 1) p = false := ltb_false_iff.mpr (by omega)
    have h₂ : ltb (en + 1) p' = false := ltb_false_iff.mpr (by omega)
    have h₃ : ltb (en + 1) rt = false := ltb_false_iff.mpr (by omega)
    have h₄ : ltb (en + 1) st = false := ltb_false_iff.mpr (by omega)
    have h₅ : ltb (en + 1) en = false := ltb_false_iff.mpr (by omega)
    have h₆ : eqb (en + 1) en = false := eqb_false_iff.mpr (by omega)
    change locCodeOfRank r e (h, en + 1) = (7, 0, 0, 0)
    dsimp only [p, p', rt, st, en] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
    simp only [locCodeOfRank, p, p', rt, st, en, h₀, h₁, h₂, h₃, h₄, h₅, h₆,
      Bool.cond_false]

end P1ProgDir.SolC4
