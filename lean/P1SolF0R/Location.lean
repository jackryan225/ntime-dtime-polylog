import P1SolF0R.Position
import P1ChkDir.C4
import P1ChkFinal.C10RcPoly
import P1SolC10P.Primitives

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open scoped P1ChkFinal.AstraC10

/-- The location tag, tape or path index, column or port number, and type number. -/
abbrev LocationCode := ℕ × ℕ × ℕ × ℕ

/-- External-location count, tape count, lane bit width, and numeric location. -/
abbrev LocationArgs := (ℕ × ℕ × ℕ) × ℕ

def decodeLocation (p : LocationArgs) : LocationCode :=
  let E := p.1.1
  let r := p.1.2.1
  let h := p.1.2.2
  let l := p.2
  let R := 2 * (h + 3)
  let S := 2 * (h + 1)
  let pin := 1 + E
  let pout := pin + r * 3
  let rt := pout + r * 3
  let st := rt + r * R * 8
  let ein := st + S * 2
  bif decide (l = 0) then (0, 0, 0, 0)
  else bif decide (l < pin) then (1, l - 1, 0, 0)
  else bif decide (l < pout) then (2, (l - pin) / 3, (l - pin) % 3, 0)
  else bif decide (l < rt) then (3, (l - pout) / 3, (l - pout) % 3, 0)
  else bif decide (l < st) then (4, (l - rt) / 8 / R, (l - rt) / 8 % R, (l - rt) % 8)
  else bif decide (l < ein) then (5, 0, (l - st) / 2, (l - st) % 2)
  else bif decide (l = ein) then (6, 0, 0, 0)
  else (7, 0, 0, 0)

set_option maxHeartbeats 800000 in
theorem decodeLocation_poly : Poly decodeLocation := by
  unfold decodeLocation
  fun_prop

noncomputable def locCode {K : Type} [Fintype K] [DecidableEq K] {h : ℕ} :
    Loc K h → LocationCode
  | .tabC => (0, 0, 0, 0)
  | .tabP c => (1, (extIdx K c).val, 0, 0)
  | .portIn k d => (2, (kIdx K k).val, d.val, 0)
  | .portOut k d => (3, (kIdx K k).val, d.val, 0)
  | .rt k j t => (4, (kIdx K k).val, j.val, num3 t)
  | .st j t => (5, 0, j.val, (t 0).val)
  | .eIn => (6, 0, 0, 0)
  | .eOut => (7, 0, 0, 0)

private theorem divmod_mul_add (b k d : ℕ) (hb : 0 < b) (hd : d < b) :
    (b * k + d) / b = k ∧ (b * k + d) % b = d := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hd, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  exact ⟨rfl, rfl⟩

theorem decodeLocation_eq {K : Type} [Fintype K] [DecidableEq K] {h : ℕ} (l : Loc K h) :
    decodeLocation ((Fintype.card (Ext K), Fintype.card K, h), locNum K h l) = locCode l := by
  let E := Fintype.card (Ext K)
  let r := Fintype.card K
  let R := 2 * (h + 3)
  let S := 2 * (h + 1)
  let pin := 1 + E
  let pout := pin + r * 3
  let rt := pout + r * 3
  let st := rt + r * R * 8
  let ein := st + S * 2
  cases l with
  | tabC => rfl
  | tabP c =>
    have hc := (extIdx K c).isLt
    have h1 : 1 + (extIdx K c).val ≠ 0 := by omega
    have h2 : 1 + (extIdx K c).val < 1 + E := by omega
    dsimp only [E] at h2
    simp only [decodeLocation, locNum, locCode, h1, h2, decide_false, decide_true, Bool.cond_false,
      Bool.cond_true, Nat.add_sub_cancel_left]
  | portIn k d =>
    let j := (kIdx K k).val
    have hj : j < r := (kIdx K k).isLt
    have hd := d.isLt
    let n := pin + (3 * j + d.val)
    have h1 : n ≠ 0 := by dsimp [n, pin]; omega
    have h2 : ¬ n < pin := by dsimp [n]; omega
    have h3 : n < pout := by dsimp [n, pout]; omega
    have hn : n - pin = 3 * j + d.val := by simp only [n, Nat.add_sub_cancel_left]
    obtain ⟨hq, hm⟩ := divmod_mul_add 3 j d.val (by decide) hd
    change decodeLocation ((E, r, h), n) = (2, j, d.val, 0)
    dsimp only [pin, pout] at h2 h3 hn
    simp only [decodeLocation, h1, h2, h3, decide_false, decide_true, Bool.cond_false, Bool.cond_true,
      hn, hq, hm]
  | portOut k d =>
    let j := (kIdx K k).val
    have hj : j < r := (kIdx K k).isLt
    have hd := d.isLt
    let n := pout + (3 * j + d.val)
    have h1 : n ≠ 0 := by dsimp [n, pout, pin]; omega
    have h2 : ¬ n < pin := by dsimp [n, pout]; omega
    have h3 : ¬ n < pout := by dsimp [n]; omega
    have h4 : n < rt := by dsimp [n, rt]; omega
    have hn : n - pout = 3 * j + d.val := by simp only [n, Nat.add_sub_cancel_left]
    obtain ⟨hq, hm⟩ := divmod_mul_add 3 j d.val (by decide) hd
    change decodeLocation ((E, r, h), n) = (3, j, d.val, 0)
    dsimp only [pin, pout, rt] at h2 h3 h4 hn
    simp only [decodeLocation, h1, h2, h3, h4, decide_false, decide_true,
      Bool.cond_false, Bool.cond_true, hn, hq, hm]
  | rt k c t =>
    let j := (kIdx K k).val
    have hj : j < r := (kIdx K k).isLt
    have hc : c.val < R := c.isLt
    have ht := num3_lt t
    let row := R * j + c.val
    have hr : row < r * R := by
      calc
        row < R * j + R := Nat.add_lt_add_left hc _
        _ = R * (j + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ R * r := Nat.mul_le_mul_left R hj
        _ = r * R := Nat.mul_comm _ _
    let n := rt + (8 * row + num3 t)
    have h1 : n ≠ 0 := by dsimp [n, rt, pout, pin]; omega
    have h2 : ¬ n < pin := by dsimp [n, rt, pout]; omega
    have h3 : ¬ n < pout := by dsimp [n, rt]; omega
    have h4 : ¬ n < rt := by dsimp [n]; omega
    have h5 : n < st := by dsimp [n, st]; omega
    have hn : n - rt = 8 * row + num3 t := by simp only [n, Nat.add_sub_cancel_left]
    obtain ⟨hq, hm⟩ := divmod_mul_add 8 row (num3 t) (by decide) ht
    have hdivmod : row / R = j ∧ row % R = c.val :=
      divmod_mul_add R j c.val (by dsimp [R]; omega) hc
    obtain ⟨hq', hm'⟩ := hdivmod
    change decodeLocation ((E, r, h), n) = (4, j, c.val, num3 t)
    dsimp only [pin, pout, rt, R, st] at h2 h3 h4 h5 hn hq' hm'
    simp only [decodeLocation, h1, h2, h3, h4, h5, decide_false, decide_true,
      Bool.cond_false, Bool.cond_true, hn, hq, hm, hq', hm']
  | st c t =>
    have hc : c.val < S := c.isLt
    have ht : (t 0).val < 2 := (show Fin 2 from t 0).isLt
    let n := st + (2 * c.val + (t 0).val)
    have h1 : n ≠ 0 := by dsimp [n, st, rt, pout, pin]; omega
    have h2 : ¬ n < pin := by dsimp [n, st, rt, pout]; omega
    have h3 : ¬ n < pout := by dsimp [n, st, rt]; omega
    have h4 : ¬ n < rt := by dsimp [n, st]; omega
    have h5 : ¬ n < st := by dsimp [n]; omega
    have h6 : n < ein := by dsimp [n, ein]; omega
    have hn : n - st = 2 * c.val + (t 0).val := by simp only [n, Nat.add_sub_cancel_left]
    obtain ⟨hq, hm⟩ := divmod_mul_add 2 c.val (t 0).val (by decide) ht
    change decodeLocation ((E, r, h), n) = (5, 0, c.val, (t 0).val)
    dsimp only [pin, pout, rt, st, ein, R, S] at h2 h3 h4 h5 h6 hn
    simp only [decodeLocation, h1, h2, h3, h4, h5, h6, decide_false,
      decide_true, Bool.cond_false, Bool.cond_true, hn, hq, hm]
  | eIn =>
    change decodeLocation ((E, r, h), ein) = _
    simp only [decodeLocation, Bool.cond_eq_ite, decide_eq_true_eq, locCode]
    split_ifs <;> first | rfl | (dsimp [ein, st, rt, pout, pin, R, S] at * <;> omega)
  | eOut =>
    change decodeLocation ((E, r, h), ein + 1) = _
    simp only [decodeLocation, Bool.cond_eq_ite, decide_eq_true_eq, locCode]
    split_ifs <;> first | rfl | (dsimp [ein, st, rt, pout, pin, R, S] at * <;> omega)

theorem locationCount_poly (K : Type) [Fintype K] : Poly (locCount K) := by
  unfold locCount
  fun_prop

/-- The decoded location, big interval, and twin flag. -/
abbrev SiteCode := (LocationCode × ℕ) × Bool

def codedBase (K : Type) [Fintype K] (p : ℕ × ℕ) : SiteCode :=
  let raw := baseCode (locCount K p.1) p.2
  ((decodeLocation ((Fintype.card (Ext K), Fintype.card K, p.1), raw.1.1), raw.1.2), raw.2)

theorem codedBase_poly (K : Type) [Fintype K] : Poly (codedBase K) := by
  have hr := ((Easy.fst.poly.compose (locationCount_poly K)).pair Easy.snd.poly).compose address_poly
  have hloc : Poly (fun p : ℕ × ℕ =>
      ((Fintype.card (Ext K), Fintype.card K, p.1), (baseCode (locCount K p.1) p.2).1.1)) :=
    (show Poly (fun p : ℕ × ℕ => (Fintype.card (Ext K), Fintype.card K, p.1)) from by fun_prop).pair
      hr.fstCompose.fstCompose
  exact ((hloc.compose decodeLocation_poly).pair hr.fstCompose.sndCompose).pair hr.sndCompose

theorem codedBase_eq (V : FiniteMultiTapeMachine) (B I : ℕ) [NeZero B] [NeZero I] {h a : ℕ}
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
    (ι : Fin I) (l : Loc V.K h) (twin : Bool) :
    codedBase V.K (h, P1P7.addr (rnState V B I σ ha) ((ι, l), twin)) =
      ((locCode l, ι.val), twin) := by
  unfold codedBase
  dsimp only
  rw [baseCode_state B σ ha ι l twin, decodeLocation_eq]


end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.decodeLocation_eq
