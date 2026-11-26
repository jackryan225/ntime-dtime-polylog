import P1ChkFinal.ProgC13

/-!
# P1, wave 2: the program of family 12 (C13link) (lane P1-lean-W2-chkfinal)

The check reads two chain entries (P6 section `chain`) and the value `W_v` of the final position `v = bval ρ`.
`W_v` is not a stored field: it is computed from `(x, u, v)` by the evaluation of P5/ProgEng, here the interface
`WHyp` (a Task with its own budget `βW`, which the integration bounds by `t^{o(1)}`), returning the coordinates
`coords b W_v` (one bit per basis vector). The link entry is then a fixed table of the algebra:
`mulEntry b w j j' = Σ_m (b.repr w m) · mulEntry b (b j) m j'` (`linkVal_coords`, from `P1Count.repr_mul_apply`).
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module

open scoped Classical

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- [P5 / ProgEng] `W_v(z|_v; ι(u))` for `v = bval ρ`, as coordinates, within the budget `βW`. -/
def WHyp (b : Basis (Fin Dd) (ZMod 2) F) (Wof : List Bool → List Bool → ℕ → F) (M K : ℕ → ℕ)
    (βW : QDom M K → ℕ) : Prop :=
  Code.Task βW (fun p : QDom M K => send p.val)
    (fun p => send (coords b (Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))))

/-- The link entry computed from coordinates and the fixed table `mulEntry b (b j) m j'`. -/
noncomputable def linkVal (b : Basis (Fin Dd) (ZMod 2) F) (cw : List Bool) (j j' : Fin Dd) : ZMod 2 :=
  ∑ m : Fin Dd, (if cw.getD m false then 1 else 0) * P1Count.mulEntry b (b j) m j'

theorem bool_zmod2 (r : ZMod 2) : (if decide (r = 1) then (1 : ZMod 2) else 0) = r := by
  rcases zmod2_eq_zero_or_one r with h | h <;> subst h <;> decide

theorem linkVal_coords (b : Basis (Fin Dd) (ZMod 2) F) (w : F) (j j' : Fin Dd) :
    linkVal b (coords b w) j j' = P1Count.mulEntry b w j j' := by
  unfold linkVal
  have hg : ∀ m : Fin Dd, (coords b w).getD m false = decide (b.repr w m = 1) := by
    intro m
    simp [coords, List.getD_eq_getElem?_getD]
  simp only [hg, bool_zmod2]
  rw [P1Count.mulEntry, mul_comm, P1Count.repr_mul_apply]

/-- Requests of C13link at position `i`: chain entries `i` and `i + 1` (none if `i ≥ P`). -/
def rqLink (dims : ℕ → Dims) (z : (List Bool × List Bool) × List Bool) : List P1Batch.Req :=
  if P1Batch.bval z.1.2 < finP (dims (P1Batch.bval z.1.1)) then
    [fieldReq (dims (P1Batch.bval z.1.1)) (dims (P1Batch.bval z.1.1)).secChain (P1Batch.bval z.1.2),
      fieldReq (dims (P1Batch.bval z.1.1)) (dims (P1Batch.bval z.1.1)).secChain (P1Batch.bval z.1.2 + 1)]
  else []

/-- The decision of C13link. -/
noncomputable def decLink (b : Basis (Fin Dd) (ZMod 2) F)
    (zf : ((List Bool × List Bool) × List Bool) × List (List Bool)) : Bool :=
  match zf.2 with
  | [f0, f1] => decide (∃ (h : bitsVal f0 < Dd) (h' : bitsVal f1 < Dd),
      linkVal b zf.1.2 ⟨bitsVal f0, h⟩ ⟨bitsVal f1, h'⟩ = 1)
  | _ => true

theorem hckLink (b : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims) (Wof : List Bool → List Bool → ℕ → F)
    (x u ρ : List Bool) :
    decide (C13linkw b dims Wof x u (P1Batch.bval ρ)) =
      decLink b (((bin x.length, ρ), coords b (Wof x u (P1Batch.bval ρ))),
        (rqLink dims ((bin x.length, ρ), coords b (Wof x u (P1Batch.bval ρ)))).map (P1Batch.fetch u)) := by
  by_cases hi : P1Batch.bval ρ < finP (dims x.length)
  · have hi' : P1Batch.bval ρ < finP (dims (P1Batch.bval (bin x.length))) := by rw [bval_bin]; exact hi
    simp only [rqLink, bval_bin]
    rw [if_pos hi]
    simp only [List.map_cons, List.map_nil, decLink]
    rw [decide_eq_decide]
    unfold C13linkw C13link
    simp only [rdChain, readField_eq, linkVal_coords]
    exact ⟨fun h => h hi, fun h _ => h⟩
  · have hi' : ¬ P1Batch.bval ρ < finP (dims (P1Batch.bval (bin x.length))) := by rw [bval_bin]; exact hi
    simp only [rqLink, bval_bin]
    rw [if_neg hi]
    simp only [List.map_nil, decLink]
    exact decide_eq_true (C13linkw_out b dims Wof x u (by unfold cnt13link; omega))

theorem addr_rqLink (dims : ℕ → Dims) (z : (List Bool × List Bool) × List Bool) :
    ∀ r ∈ rqLink dims z, P1Batch.bval r.1 ≤ (dims (P1Batch.bval z.1.1)).fixedLen := by
  intro r hr
  have hc : (dims (P1Batch.bval z.1.1)).count (dims (P1Batch.bval z.1.1)).secChain =
      (dims (P1Batch.bval z.1.1)).chainLen := by
    simp only [Dims.count, (dims (P1Batch.bval z.1.1)).kind_chain]
  unfold rqLink at hr
  split_ifs at hr with hi
  · unfold finP at hi
    rcases List.mem_cons.mp hr with h | hr
    · subst h
      simp only [fieldReq, bval_bin]
      exact field_le_fixedLen _ (Dims.secChain_lt_nSec _) (by rw [hc]; omega)
    · rw [List.mem_singleton] at hr
      subst hr
      simp only [fieldReq, bval_bin]
      exact field_le_fixedLen _ (Dims.secChain_lt_nSec _) (by rw [hc]; omega)
  · simp at hr

theorem total_rqLink_le (dims : ℕ → Dims) (z : (List Bool × List Bool) × List Bool) :
    P1Batch.total (rqLink dims z) ≤ 2 * totC13 (dims (P1Batch.bval z.1.1)) := by
  unfold rqLink
  split_ifs
  · simp only [P1Batch.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fieldReq, bval_bin, totC13]
    omega
  · simp [P1Batch.total]

theorem arith_link (X U R B Dd T Q Ct E : ℕ) (hB : B ≤ Q) (hT : T ≤ Ct * Q) :
    (2 * X + 1 + (2 * U + 1 + (2 * R + 1) + 1) + 1) + E + (2 * Dd + 1 + X) +
        (2 * Dd + 1 + (2 * B + 1 + (2 * U + 1 + (2 * R + 1) + 1) + 1) + 1) + U + T + 1 ≤
      (Ct + 4 * Dd + 20) * (X + U + R + Q + E + 1) := by
  have : Ct * Q ≤ Ct * (X + U + R + Q + E + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 4 * Dd * 1 ≤ 4 * Dd * (X + U + R + Q + E + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul, Nat.add_mul]
  omega

/-- **Family 12 (C13link), program** (budget: the family budget plus the budget `βW` of the evaluation). -/
theorem progC13link (b : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims)
    (Wof : List Bool → List Bool → ℕ → F) (M K : ℕ → ℕ) (βW : QDom M K → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hM : ∀ n, (dims n).fixedLen ≤ M n) (hW : WHyp b Wof M K βW)
    (hrq : Poly (fun z : (List Bool × List Bool) × List Bool => (rqLink dims z, z)))
    (hdec : Poly (decLink b))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC13 (dims n))) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val + βW p) (fun p => send p.val)
      (fun p => send (decide (C13linkw b dims Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let cw : QDom M K → List Bool := fun p => coords b (Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))
  let σ : QDom M K → ℕ := fun p => Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length
  have hcw : ∀ p, (cw p).length = Dd := fun p => by simp [cw, coords]
  -- (A) clone, evaluate W_v on one copy, binary length of x on the other, rearrange
  have T0 := (Easy.clone (X := Qry)).on (fun p : QDom M K => p.val)
  have TW := hW.left (fun p : QDom M K => send p.val)
  have TL := (((lenHyp_bin hl).on (fun p : QDom M K => p.val.1)).left (fun p => send p.val.2)).right (fun p => send (cw p))
  have E1 : Easy (fun w : List Bool × (List Bool × (List Bool × List Bool)) => (w.2.2.1, ((w.2.1, w.2.2.2), w.1))) :=
    Easy.pair (Easy.compose (Easy.compose Easy.snd Easy.snd) Easy.fst)
      (Easy.pair (Easy.pair (Easy.compose Easy.snd Easy.fst) (Easy.compose (Easy.compose Easy.snd Easy.snd) Easy.snd))
        Easy.fst)
  have TR := E1.on (fun p : QDom M K => (cw p, (bin p.val.1.length, p.val.2)))
  have hA : Code.Task (fun p : QDom M K => size p.val + βW p + ((send (cw p)).count + p.val.1.length) +
        size (cw p, (bin p.val.1.length, p.val.2)))
      (fun p => send p.val) (fun p => send (p.val.2.1, ((bin p.val.1.length, p.val.2.2), cw p))) :=
    ((T0.compose TW).compose TL).compose TR
  have hlog : ∀ p : QDom M K, (bin p.val.1.length).length ≤ Nat.log 2 (p.val.1.length + 1) + 1 :=
    fun p => (length_bin_log _).trans (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)
  have hσ : Dom σ (fun p => size ((bin p.val.1.length, p.val.2.2), cw p)) := by
    refine ⟨1, 2 * Dd + 10, fun p => ?_⟩
    simp only [size_prod, size_listBool, pow_one, σ, hcw]
    have := hlog p
    nlinarith
  have htot : Dom σ (fun p => P1Batch.total (rqLink dims ((bin p.val.1.length, p.val.2.2), cw p))) := by
    obtain ⟨k, C, hk⟩ := hfb
    refine ⟨k, 2 * C, fun p => ?_⟩
    refine (total_rqLink_le dims _).trans ?_
    simp only [bval_bin]
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ((hk _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)))
    simp only [σ]
    omega
  have haddr' : ∀ p : QDom M K, ∀ r ∈ rqLink dims ((bin p.val.1.length, p.val.2.2), cw p),
      P1Batch.bval r.1 ≤ p.val.2.1.length := by
    intro p r hr
    have h1 := addr_rqLink dims _ r hr
    simp only [bval_bin] at h1
    rw [p.property.1]
    exact h1.trans (hM _)
  obtain ⟨t, ⟨kt, Ct, hkt⟩, T⟩ := checkSkeleton hb (fun p : QDom M K => send p.val) (fun p => p.val.2.1)
    (fun p => ((bin p.val.1.length, p.val.2.2), cw p)) (rqLink dims) (decLink b)
    (fun p => decide (C13linkw b dims Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) _ σ hA hrq hdec hσ htot
    haddr' (fun p => hckLink b dims Wof p.val.1 p.val.2.1 p.val.2.2)
  refine ⟨kt + 1, T.bound (Ct + 4 * Dd + 20) fun p => ?_⟩
  have h1 := hkt p
  have h2 := hlog p
  have hc := hcw p
  simp only [σ] at h1
  have hcc : (send (cw p)).count = 2 * Dd + 1 := by rw [← hc]; exact size_listBool (cw p)
  simp only [budget, size_prod, size_listBool, hcc, hc]
  set P := Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length + 1 with hPdef
  have hP0 : 1 ≤ P := by omega
  have hP1 : P ≤ P ^ (kt + 1) := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ (kt + 1) := Nat.pow_le_pow_right hP0 (by omega)
  have hP2 : P ^ kt ≤ P ^ (kt + 1) := Nat.pow_le_pow_right hP0 (by omega)
  have h3 : t p ≤ Ct * P ^ (kt + 1) := h1.trans (Nat.mul_le_mul_left _ hP2)
  have hb2 : (bin p.val.1.length).length ≤ P ^ (kt + 1) := by omega
  exact arith_link _ _ _ _ _ _ _ _ _ hb2 h3

end P1ChkFinal
