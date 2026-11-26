import P1SolC10P.Decision
import P1SolC10P.Rounds

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1Wit P1C10 P1ChkFinal P1ChkGreedy
open scoped P1ChkFinal.AstraC10

set_option maxHeartbeats 1600000

theorem roundTotal_le (dH : ℕ) (s : C10State) :
    P1Batch.total (requests dH s) ≤ size (roundKeys dH s) * size s := by
  refine (total_map_reqOf_le _ _ (fun _ hk => (roundKeys_bounds dH s hk).2)).trans ?_
  have h1 := (duration (roundKeys dH s)).le
  have h2 : s.1.1.length ≤ size s := by
    simp only [size_prod, size_tally]
    omega
  exact Nat.mul_le_mul h1 h2

theorem dom_roundTotal {X : Type} {σ : X → ℕ} {s : X → C10State}
    (dH : ℕ) (hs : Dom σ (fun p => size (s p))) :
    Dom σ (fun p => P1Batch.total (requests dH (s p))) :=
  ((((poly_roundKeys dH).length.map s).sub hs).mul hs).mono (fun p => roundTotal_le dH (s p))

theorem dom_advance {X : Type} {σ : X → ℕ} {s : X → C10State} (u : X → List Bool)
    (dH : ℕ) (hs : Dom σ (fun p => size (s p))) :
    Dom σ (fun p => size (advance dH (s p, (requests dH (s p)).map (P1Batch.fetch (u p))))) := by
  have hl := ((poly_requests dH).length.map s).sub hs
  have ht := dom_roundTotal dH hs
  have hw : Dom σ (fun p => size ((requests dH (s p)).map (P1Batch.fetch (u p)))) := by
    apply (((Dom.const σ 2).mul (hl.add ht)).add (Dom.const σ 1)).mono
    intro p
    exact (size_fetch_le _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (duration (requests dH (s p))).le _)) _)
  have hp : Dom σ (fun p => size (s p, (requests dH (s p)).map (P1Batch.fetch (u p)))) :=
    (hs.add hw).add (Dom.const σ 1)
  exact (((poly_advance dH).length.map
    (fun p => (s p, (requests dH (s p)).map (P1Batch.fetch (u p))))).sub hp)

theorem dom_stateAt {X : Type} {σ : X → ℕ} (u : X → List Bool) (h : X → C10Head)
    (dH : ℕ) (hs : Dom σ (fun p => size (initial (h p)))) (r : ℕ) :
    Dom σ (fun p => size (stateAt dH (u p) (h p) r)) := by
  induction r with
  | zero => exact hs
  | succ r ih => exact dom_advance u dH ih

theorem address_requests (u : List Bool) (dH : ℕ) {h : C10Head} (hh : h.2.1 = u.length)
    (r : ℕ) (q : P1Batch.Req) (hq : q ∈ requests dH (stateAt dH u h r)) :
    P1Batch.bval q.1 ≤ u.length := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  have h1 := (roundKeys_bounds dH (stateAt dH u h r) hk).1
  simpa only [reqOf, P1ChkFinal.AstraC10.bval_binary, stateAt_head, hh] using h1

def programSigma (q : P1ChkFinal.Qry) : ℕ :=
  (Nat.log 2 (q.1.length + 1) + q.2.2.length) + Nat.log 2 (q.2.1.length + 1)

def headerInput (q : P1ChkFinal.Qry) : P1ChkFinal.Qry :=
  (bin q.1.length, bin q.2.1.length, q.2.2)

def initialCost (q : P1ChkFinal.Qry) : ℕ :=
  q.1.length + size (bin q.1.length, q.2) +
    (size q.2.1 + (size q.2.1 + q.2.1.length)) + size ((q.2.1, bin q.2.1.length), (bin q.1.length, q.2.2))

theorem strip_input (hl : LenHyp) :
    Computes initialCost (fun q : P1ChkFinal.Qry => (q.2.1, headerInput q)) := by
  have change1 : Easy (fun q : P1ChkFinal.Qry => (q.2.1, (q.1, q.2.2))) :=
    Easy.pair (Easy.snd.compose Easy.fst) (Easy.pair Easy.fst (Easy.snd.compose Easy.snd))
  have change2 : Easy (fun q : (List Bool × List Bool) × (List Bool × List Bool) =>
      (q.1.1, (q.2.1, q.1.2, q.2.2))) :=
    Easy.pair (Easy.fst.compose Easy.fst)
      (Easy.pair (Easy.snd.compose Easy.fst)
        (Easy.pair (Easy.fst.compose Easy.snd) (Easy.snd.compose Easy.snd)))
  have makeU : Computes (fun u : List Bool => size u + (size u + u.length))
      (fun u : List Bool => (u, bin u.length)) := by
    have keep := (lenHyp_bin hl).right (fun u : List Bool => send u)
    exact Code.Task.compose (Easy.clone (X := List Bool)) keep
  have tx := ((lenHyp_bin hl).on (fun q : P1ChkFinal.Qry => q.1)).left (fun q => send q.2)
  have tw := tx.compose (change1.on (fun q : P1ChkFinal.Qry => (bin q.1.length, q.2)))
  have tu := (makeU.on (fun q : P1ChkFinal.Qry => q.2.1)).left (fun q => send (bin q.1.length, q.2.2))
  exact (tw.compose tu).compose (change2.on (fun q : P1ChkFinal.Qry =>
    ((q.2.1, bin q.2.1.length), (bin q.1.length, q.2.2))))

theorem size_headerInput (q : P1ChkFinal.Qry) : size (headerInput q) ≤ 2 * programSigma q + 9 := by
  have hx := length_bin_log q.1.length
  have hu := length_bin_log q.2.1.length
  have hx' : Nat.log 2 q.1.length ≤ Nat.log 2 (q.1.length + 1) :=
    Nat.log_mono_right (Nat.le_succ q.1.length)
  have hu' : Nat.log 2 q.2.1.length ≤ Nat.log 2 (q.2.1.length + 1) :=
    Nat.log_mono_right (Nat.le_succ q.2.1.length)
  simp only [headerInput, programSigma, size_prod, size_listBool]
  omega

theorem initialCost_le (q : P1ChkFinal.Qry) :
    initialCost q ≤ 18 * (q.1.length + q.2.1.length + q.2.2.length + 1) + 4 * (programSigma q + 1) := by
  have hx := length_bin_log q.1.length
  have hu := length_bin_log q.2.1.length
  have hx' : Nat.log 2 q.1.length ≤ Nat.log 2 (q.1.length + 1) :=
    Nat.log_mono_right (Nat.le_succ q.1.length)
  have hu' : Nat.log 2 q.2.1.length ≤ Nat.log 2 (q.2.1.length + 1) :=
    Nat.log_mono_right (Nat.le_succ q.2.1.length)
  simp only [initialCost, programSigma, size_prod, size_listBool]
  omega

theorem log_pow_linear (c n : ℕ) :
    (Nat.log 2 (n + 1) + 1) ^ c ≤ (c.factorial * 2 ^ c) * (n + 1) := by
  let m := Nat.log 2 (n + 1)
  have hm : 2 ^ m ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  calc
    (m + 1) ^ c ≤ (m + c).descFactorial c := by
      have h := Nat.pow_sub_le_descFactorial (m + c) c
      rw [show m + c + 1 - c = m + 1 by omega] at h
      exact h
    _ = c.factorial * (m + c).choose c := Nat.descFactorial_eq_factorial_mul_choose _ _
    _ ≤ c.factorial * 2 ^ (m + c) :=
      Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = (c.factorial * 2 ^ c) * 2 ^ m := by rw [pow_add]; ac_rfl
    _ ≤ (c.factorial * 2 ^ c) * (n + 1) := Nat.mul_le_mul_left _ hm

theorem sig_pow_le_budget (j : ℕ) (q : P1ChkFinal.Qry) :
    (programSigma q + 1) ^ j ≤ (2 ^ j * (1 + j.factorial * 2 ^ j)) * (budget j q + 1) := by
  let a := Nat.log 2 (q.1.length + 1) + q.2.2.length + 1
  let b := Nat.log 2 (q.2.1.length + 1) + 1
  have hab : programSigma q + 1 ≤ 2 * max a b := by
    have h1 : a ≤ max a b := le_max_left _ _
    have h2 : b ≤ max a b := le_max_right _ _
    unfold programSigma a b at *
    omega
  have ha : a ^ j ≤ budget j q + 1 := by
    unfold budget
    change a ^ j ≤ _ + a ^ j + 1
    omega
  have hb : b ^ j ≤ (j.factorial * 2 ^ j) * (budget j q + 1) := by
    exact (log_pow_linear j q.2.1.length).trans (Nat.mul_le_mul_left _ (by unfold budget; omega))
  calc
    (programSigma q + 1) ^ j ≤ (2 * max a b) ^ j := Nat.pow_le_pow_left hab _
    _ = 2 ^ j * (max a b) ^ j := mul_pow ..
    _ ≤ 2 ^ j * ((1 + j.factorial * 2 ^ j) * (budget j q + 1)) := by
      apply Nat.mul_le_mul_left
      rw [Nat.add_mul, Nat.one_mul]
      rcases le_total a b with h | h
      · rw [max_eq_right h]
        exact hb.trans (Nat.le_add_left _ _)
      · rw [max_eq_left h]
        exact ha.trans (Nat.le_add_right _ _)
    _ = _ := (Nat.mul_assoc ..).symm

theorem decision_correct (fx : C10Fix) (dims : ℕ → Dims) {C k : ℕ}
    (hb : ∀ n, c10Size (dims n) ≤ C * (Nat.log 2 (n + 1) + 1) ^ k)
    (q : P1ChkFinal.Qry) :
    decide (C10w fx dims q.1 q.2.1 (P1Batch.bval q.2.2)) =
      finalCheck fx (stateAt fx.dH q.2.1 (makeHead dims C k (headerInput q))
        (roundCount (makeHead dims C k (headerInput q)))) := by
  let D := dims q.1.length
  let l := P1Batch.bval q.2.2 % 2 ^ levBits D
  let Y := P1Batch.bval q.2.2 / 2 ^ levBits D
  let t := makeClock C k (bin q.1.length)
  let h := actualHead D q.2.1 l Y t
  have hh : makeHead dims C k (headerInput q) = h := makeHead_eq dims C k _ _ _
  rw [hh]
  change decide ((l < D.top ∧ Y < (D.lv (l + 1)).bases) → C10at fx D q.2.1 l Y) = _
  have en : enabled h = (decide (l < D.top) && decide (Y < (D.lv (l + 1)).bases)) :=
    enabled_actual D q.2.1 l Y t
  by_cases hi : l < D.top ∧ Y < (D.lv (l + 1)).bases
  · have hen : enabled h = true := by simp only [en, hi.1, hi.2, decide_true, Bool.true_and]
    have fit : Fits D l t := fits_of_size D hi.1 (size_le_clock dims hb)
    rw [finalCheck_valid fx fit hen, decide_eq_decide]
    exact ⟨fun h => h hi, fun h _ => h⟩
  · have hen : enabled h ≠ true := by
      intro he
      rw [en] at he
      have both : decide (l < D.top) = true ∧ decide (Y < (D.lv (l + 1)).bases) = true := by
        simpa only [Bool.and_eq_true] using he
      exact hi ⟨of_decide_eq_true both.1, of_decide_eq_true both.2⟩
    have he' : enabled (stateAt fx.dH q.2.1 h (roundCount h)).1 ≠ true := by
      rw [stateAt_head]
      exact hen
    simp only [finalCheck, Bool.eq_false_of_not_eq_true he', Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq]
    intro h
    exact False.elim (hi h)

end P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1C10 P1ChkFinal P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

set_option maxHeartbeats 1600000 in
theorem P1SolC10P.progC10 : P1C10.ProgC10Target := by
  intro fx dims M K hb hl _hM hf hfb hS hR
  obtain ⟨k, C, hclock⟩ := hfb
  let X := QDom M K
  let σ : X → ℕ := fun p => programSigma p.val
  let u : X → List Bool := fun p => p.val.2.1
  let h : X → C10Head := fun p => makeHead dims C k (headerInput p.val)
  have hi : Dom σ (fun p : X => size (headerInput p.val)) := by
    refine ⟨1, 9, fun p => (size_headerInput p.val).trans ?_⟩
    simp only [σ, pow_one]
    omega
  let sh : X → Bool := fun p => shrinking (h p)
  let s : X → C10State := fun p => initial (h p)
  let qry : X → Tree := fun p => send (u p, s p)
  let ck : X → Bool := fun p => decide (C10w fx dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))
  have hp := (poly_makeHead dims C k hf).compose poly_initial
  have hs : Dom σ (fun p => size (s p)) := (hp.length.map _).sub hi
  have htag := (poly_makeHead dims C k hf).compose poly_shrinking
  obtain ⟨a, ha, ta⟩ := (htag.pair hp).on hi
  have sort : Easy (fun q : List Bool × (Bool × C10State) => (q.2.1, (q.1, q.2.2))) :=
    Easy.pair (Easy.snd.compose Easy.fst) (Easy.pair Easy.fst (Easy.snd.compose Easy.snd))
  have Tinit : Code.Task
      (fun p : X => initialCost p.val + (size (u p) + a p) + size (u p, (sh p, s p)))
      (fun p => send p.val) (fun p => (Tree.atom (sh p)).fork (qry p)) :=
    (((strip_input hl).on (fun p : X => p.val)).compose (ta.right (fun p => send (u p)))).compose
      (sort.on (fun p => (u p, (sh p, s p))))
  have hAddr (p : X) : (h p).2.1 = (u p).length := P1ChkFinal.bval_bin _
  have branch (kind : Bool) : ∃ e D : ℕ,
      Code.Task (fun p : {p : X // sh p = kind} =>
        8 * (u p.val).length + D * (σ p.val + 1) ^ e)
        (fun p => qry p.val) (fun p => send (ck p.val)) := by
    let R : ℕ := if kind then 7 else 2
    let f : {p : X // sh p = kind} → X := Subtype.val
    have hRle : R + 1 ≤ 8 := by cases kind <;> decide
    have hck (p : {p : X // sh p = kind}) :
        ck p.val = finalCheck fx (stateAt fx.dH (u p.val) (h p.val) R) := by
      have er : roundCount (h p.val) = R := by
        change (if sh p.val then 7 else 2) = R
        rw [p.property]
      have e := decision_correct fx dims hclock p.val.val
      change ck p.val = finalCheck fx (stateAt fx.dH (u p.val) (h p.val) (roundCount (h p.val))) at e
      simpa only [er] using e
    have hst (r : ℕ) := dom_stateAt u h fx.dH hs r
    obtain ⟨t, ⟨e, D, ht⟩, T⟩ := P1SolC10P.checkRounds hb R (qry ∘ f) (u ∘ f) (s ∘ f)
      (requests fx.dH) (advance fx.dH) (finalCheck fx) (ck ∘ f) (fun _ => 0) (σ ∘ f)
      Task.self ((poly_requests fx.dH).pair Code.Poly.identity) (poly_advance fx.dH)
      (poly_finalCheck fx hS hR) (fun r _ => (hst r).map f)
      (fun r _ => (dom_roundTotal fx.dH (hst r)).map f)
      (fun p r _ q hq => address_requests (u p.val) fx.dH (hAddr p.val) r q hq) hck
    refine ⟨e, D, T.mono (fun p => ?_)⟩
    simp only [Nat.zero_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hRle) (ht p)
  obtain ⟨ef, Df, Tf⟩ := branch false
  obtain ⟨et, Dt, Tt⟩ := branch true
  let small (p : X) : ℕ := Df * (σ p + 1) ^ ef + Dt * (σ p + 1) ^ et
  have Tdec : Code.Task (fun p : X => 8 * (u p).length + small p)
      (fun p => (Tree.atom (sh p)).fork (qry p)) (fun p => send (ck p)) := by
    apply Code.Task.control sh
    · apply Tf.mono
      intro p
      exact Nat.add_le_add_left (Nat.le_add_right _ _) _
    · apply Tt.mono
      intro p
      exact Nat.add_le_add_left (Nat.le_add_left _ _) _
  have T := Tinit.compose Tdec
  have dsmall : Dom σ small :=
    (show Dom σ (fun p => Df * (σ p + 1) ^ ef) from ⟨ef, Df, fun _ => le_rfl⟩).add
      (show Dom σ (fun p => Dt * (σ p + 1) ^ et) from ⟨et, Dt, fun _ => le_rfl⟩)
  have hd : Dom σ (fun p => a p + size (s p) + small p + 4 * (σ p + 1)) :=
    ((ha.add hs).add dsmall).add ((Dom.const σ 4).mul ((Dom.base σ).add (Dom.const σ 1)))
  obtain ⟨j, A, hj⟩ := hd
  let B := 2 ^ j * (1 + j.factorial * 2 ^ j)
  refine ⟨j, T.bound (36 + A * B) fun p => ?_⟩
  have hh := (hj p).trans (Nat.mul_le_mul_left A (sig_pow_le_budget j p.val))
  have hinit := initialCost_le p.val
  have hbudget : p.val.1.length + p.val.2.1.length + p.val.2.2.length + 1 ≤ budget j p.val + 1 := by
    unfold budget
    omega
  have hcost := Nat.mul_le_mul_left 36 hbudget
  have hs' : a p + size (s p) + small p + 4 * (σ p + 1) ≤ (A * B) * (budget j p.val + 1) := by
    simpa only [σ, B, Nat.mul_assoc] using hh
  have hsort : size (u p, (sh p, s p)) = 2 * (u p).length + size (s p) + 4 := by
    change size (u p) + (size (sh p) + size (s p) + 1) + 1 = _
    simp only [size_listBool, size_bit]
    omega
  change initialCost p.val + (size (u p) + a p) + size (u p, (sh p, s p)) +
    (8 * (u p).length + small p) + 1 ≤ (36 + A * B) * (budget j p.val + 1)
  rw [Nat.add_mul, hsort, size_listBool]
  dsimp only [u, σ] at hinit hs' ⊢
  omega

#print axioms P1SolC10P.progC10
