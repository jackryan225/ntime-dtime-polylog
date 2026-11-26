import P1ProgDir.C3Correct
import P1ProgDir.Adapter
import P1ProgDir.Budget

namespace P1ProgDir.SolProgram3

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Wit P1ChkDir P1Int
open P1ProgDir.SolGeometry P1ProgDir.SolFieldWords P1ProgDir.SolFrontWords P1ProgDir.SolOffsets
open P1ProgDir.SolAdapter P1ProgDir.SolBudget

def header (a b aM r w₀ w₁ : ℕ) (p : Word × Word) : SolC3Input.Header :=
  (p.2, (iWord a b aM p.1, startWord a b aM r p.1, endWord a b aM r w₀ w₁ 1 p.1,
    endWord a b aM r w₀ w₁ 4 p.1), widthTally a b w₀ w₁ p.1, hTally a b p.1)

theorem poly_header (a b aM r w₀ w₁ : ℕ) : Poly (header a b aM r w₀ w₁) := by
  have hn : Poly (fun p : Word × Word => p.1) := Poly.identity.fstCompose
  exact Poly.identity.sndCompose.pair
    (((hn.compose (poly_iWord a b aM)).pair ((hn.compose (poly_startWord a b aM r)).pair
      ((hn.compose (poly_endWord a b aM r w₀ w₁ 1)).pair
        (hn.compose (poly_endWord a b aM r w₀ w₁ 4))))).pair
        ((hn.compose (poly_widthTally a b w₀ w₁)).pair (hn.compose (poly_hTally a b))))

set_option maxHeartbeats 1200000 in
theorem header_fits (a b aM r w₀ w₁ : ℕ) (D : Dims) (p : Word × Word) (w : Word)
    (hI : D.I = bigCount a b aM (value p.1))
    (hN : D.N = laneCount a b (value p.1)) (hr : D.r = r)
    (hW : D.bigW = w₀ + w₁ * lpK2 a b (value p.1)) (hfit : D.fixedLen ≤ w.length) :
    SolC3Input.Fits D r (header a b aM r w₀ w₁ p) w := by
  have hs : value (startWord a b aM r p.1) = tritEnd D := by
    rw [startWord_value, tritEnd, hI, hN, hr]
  have hw : value (directoryWidth a b aM r w₀ w₁ p.1) = D.I * D.r * D.bigW := by
    rw [directoryWidth_value, hI, hr, hW]
  refine ⟨(iWord_value a b aM p.1).trans hI.symm, hs.trans (off_start D).symm, ?_, ?_,
    (widthTally_length a b w₀ w₁ p.1).trans hW.symm, ?_, hr.symm, head_fits hfit⟩
  · change value (endWord a b aM r w₀ w₁ 1 p.1) = D.off secPrev
    rw [endWord_value, hs, hw, off_prev, startEnd, Nat.one_mul]
  · change value (endWord a b aM r w₀ w₁ 4 p.1) = D.off secNext
    rw [endWord_value, hs, hw, off_next, prevEnd, startEnd]
    ring
  · exact (congrArg (fun j : ℕ => (2 : ℕ) ^ j) (hTally_length a b p.1)).trans hN.symm

theorem header_size (a b aM r w₀ w₁ : ℕ) :
    ∃ C : ℕ, ∀ n ρ : Word, ρ.length ≤ lpK2 a b (value n) →
      size (header a b aM r w₀ w₁ (n, ρ)) ≤ C * (lpK2 a b (value n) + 1) := by
  let A := 2 * aM + 12
  let B := r * (A + 1)
  let W := w₀ + w₁
  let S := B + 12
  let E := S + 8 * (B + W) + 6
  refine ⟨2 * (1 + A + S + 2 * E + W + 10) + 20, ?_⟩
  intro n ρ hρ
  let lamN := lpK2 a b (value n)
  change ρ.length ≤ lamN at hρ
  have hl : 1 ≤ lamN + 1 := by omega
  have hp : lpP2 a b (value n) ≤ lamN := Nat.log_le_self _ _
  have hh : (hTally a b n).length ≤ 10 * lamN := by rw [hTally_length]; omega
  have hb : (bTally a b n).length ≤ 10 * lamN := by rw [bTally_length]; omega
  have hfill (v : Bool) (s : Tally) : (fill v s).length = s.length := by rw [fill_eq, List.length_replicate]
  have hpow : ∀ s : Tally, (powWord s).length = s.length + 1 := by
    intro s
    simp only [powWord, shift, List.length_append, hfill, List.length_cons, List.length_nil]
  have hI : (iWord a b aM n).length ≤ A * (lamN + 1) := by
    simp only [iWord, cutLists, List.length_drop]
    apply (Nat.sub_le _ _).trans
    rw [add_length, scale_length, hpow, lambdaTally_length, hfill]
    change aM * (lamN + 1 + 1) + (bTally a b n).length + 1 ≤ _
    unfold A
    nlinarith [Nat.zero_le (aM * lamN)]
  have hB : (blocksWord a b aM r n).length ≤ B * (lamN + 1) := by
    rw [blocksWord, scale_length]
    exact (Nat.mul_le_mul_left r (show (iWord a b aM n).length + 1 ≤ (A + 1) * (lamN + 1) by
      rw [Nat.add_mul, Nat.one_mul]; omega)).trans_eq (by unfold B; ring)
  have hs : (startWord a b aM r n).length ≤ S * (lamN + 1) := by
    simp only [startWord, tritCountWord, shift, List.length_cons, List.length_append, hfill]
    change (hTally a b n).length + (blocksWord a b aM r n).length + 1 ≤ _
    unfold S
    rw [Nat.add_mul]
    omega
  have hw : (widthTally a b w₀ w₁ n).length ≤ W * (lamN + 1) := by
    rw [widthTally_length]
    change w₀ + w₁ * lamN ≤ _
    unfold W
    nlinarith [Nat.zero_le (w₀ * lamN)]
  have hwn := (birthLen (widthTally a b w₀ w₁ n).length).trans hw
  have hd : (directoryWidth a b aM r w₀ w₁ n).length ≤ 2 * ((B + W) * (lamN + 1)) := by
    rw [directoryWidth, length_prod, Nat.add_mul]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add hB hwn)
  have he (c : ℕ) (hc : c ≤ 4) : (endWord a b aM r w₀ w₁ c n).length ≤ E * (lamN + 1) := by
    rw [endWord, add_length, scale_length]
    have cmp := Nat.mul_le_mul hc (Nat.add_le_add_right hd 1)
    unfold E
    nlinarith
  have hh' : (hTally a b n).length ≤ 10 * (lamN + 1) := by omega
  simp only [header, size_prod, size_word, size_tally]
  change _ ≤ _ * (lamN + 1)
  have he₁ := he 1 (by decide)
  have he₄ := he 4 (by decide)
  ring_nf at *
  linarith

open Classical in
theorem _root_.P1ProgDir.progC3 {K : Type} (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
    (aM r w₀ w₁ n₀ : ℕ) [NeZero r] (D : ℕ → Dims) (tape : ∀ n, K ≃ Fin (D n).r)
    (hI : ∀ n, n₀ ≤ n → (D n).I = bigCount a b aM n)
    (hN : ∀ n, n₀ ≤ n → (D n).N = laneCount a b n)
    (hr : ∀ n, n₀ ≤ n → (D n).r = r)
    (hW : ∀ n, n₀ ≤ n → (D n).bigW = w₀ + w₁ * lpK2 a b n)
    (hfit : ∀ n, n₀ ≤ n → (D n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
        ∀ (u : Fin (lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (C3F (D x.length) (tape x.length) (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  apply checkProgram (fun x u i => C3F (D x.length) (tape x.length) u i)
  let X := Input s a b n₀
  let q (x : X) := raw x
  let n (x : X) := x.1.val.length
  let p (x : X) := (lengthHeader (q x)).1
  let u (x : X) := (q x).2.1
  let h (x : X) := header a b aM r w₀ w₁ (p x)
  let out (x : X) := SolSmallBatch.readPlan (SolC3Input.plan r) (h x) (u x)
  let z (x : X) := SolC3Engine.packed r (out x)
  have hu (x : X) : (u x).length = lpM2 s a b (n x) := List.length_ofFn
  have hn (x : X) : value (p x).1 = n x := birthValue _
  have hh (x : X) : SolC3Input.Fits (D (n x)) r (h x) (u x) := by
    have hx := x.1.property
    exact header_fits _ _ _ _ _ _ _ _ _
      (by rw [hn]; exact hI _ hx) (by rw [hn]; exact hN _ hx) (hr _ hx)
      (by rw [hn]; exact hW _ hx) (by rw [hu]; exact hfit _ hx)
  obtain ⟨β, hβ, hc⟩ := SolC3Correct.prepare (D ∘ n) r h u hh
  have hhead := poly_header a b aM r w₀ w₁
  have hsz := (Code.Poly.length hhead).map p
  obtain ⟨α, hα, hpre⟩ := hhead
  let θ (x : X) := α (p x) + β x + (size (z x) + 1)
  have hζ : Dom (fun x => size (p x)) (fun x => size (z x)) := by
    have hread := SolSmallBatch.readPlan_size h u (SolC3Input.plan r)
      (SolC3Input.poly_plan r) ((SolC3Input.total_dom r).map h)
    exact (((Code.Poly.length (SolC3Engine.poly_packed r)).map out).sub hread).sub hsz
  have hθ : Dom (fun x => size (p x)) θ :=
    ((hα.map p).add (hβ.sub hsz)).add (hζ.add (Dom.const _ 1))
  have hl := (easy_lengthHeader.on q).compose ((hpre.on p).left (fun x => send (u x)))
  have hrun := hl.compose hc
  have hsnd (x : X) : (q x).2.2.length ≤ lpK2 a b (n x) :=
    x.2.2.property ▸ Nat.sub_le _ _
  obtain ⟨A, hA⟩ := raw_poly_cost q s hs a b hb hu hsnd hθ
  obtain ⟨C, hC⟩ := header_size a b aM r w₀ w₁
  obtain ⟨F, hF⟩ := SolC3Engine.packed_size r
  obtain ⟨G, hG⟩ := directory_scan_bound s hs a b aM hb
  let P := F * (4 * C + 7) + 1
  have hscan (x : X) : (D (n x)).I * (size (z x) + 1) ≤ P * G * lpM2 s a b (n x) := by
    let l := lpK2 a b (n x) + 1
    have hpos : 1 ≤ l := by unfold l; omega
    have h0 : size (h x) ≤ C * l := by
      have e := hC (p x).1 (p x).2 (by rw [hn]; exact hsnd x)
      rw [hn] at e
      exact e
    have h1 : size (out x) + 1 ≤ (4 * C + 7) * l := by
      have e : size (out x) ≤ 4 * size (h x) + 6 := SolC3Input.readPlan_size_linear r (h x) (u x)
      rw [Nat.add_mul, Nat.mul_assoc]
      omega
    have h2 : size (z x) + 1 ≤ P * l := by
      have e : size (z x) ≤ F * ((4 * C + 7) * l) :=
        (hF (out x)).trans (Nat.mul_le_mul_left F h1)
      unfold P
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    have hd : l ≤ l ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by unfold l; omega)
    have h3 := (Nat.mul_le_mul_left ((D (n x)).I) h2).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd))
    rw [hI _ x.1.property, Nat.mul_left_comm] at h3
    rw [hI _ x.1.property]
    exact h3.trans ((Nat.mul_le_mul_left P (hG (n x))).trans_eq (by ring))
  refine (hrun.conform (fun _ => rfl) (fun _ => rfl) (fun x => ?_)).bound (A + P * G) ?_
  · apply congrArg send
    rw [Bool.eq_iff_iff, decide_eq_true_eq, P1Batch.bval_eq_value]
    exact SolC3Correct.reply_iff (tape (n x)) (hh x)
  · intro x
    let m := lpM2 s a b (n x)
    let e := lpP2 a b (n x) + 1
    change size (q x) + α (p x) + ((u x).length + β x +
      ((D (n x)).I + 1) * (size (z x) + 1)) + 1 ≤ (A + P * G) * (m * e + 1)
    have hhA := hA x
    change size (q x) + (u x).length + θ x + 1 ≤ A * (m * e + 1) at hhA
    rw [Nat.add_mul ((D (n x)).I) 1, Nat.one_mul, Nat.add_mul A]
    have hmx : m ≤ m * e + 1 := (Nat.le_mul_of_pos_right _ (by unfold e; omega)).trans (Nat.le_succ _)
    have hS := (hscan x).trans (Nat.mul_le_mul_left (P * G) hmx)
    unfold θ at hhA
    omega

#print axioms P1ProgDir.progC3

end P1ProgDir.SolProgram3
