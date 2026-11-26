import P1ProgDir.C14Batch
import P1ProgDir.Adapter
import P1ProgDir.Budget

namespace P1ProgDir.SolProgram14

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkDir P1Wit P1Int
open P1ProgDir.SolGeometry P1ProgDir.SolFrontWords P1ProgDir.SolFieldWords
open P1ProgDir.SolAdapter P1ProgDir.SolBudget P1ProgDir.SolOffsets

def header (a b aM r w₀ w₁ : ℕ) (p : Word × Word) : SolC14Batch.Header :=
  ((p.2, guessCountWord a b p.1),
    (iWord a b aM p.1, widthTally a b w₀ w₁ p.1, hTally a b p.1),
    (startWord a b aM r p.1, endWord a b aM r w₀ w₁ 1 p.1, endWord a b aM r w₀ w₁ 7 p.1))

theorem poly_header (a b aM r w₀ w₁ : ℕ) : Poly (header a b aM r w₀ w₁) := by
  have hn : Poly (fun p : Word × Word => p.1) := Poly.identity.fstCompose
  exact (Poly.identity.sndCompose.pair (hn.compose (poly_guessCountWord a b))).pair
    (((hn.compose (poly_iWord a b aM)).pair
      ((hn.compose (poly_widthTally a b w₀ w₁)).pair (hn.compose (poly_hTally a b)))).pair
        ((hn.compose (poly_startWord a b aM r)).pair
          ((hn.compose (poly_endWord a b aM r w₀ w₁ 1)).pair
            (hn.compose (poly_endWord a b aM r w₀ w₁ 7)))))

set_option maxHeartbeats 1200000 in
theorem header_fits (a b aM r w₀ w₁ t : ℕ) (D : Dims) (p : Word × Word) (w : Word)
    (hI : D.I = bigCount a b aM (value p.1))
    (hN : D.N = laneCount a b (value p.1)) (hr : D.r = r)
    (hW : D.bigW = w₀ + w₁ * lpK2 a b (value p.1))
    (hG : D.nGB = nGuessBlocks (a * ((value p.1) ^ 2 + 1))
      (2 ^ (lpP2 a b (value p.1) / 2) * D.N))
    (ht : t < r) (hfit : D.fixedLen ≤ w.length) :
    SolC14Batch.Fits D r t (header a b aM r w₀ w₁ p) w := by
  have hs : value (startWord a b aM r p.1) = tritEnd D := by
    rw [startWord_value, tritEnd, hI, hN, hr]
  have hw : value (directoryWidth a b aM r w₀ w₁ p.1) = D.I * D.r * D.bigW := by
    rw [directoryWidth_value, hI, hr, hW]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hr.symm, ht, head_fits hfit⟩
  · change value (guessCountWord a b p.1) = D.nGB
    rw [guessCountWord_value, hG, nGuessBlocks, hN]
    by_cases ha : a = 0
    · simp only [ha, Nat.zero_mul, ↓reduceIte]
    · have hg : a * ((value p.1) ^ 2 + 1) ≠ 0 := Nat.mul_ne_zero ha (by omega)
      simp only [ha, hg, ↓reduceIte]
  · exact (iWord_value a b aM p.1).trans hI.symm
  · exact (widthTally_length a b w₀ w₁ p.1).trans hW.symm
  · exact (congrArg (fun j : ℕ => (2 : ℕ) ^ j) (hTally_length a b p.1)).trans hN.symm
  · exact hs.trans (off_start D).symm
  · change value (endWord a b aM r w₀ w₁ 1 p.1) = D.off secPrev
    rw [endWord_value, hs, hw, off_prev, startEnd, Nat.one_mul]
  · change value (endWord a b aM r w₀ w₁ 7 p.1) = D.off secGuess
    rw [endWord_value, hs, hw, off_guess, nextEnd, prevEnd, startEnd]
    ring

open Classical in
theorem _root_.P1ProgDir.progC14 {K : Type} (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
    (aM r w₀ w₁ t n₀ : ℕ) (D : ℕ → Dims) (tape : ∀ n, K ≃ Fin (D n).r) (kIn : K)
    (hI : ∀ n, n₀ ≤ n → (D n).I = bigCount a b aM n)
    (hN : ∀ n, n₀ ≤ n → (D n).N = laneCount a b n)
    (hr : ∀ n, n₀ ≤ n → (D n).r = r)
    (hW : ∀ n, n₀ ≤ n → (D n).bigW = w₀ + w₁ * lpK2 a b n)
    (hG : ∀ n, n₀ ≤ n → (D n).nGB = nGuessBlocks (a * (n ^ 2 + 1))
      (2 ^ (lpP2 a b n / 2) * (D n).N))
    (ht : ∀ n, n₀ ≤ n → t = (tape n kIn : ℕ))
    (hfit : ∀ n, n₀ ≤ n → (D n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
        ∀ (u : Fin (lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (C14F (D x.length) (tape x.length) kIn (fun q => ((q : ℕ) : ℤ))
              (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  apply checkProgram (fun x u i => C14F (D x.length) (tape x.length) kIn
    (fun q => ((q : ℕ) : ℤ)) u i)
  let X := Input s a b n₀
  let q (x : X) := raw x
  let n (x : X) := x.1.val.length
  let p (x : X) := (lengthHeader (q x)).1
  let u (x : X) := (q x).2.1
  let h (x : X) := header a b aM r w₀ w₁ (p x)
  have hu (x : X) : (u x).length = lpM2 s a b (n x) := List.length_ofFn
  have hn (x : X) : value (p x).1 = n x := birthValue _
  have hh (x : X) : SolC14Batch.Fits (D (n x)) r t (h x) (u x) := by
    have hx := x.1.property
    have htl : t < r := by
      rw [← hr _ hx, ht _ hx]
      exact (tape (n x) kIn).isLt
    exact header_fits _ _ _ _ _ _ _ _ _ _
      (by rw [hn]; exact hI _ hx) (by rw [hn]; exact hN _ hx) (hr _ hx)
      (by rw [hn]; exact hW _ hx) (by rw [hn]; exact hG _ hx) htl
      (by rw [hu]; exact hfit _ hx)
  obtain ⟨β, hβ, hc⟩ := SolSmallBatch.twice h u SolC14Batch.first
    (SolC14Batch.second r t) SolC14Batch.reply SolC14Batch.poly_first
    (SolC14Batch.poly_second r t) SolC14Batch.easy_reply.poly
    (SolC14Batch.first_total.map h)
    ((SolC14Batch.second_total r t).map (fun x => SolSmallBatch.readPlan SolC14Batch.first (h x) (u x)))
    (fun x => SolC14Batch.first_fits (hh x)) (fun x => SolC14Batch.second_fits (hh x))
  have hhead := poly_header a b aM r w₀ w₁
  have hsz := (Code.Poly.length hhead).map p
  obtain ⟨α, hα, hpre⟩ := hhead
  let θ (x : X) := α (p x) + β x
  have hθ : Dom (fun x => size (p x)) θ := (hα.map p).add (hβ.sub hsz)
  have hl := (easy_lengthHeader.on q).compose ((hpre.on p).left (fun x => send (u x)))
  have hrun := hl.compose hc
  have hsnd (x : X) : (q x).2.2.length ≤ lpK2 a b (n x) :=
    x.2.2.property ▸ Nat.sub_le _ _
  obtain ⟨A, hA⟩ := raw_poly_cost q s hs a b hb hu hsnd hθ
  refine (hrun.conform (fun x => ?_) (fun _ => rfl) (fun x => ?_)).bound A hA
  · change size (q x) + α (p x) + ((u x).length + β x) = size (q x) + (u x).length + θ x
    unfold θ
    omega
  · apply congrArg send
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    rw [P1Batch.bval_eq_value]
    exact SolC14Batch.reply_iff (tape (n x)) kIn (hh x) (ht _ x.1.property)

#print axioms P1ProgDir.progC14

end P1ProgDir.SolProgram14
