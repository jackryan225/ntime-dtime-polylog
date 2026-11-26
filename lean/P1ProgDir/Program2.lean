import P1ProgDir.C2Batch
import P1ProgDir.Adapter
import P1ProgDir.Budget

namespace P1ProgDir.SolProgram2

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkDir P1Wit P1Int
open P1ProgDir.SolGeometry P1ProgDir.SolFrontWords P1ProgDir.SolFieldWords P1ProgDir.SolC2Trits
open P1ProgDir.SolAdapter P1ProgDir.SolBudget P1ProgDir.SolOffsets

def header (a b aM r w₀ w₁ : ℕ) (p : Word × Word) : SolC2Batch.Header :=
  ((p.2, blocksWord a b aM r p.1), startWord a b aM r p.1,
    widthTally a b w₀ w₁ p.1, laneTally a b p.1)

theorem poly_header (a b aM r w₀ w₁ : ℕ) : Poly (header a b aM r w₀ w₁) := by
  have hn : Poly (fun p : Word × Word => p.1) := Poly.identity.fstCompose
  exact (Poly.identity.sndCompose.pair (hn.compose (poly_blocksWord a b aM r))).pair
    ((hn.compose (poly_startWord a b aM r)).pair
      ((hn.compose (poly_widthTally a b w₀ w₁)).pair (hn.compose (poly_laneTally a b))))

set_option maxHeartbeats 1200000 in
theorem header_fits (a b aM r w₀ w₁ : ℕ) (D : Dims) (p : Word × Word) (w : Word)
    (hI : D.I = bigCount a b aM (value p.1))
    (hN : D.N = laneCount a b (value p.1)) (hr : D.r = r)
    (hW : D.bigW = w₀ + w₁ * lpK2 a b (value p.1)) (hfit : D.fixedLen ≤ w.length) :
    SolC2Batch.Fits D r (header a b aM r w₀ w₁ p) w := by
  refine ⟨?_, ?_, ?_, ?_, hr.symm, head_fits hfit⟩
  · change value (blocksWord a b aM r p.1) = _
    rw [blocksWord_value, hI, hr]
  · change value (startWord a b aM r p.1) = _
    rw [startWord_value, off_start, tritEnd, hI, hN, hr]
  · exact (widthTally_length a b w₀ w₁ p.1).trans hW.symm
  · change (tally (laneCount a b (value p.1))).length = _
    rw [tally_length, hN]

open Classical in
theorem _root_.P1ProgDir.progC2 {K : Type} (s : ℝ) (hs : s ≤ 1) (a b : ℕ) (hb : 1 ≤ b)
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
            (decide (C2F (D x.length) (tape x.length) (List.ofFn u) (P1Batch.bval ρ))) bnd := by
  apply checkProgram (fun x u i => C2F (D x.length) (tape x.length) u i)
  let X := Input s a b n₀
  let q (x : X) := raw x
  let n (x : X) := x.1.val.length
  let p (x : X) := (lengthHeader (q x)).1
  let u (x : X) := (q x).2.1
  let h (x : X) := header a b aM r w₀ w₁ (p x)
  have hu (x : X) : (u x).length = lpM2 s a b (n x) := List.length_ofFn
  have hn (x : X) : value (p x).1 = n x := birthValue _
  have hh (x : X) : SolC2Batch.Fits (D (n x)) r (h x) (u x) := by
    have hx := x.1.property
    exact header_fits _ _ _ _ _ _ _ _ _
      (by rw [hn]; exact hI _ hx) (by rw [hn]; exact hN _ hx) (hr _ hx)
      (by rw [hn]; exact hW _ hx) (by rw [hu]; exact hfit _ hx)
  obtain ⟨β, hβ, hc⟩ := SolSmallBatch.once h u (SolC2Batch.plan r)
    (SolC2Batch.reply r) (SolC2Batch.poly_plan r) (SolC2Batch.poly_reply r)
    ((SolC2Batch.total_dom r).map h) (fun x => SolC2Batch.plan_fits (hh x))
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
    exact SolC2Batch.reply_iff (tape (n x)) (hh x)

#print axioms P1ProgDir.progC2

end P1ProgDir.SolProgram2
