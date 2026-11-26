import P1ProgDir.DirFinal
import P1ProgDir.C4Genuine
import P1Int.ComposeFam

/-!
# P1ProgDir.FamDir: the programs of C1, C2, C3, C4, C14 in the form `P1Int.P11.FamProg` (integration layer 1.5)

Lane P1-lean-checks (2026-11-25), on the request of P1-lean-integ (board 12:46Z): each family program as
`FamProg letter answer Rc ck s a b cc n₂` with `ck := fun x u i => decide (CkF ..)`. The D8 shape of the Sol programs
(`4 * 4 + bnd ≤ lpCost2 c ..`, value `P1Batch.bval ρ`) gives it at once: `bnd ≤ lpCost2 c ..`, and
`P1Count.bval = P1Batch.bval` (`bval_count_eq`; the two lanes define the same LSB-first value).
-/

namespace P1ProgDir.FamDir

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int

theorem bval_count_eq (l : List Bool) : P1Count.bval l = P1Batch.bval l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [P1Count.bval, P1Batch.bval, ih]

/-- **The D8 shape of the check lanes gives `FamProg`.** -/
theorem famProg_of_D8 {s : ℝ} {a b n₀ : ℕ} {ck : List Bool → List Bool → ℕ → Bool}
    (h : ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
        ∀ (u : Fin (lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (ck x (List.ofFn u) (P1Batch.bval ρ)) bnd) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc ck s a b cc n₀ := by
  obtain ⟨Rc, c, hc⟩ := h
  refine ⟨Rc, c, fun x hx => ?_⟩
  obtain ⟨bnd, _, hle, hans⟩ := hc x hx
  refine ⟨bnd, by omega, fun u ρ hρ => ?_⟩
  rw [bval_count_eq]
  exact hans u ρ hρ

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
  (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)

open Classical

/-- Family 0 (C1) as `FamProg`, genuine dims. -/
theorem famC1 (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (DirFinal.gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → 2 * ((DirFinal.gD A Kc V aM a b d bigBias termBias n).I *
      (DirFinal.gD A Kc V aM a b d bigBias termBias n).N * (DirFinal.gD A Kc V aM a b d bigBias termBias n).r) ≤
        lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (P1ChkDir.C1F (DirFinal.gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) u i))
      s a b cc n₀ :=
  famProg_of_D8 (DirFinal.progC1_genuine A Kc V aM a b d bigBias termBias s hs hb n₀ tape hfit)

/-- Family 1 (C2) as `FamProg`, genuine dims. -/
theorem famC2 [NeZero (Fintype.card V.K)] (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (DirFinal.gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → (DirFinal.gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (P1ChkDir.C2F (DirFinal.gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) u i))
      s a b cc n₀ :=
  famProg_of_D8 (DirFinal.progC2_genuine A Kc V aM a b d bigBias termBias s hs hb n₀ tape hfit)

/-- Family 2 (C3) as `FamProg`, genuine dims. -/
theorem famC3 [NeZero (Fintype.card V.K)] (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (DirFinal.gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → (DirFinal.gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (P1ChkDir.C3F (DirFinal.gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) u i))
      s a b cc n₀ :=
  famProg_of_D8 (DirFinal.progC3_genuine A Kc V aM a b d bigBias termBias s hs hb n₀ tape hfit)

/-- Family 14 (C14) as `FamProg`, genuine dims. -/
theorem famC14 (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (t n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (DirFinal.gD A Kc V aM a b d bigBias termBias n).r) (kIn : V.K)
    (ht : ∀ n, n₀ ≤ n → t = (tape n kIn : ℕ))
    (hfit : ∀ n, n₀ ≤ n → (DirFinal.gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (P1ChkDir.C14F (DirFinal.gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) kIn
        (fun q => ((q : ℕ) : ℤ)) u i))
      s a b cc n₀ :=
  famProg_of_D8 (DirFinal.progC14_genuine A Kc V aM a b d bigBias termBias s hs hb t n₀ tape kIn ht hfit)

/-- Family 3 (C4) as `FamProg`, genuine dims, NO input (threshold 16). -/
theorem famC4 (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) {e : ℕ} (ha : 4 ≤ 2 ^ e) (τ : V.K → ℕ) :
    ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (P1ChkDir.C4w ha τ (genuineC4Dims A Kc V aM a b d bigBias termBias) x u i))
      s a b cc 16 := by
  obtain ⟨Rc, c, h⟩ := SolC4.progC4_D8 ha τ (genuineC4Dims A Kc V aM a b d bigBias termBias)
    (P1SolFmt.fmtHyp4_genuine A Kc V aM a b d bigBias termBias) s hs a b hb
  exact famProg_of_D8 ⟨Rc, c, h⟩

end P1ProgDir.FamDir

#print axioms P1ProgDir.FamDir.famC1
#print axioms P1ProgDir.FamDir.famC2
#print axioms P1ProgDir.FamDir.famC3
#print axioms P1ProgDir.FamDir.famC14
#print axioms P1ProgDir.FamDir.famC4
