import P1ProgDir.Program1
import P1ProgDir.Program2
import P1ProgDir.Program3
import P1ProgDir.Program14
import P1ProgDir.C4Final
import P1Wit.SpaceFacts

/-!
# P1ProgDir.DirFinal: the programs of C1, C2, C3, C14 (Sol P1-sol-progdir) at the GENUINE dims

Lane P1-lean-checks (2026-11-25). The four delivered theorems `P1ProgDir.progC1`, `progC2`, `progC3`, `progC14`
(files P1ProgDir/Program{1,2,3,14}.lean and their 29 helper files, copied UNCHANGED from
research/agents/P1-sol-progdir/lean/, sha256 = DONE.md of round 1) have the D8 shape accepted by the owner (board 11:52Z):
one program `Rc` and one constant `c`; for `n₀ ≤ |x|` a bound `bnd` with `1 ≤ bnd`, `4 * 4 + bnd ≤ lpCost2 c s a b |x|`;
for every witness `u` of length `lpM2 s a b |x|` and every selector of length `lpK2 a b |x| - 4` the program answers
`decide (CkF ..)` within `bnd`. Their only hypotheses are equalities and inequalities on the numbers of `D`.

NON-VACUITY (this file): the equalities `hI`, `hN`, `hr`, `hW`, `hG` hold for the genuine dims of Lemma P
(`P1Wit.SolSpace.genuineDims` at `t = lpTime a b n`, `g = a (n^2 + 1)`) BY DEFINITION (`rfl`); so at the genuine dims
the four programs need only the fit `hfit` (the witness length, P1-lean-integ's `witness_fits`), the tape numbering and
(for C14) one constant tape index of the input tape.
-/

namespace P1ProgDir.DirFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1Int

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
  (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)

/-- The genuine dims at input length `n`. -/
noncomputable abbrev gD (n : ℕ) : Dims :=
  genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias

theorem genuine_I (n : ℕ) : (gD A Kc V aM a b d bigBias termBias n).I = SolGeometry.bigCount a b aM n := rfl

theorem genuine_N (n : ℕ) : (gD A Kc V aM a b d bigBias termBias n).N = SolGeometry.laneCount a b n := rfl

theorem genuine_r (n : ℕ) : (gD A Kc V aM a b d bigBias termBias n).r = Fintype.card V.K := rfl

theorem genuine_bigW (n : ℕ) :
    (gD A Kc V aM a b d bigBias termBias n).bigW = bigBias + 6 * P1Int.lpK2 a b n := rfl

theorem genuine_nGB (n : ℕ) :
    (gD A Kc V aM a b d bigBias termBias n).nGB = P1ChkDir.nGuessBlocks (a * (n ^ 2 + 1))
      (2 ^ (P1Int.lpP2 a b n / 2) * (gD A Kc V aM a b d bigBias termBias n).N) := rfl

open Classical

/-- **C1 (family 0) at the genuine dims**: only the fit of the trit section and the tape numbering stay. -/
theorem progC1_genuine (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → 2 * ((gD A Kc V aM a b d bigBias termBias n).I *
      (gD A Kc V aM a b d bigBias termBias n).N * (gD A Kc V aM a b d bigBias termBias n).r) ≤ P1Int.lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ P1Int.lpCost2 c s a b x.length ∧
        ∀ (u : Fin (P1Int.lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = P1Int.lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (P1ChkDir.C1F (gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) (List.ofFn u)
              (P1Batch.bval ρ))) bnd :=
  P1ProgDir.progC1 s hs a b hb aM (Fintype.card V.K) n₀ _ tape
    (fun n _ => genuine_I A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_N A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_r A Kc V aM a b d bigBias termBias n) hfit

/-- **C2 (family 1) at the genuine dims.** -/
theorem progC2_genuine [NeZero (Fintype.card V.K)] (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → (gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ P1Int.lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ P1Int.lpCost2 c s a b x.length ∧
        ∀ (u : Fin (P1Int.lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = P1Int.lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (P1ChkDir.C2F (gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) (List.ofFn u)
              (P1Batch.bval ρ))) bnd :=
  P1ProgDir.progC2 s hs a b hb aM (Fintype.card V.K) bigBias 6 n₀ _ tape
    (fun n _ => genuine_I A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_N A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_r A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_bigW A Kc V aM a b d bigBias termBias n) hfit

/-- **C3 (family 2) at the genuine dims.** -/
theorem progC3_genuine [NeZero (Fintype.card V.K)] (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (gD A Kc V aM a b d bigBias termBias n).r)
    (hfit : ∀ n, n₀ ≤ n → (gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ P1Int.lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ P1Int.lpCost2 c s a b x.length ∧
        ∀ (u : Fin (P1Int.lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = P1Int.lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (P1ChkDir.C3F (gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) (List.ofFn u)
              (P1Batch.bval ρ))) bnd :=
  P1ProgDir.progC3 s hs a b hb aM (Fintype.card V.K) bigBias 6 n₀ _ tape
    (fun n _ => genuine_I A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_N A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_r A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_bigW A Kc V aM a b d bigBias termBias n) hfit

/-- **C14 (family 14) at the genuine dims**: plus one constant index `t` of the input tape `kIn`. -/
theorem progC14_genuine (s : ℝ) (hs : s ≤ 1) (hb : 1 ≤ b) (t n₀ : ℕ)
    (tape : ∀ n, V.K ≃ Fin (gD A Kc V aM a b d bigBias termBias n).r) (kIn : V.K)
    (ht : ∀ n, n₀ ≤ n → t = (tape n kIn : ℕ))
    (hfit : ∀ n, n₀ ≤ n → (gD A Kc V aM a b d bigBias termBias n).fixedLen ≤ P1Int.lpM2 s a b n) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, n₀ ≤ x.length →
      ∃ bnd, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ P1Int.lpCost2 c s a b x.length ∧
        ∀ (u : Fin (P1Int.lpM2 s a b x.length) → Bool) (ρ : List Bool),
          ρ.length = P1Int.lpK2 a b x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (P1ChkDir.C14F (gD A Kc V aM a b d bigBias termBias x.length) (tape x.length) kIn
              (fun q => ((q : ℕ) : ℤ)) (List.ofFn u) (P1Batch.bval ρ))) bnd :=
  P1ProgDir.progC14 s hs a b hb aM (Fintype.card V.K) bigBias 6 t n₀ _ tape kIn
    (fun n _ => genuine_I A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_N A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_r A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_bigW A Kc V aM a b d bigBias termBias n)
    (fun n _ => genuine_nGB A Kc V aM a b d bigBias termBias n) ht hfit

end P1ProgDir.DirFinal

#print axioms P1ProgDir.progC1
#print axioms P1ProgDir.progC2
#print axioms P1ProgDir.progC3
#print axioms P1ProgDir.progC14
#print axioms P1ProgDir.progC4
#print axioms P1ProgDir.DirFinal.progC1_genuine
#print axioms P1ProgDir.DirFinal.progC2_genuine
#print axioms P1ProgDir.DirFinal.progC3_genuine
#print axioms P1ProgDir.DirFinal.progC14_genuine
