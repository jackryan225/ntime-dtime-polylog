import P1ChkDir.C14
import P1ChkDir.C4

/-!
# P1ChkDir.Stage: check C14 on the witness of lane P6, and the stage lemmas of the directory checks

Lane P1-lean-W2-chkdir. Stage order of decision D5: stage 0 = C1-C3 (`P1ChkDir.dirF_iff`), stage 1 = C14,
stage 2 = C4 (`P1ChkDir.C4_stage`). This file gives
* `guessP6 D kIn blk`: the guess section (section 4 of `P1Wit.Layout`: field `Q` at `D.off secGuess + Q * width`,
  owner code `optCode`, as the owner fields of the directory) as a `GuessDir`;
* `guessP6_gOwnS`: the stored guess owner is P6's `rdGuess` decoded;
* the family `C14F` of D5 (family 14, index `Q < D.nGB`), `C14F_out`, `C14F_iff`;
* `C14_stage`: once the directory is true, every C14 index passes iff every guess field holds the true LEAST
  owner and `P1Net.unownedCount = 0` (Challenge input `withGuess`, `D.nGB = nGuessBlocks g (B N)`, `2 ≤ B N`).
-/

namespace P1ChkDir

open P1Net P1Wit

variable {K : Type}

theorem width_guess (D : Dims) : D.width secGuess = D.bigW := by simp [Dims.width, Dims.kind, secGuess]

/-- The guess section of P6 (section 4) as a `GuessDir`: guess big block `Q < D.nGB` is big block `blk Q` of the
input tape `kIn`. -/
def guessP6 (D : Dims) (kIn : K) (blk : Fin D.nGB → ℤ) : GuessDir K D.nGB where
  kIn := kIn
  blk := blk
  off q := D.off secGuess + (q : ℕ) * D.width secGuess

theorem guessP6_gOwnS (D : Dims) (ρ : K ≃ Fin D.r) (kIn : K) (blk : Fin D.nGB → ℤ) (u : List Bool)
    (q : Fin D.nGB) : gOwnS (dirP6 D ρ) (guessP6 D kIn blk) u q = ownOfN D.I (rdGuess D u q) := by
  simp only [gOwnS, dirP6, guessP6, ownCode, numCode_read, rdGuess, readField, width_guess]

/-- Family 14 of D5, **C14**: index `Q < D.nGB`. -/
def C14F (D : Dims) (ρ : K ≃ Fin D.r) (kIn : K) (blk : Fin D.nGB → ℤ) (u : List Bool) (i : ℕ) : Prop :=
  ∀ h : i < D.nGB, C14 (dirP6 D ρ) (guessP6 D kIn blk) u ⟨i, h⟩

theorem C14F_out (D : Dims) (ρ : K ≃ Fin D.r) (kIn : K) (blk : Fin D.nGB → ℤ) (u : List Bool) {i : ℕ}
    (hi : D.nGB ≤ i) : C14F D ρ kIn blk u i := fun h => absurd h (by omega)

theorem C14F_iff (D : Dims) (ρ : K ≃ Fin D.r) (kIn : K) (blk : Fin D.nGB → ℤ) (u : List Bool) :
    (∀ i, C14F D ρ kIn blk u i) ↔ ∀ q, C14 (dirP6 D ρ) (guessP6 D kIn blk) u q :=
  ⟨fun hF q => hF q q.isLt, fun hC _ _ => hC _⟩

section Challenge

open OAI.DepthThreeLowerBound

variable {M : FiniteMultiTapeMachine} {B : ℕ} [NeZero B] {g : ℕ}

/-- `covers_withGuess` for a block count `n` that EQUALS `nGuessBlocks g (B N)`. -/
theorem covers_withGuess' (x : List Bool) {N n : ℕ} (hP : 2 ≤ B * N) (hn : n = nGuessBlocks g (B * N))
    (off : Fin n → ℕ) :
    (⟨M.inputTape, fun q => ((q : ℕ) : ℤ), off⟩ : GuessDir M.K n).Covers (withGuessLayout (M := M) x g) B N := by
  subst hn
  exact covers_withGuess x hP off

/-- **Stage 1 (C14) of `P1Count.stages_iff`, Challenge input.** Once C1-C3 pass (the directory of the P6 witness is
true), every index of family C14 passes iff every guess field holds the true least owner and no guess cell is
unowned (`P1Net.unownedCount = 0`, the exponent of the routed scalar). -/
theorem C14_stage (x : List Bool) (D : Dims) [NeZero (D.I * D.N)] (hP : 2 ≤ B * D.N)
    (hn : D.nGB = nGuessBlocks g (B * D.N)) (ρ : M.K ≃ Fin D.r) (u : List Bool) (hDir : DirTrue (dirP6 D ρ) u) :
    (∀ i, C14F D ρ M.inputTape (fun q => ((q : ℕ) : ℤ)) u i) ↔
      (∀ q, gOwnS (dirP6 D ρ) (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)) u q =
          some (gOwnT (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)) D.N ((dirP6 D ρ).sigmaS u) q)) ∧
        unownedCount (B := B) (withGuessLayout (M := M) x g) ((dirP6 D ρ).sigmaS u) D.N D.I = 0 := by
  have hcov : (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)).Covers (withGuessLayout (M := M) x g) B D.N :=
    covers_withGuess' x hP hn _
  have hβ := hDir.2.1
  have hprev : ∀ ι k δ, (dirP6 D ρ).prevS u ι k δ = some (prevT D.N ((dirP6 D ρ).sigmaS u) ι k δ) :=
    fun ι k δ => (hDir.2.2 ι k δ).2
  rw [C14F_iff, ← owned_iff_unownedCount _ _ hcov]
  constructor
  · intro hC
    exact C14_unique _ _ u _ hβ hprev hC
  · rintro ⟨hg, hown⟩
    exact C14_true _ _ u _ hβ hprev hg hown

end Challenge

end P1ChkDir
