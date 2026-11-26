import P1ChkDir.Stage
import P1ChkDir.C4Wired

/-!
# P1ChkDir.D5Steps: the steps `c14` and `c4` of the integration's `P1Int.P11.D5Steps`, in its shape

Lane P1-lean-checks (2026-11-25), on the request of P1-lean-integ (board 13:05Z), in the form of integ's
`P1Int.P11.d5_dir_step` (ComposeDir.lean): for a family decision `ck` that is the check of this lane on the bit list
`w u`, and counts that fit into the `ni` index words,
`(earlier group true) → ((∀ i < ni, i < cnt → ck u i = true) ↔ group predicate)`.

* group `c14` (family 14): predicate = RHS of `P1ChkDir.C14_stage` (guess fields = least owners and
  `unownedCount = 0`); earlier group: `DirTrue (dirP6 D ρ) (w u)`; count `D.nGB`.
* group `c4` (family 3): predicate = every level-0 panel field holds the true panel of `stateNet I σ(w u)`
  (RHS of `P1ChkDir.C4_stage`); earlier group: `DirTrue L (w u)` (for the layout `dirAt` of `C4w`, from the `dir`
  group by `dirTrue_dirAt`); count `2 * (I * locCount K h)` (= `cnt4`).
-/

namespace P1ChkDir

open P1Net P1Wit OAI.DepthThreeLowerBound

/-- **Step `c14`.** -/
theorem d5_c14_step {M : FiniteMultiTapeMachine} {B : ℕ} [NeZero B] {g : ℕ} (x : List Bool) (D : Dims)
    [NeZero (D.I * D.N)] (hP : 2 ≤ B * D.N) (hn : D.nGB = nGuessBlocks g (B * D.N)) (ρ : M.K ≃ Fin D.r)
    (ni cnt : ℕ) (hc : cnt = D.nGB) (hni : D.nGB ≤ ni)
    {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool)
    (hck : ∀ u i, ck u i = true ↔ C14F D ρ M.inputTape (fun q => ((q : ℕ) : ℤ)) (w u) i)
    (u : U) (hDir : DirTrue (dirP6 D ρ) (w u)) :
    (∀ i < ni, i < cnt → ck u i = true) ↔
      ((∀ q, gOwnS (dirP6 D ρ) (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)) (w u) q =
          some (gOwnT (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)) D.N ((dirP6 D ρ).sigmaS (w u)) q)) ∧
        unownedCount (B := B) (withGuessLayout (M := M) x g) ((dirP6 D ρ).sigmaS (w u)) D.N D.I = 0) := by
  rw [← C14_stage x D hP hn ρ (w u) hDir]
  subst hc
  constructor
  · intro h i
    by_cases hi : i < D.nGB
    · exact (hck u i).1 (h i (by omega) hi)
    · exact C14F_out D ρ M.inputTape _ (w u) (by omega)
  · intro h i _ _
    exact (hck u i).2 (h i)

variable {K : Type} [Fintype K] [DecidableEq K]

/-- **Step `c4`.** -/
theorem d5_c4_step {a h I : ℕ} [NeZero I] (ha : 4 ≤ 2 ^ a) (D : Dims) (L : DirLayout K I (2 ^ h))
    (Wc Ws Wt ni cnt : ℕ) (hc : cnt = 2 * (I * locCount K h)) (hni : 2 * (I * locCount K h) ≤ ni)
    {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool)
    (hck : ∀ u i, ck u i = true ↔ C4F ha D L (w u) Wc Ws Wt i)
    (u : U) (hDir : DirTrue L (w u)) :
    (∀ i < ni, i < cnt → ck u i = true) ↔
      ∀ y, PanelStored D (w u) (addrL y) (P1P7.panel (stateNet (K := K) I (L.sigmaS (w u)) ha Wc Ws Wt) y) := by
  rw [← C4_stage ha D L (w u) Wc Ws Wt hDir]
  subst hc
  constructor
  · intro hall i
    by_cases hi : i < 2 * (I * locCount K h)
    · exact (hck u i).1 (hall i (by omega) hi)
    · exact C4F_out ha D L (w u) Wc Ws Wt (by omega)
  · intro hall i _ _
    exact (hck u i).2 (hall i)

/-- **Step `c4` for the wired family `C4w`** (the program's family, `P1ProgDir.progC4`): the directory group of
`dirP6 D ρ` gives the earlier group of the layout `dirAt D τ D.I (2 ^ h)` when `D.N = 2 ^ h` and `τ = ρ`. -/
theorem d5_c4w_step {a : ℕ} (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (x : List Bool)
    [NeZero (dims x.length).D.I] (ρ : K ≃ Fin (dims x.length).D.r) (hτ : ∀ k, (ρ k : ℕ) = τ k)
    (hN : (dims x.length).D.N = 2 ^ (dims x.length).h)
    (ni cnt : ℕ) (hc : cnt = cnt4 K dims x.length) (hni : cnt4 K dims x.length ≤ ni)
    {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool)
    (hck : ∀ u i, ck u i = true ↔ C4w ha τ dims x (w u) i)
    (u : U) (hDir : DirTrue (dirP6 (dims x.length).D ρ) (w u)) :
    (∀ i < ni, i < cnt → ck u i = true) ↔
      ∀ y, PanelStored (dims x.length).D (w u) (addrL y)
        (P1P7.panel (stateNet (K := K) (dims x.length).D.I
          ((dirAt (dims x.length).D τ (dims x.length).D.I (2 ^ (dims x.length).h)).sigmaS (w u))
          ha (dims x.length).Wc (dims x.length).Ws (dims x.length).Wt) y) :=
  d5_c4_step ha (dims x.length).D _ _ _ _ ni cnt hc hni w ck hck u
    (dirTrue_dirAt _ ρ τ hτ hN (w u) hDir)

end P1ChkDir

#print axioms P1ChkDir.d5_c14_step
#print axioms P1ChkDir.d5_c4_step
#print axioms P1ChkDir.d5_c4w_step
