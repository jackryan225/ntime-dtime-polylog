import P1Net.Count
import P1ChkDir.Basic

/-!
# P1ChkDir.C14: the witness check C14 (every guess cell lies in an owned big block)

Lane P1-lean-W2-chkdir (brief `ORG/briefs/P1-lean-W2-chkdir.md`). Check C14 comes from lane net B
(`P1Net.unownedCount`, `research/p1/lean/Net/P1Net/Count.lean`): the routed network carries the scalar `2 ^ u`
with `u = unownedCount`, the number of guess cells in big blocks that no big interval owns. Over `F_2` a skeleton
with `u > 0` contributes an even count, so the verifier rejects it: C14 asks that every guess big block has an
owner. (Hand-over `ORG/winddown/HANDOVER-P1.md` section 4, "C14 and the scalar".)

The witness stores, for each guess big block `q < nQ` (big block `blk q` of the input tape `kIn`), the LEAST big
interval that owns it (P6 section `guessOwner`, owner code `cO` of the directory). The check is local: 3 reads.
* `C14 D G u q`: the stored owner `ι` of block `q` has a stored start block `b` with `blk q = ⌊b / N⌋ - 1 + δ`,
  and the stored PREVIOUS owner of the directory field `(ι, kIn, δ)` is `none`.
Once C2 and C3 hold (the directory is the true one), `prev = none` says that no `j < ι` owns `blk q`, so the
stored owner is the least owner (`C14_iff`); this gives uniqueness of the witness.

Index set. The stored blocks must be EXACTLY the big blocks that contain a guess cell (`GuessDir.Covers`): a block
without a guess cell must not be checked (C14 would then reject skeletons with `u = 0` and break the count).
For the Challenge input `withGuess` (guess cell `j` at input cell `2 j + 1`) and `2 ≤ B N`, these are the blocks
`0, ..., (2 g - 1) / (B N)` (`covers_withGuess`). Note: the block of the separator cell `2 g` is NOT among them
when `B N` divides `2 g`.

Results: `C14_iff`, `C14_true`, `C14_unique`, `C14_unique_bits`; link to the count: `owned_iff_unownedCount`
(general layout) and `C14_iff_unownedCount_withGuess` (the Challenge layout).
-/

namespace P1ChkDir

open P1Net

variable {K : Type} {I N : ℕ}

/-! ## Scans -/

/-- The least `j` that owns `Q` according to `β`, or `none`. -/
def leastScan (β : Fin I → Option ℤ) (N : ℕ) (Q : ℤ) : Option (Fin I) :=
  if hS : (Finset.univ.filter fun j : Fin I => ownsTab β N j Q = true).Nonempty then
    some ((Finset.univ.filter fun j : Fin I => ownsTab β N j Q = true).min' hS)
  else none

theorem leastScan_eq_some_iff (β : Fin I → Option ℤ) (N : ℕ) (Q : ℤ) (ι : Fin I) :
    leastScan β N Q = some ι ↔ ownsTab β N ι Q = true ∧ ∀ j < ι, ownsTab β N j Q = false := by
  unfold leastScan
  split_ifs with hS
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      have hm := Finset.min'_mem _ hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      refine ⟨hm, fun j hj => ?_⟩
      by_contra hc
      have hc' : ownsTab β N j Q = true := by simpa using hc
      have hjm : j ∈ (Finset.univ.filter fun j : Fin I => ownsTab β N j Q = true) := by simpa using hc'
      exact absurd (Finset.min'_le _ _ hjm) (not_le.2 hj)
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ (by simpa using h1)
      · apply Finset.le_min'
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_contra hc
        rw [not_le] at hc
        rw [h2 j hc] at hj
        exact Bool.false_ne_true hj
  · constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h1, -⟩
      exact (hS ⟨ι, by simpa using h1⟩).elim

theorem leastScan_ne_none_iff (β : Fin I → Option ℤ) (N : ℕ) (Q : ℤ) :
    leastScan β N Q ≠ none ↔ ∃ j, ownsTab β N j Q = true := by
  unfold leastScan
  split_ifs with hS
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    obtain ⟨j, hj⟩ := hS
    exact ⟨j, by simpa using hj⟩
  · simp only [ne_eq, eq_self_iff_true, not_true_eq_false, false_iff, not_exists]
    intro j hj
    exact hS ⟨j, by simpa using hj⟩

theorem prevScan_eq_none_iff (β : Fin I → Option ℤ) (N : ℕ) (ι : Fin I) (Q : ℤ) :
    prevScan β N ι Q = none ↔ ∀ j < ι, ownsTab β N j Q = false := by
  unfold prevScan
  split_ifs with hS
  · constructor
    · intro h
      exact absurd h (by simp)
    · intro h
      exfalso
      obtain ⟨j, hj⟩ := hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have h2 := hj.2
      rw [h j hj.1] at h2
      exact Bool.false_ne_true h2
  · refine ⟨fun _ j hj => ?_, fun _ => rfl⟩
    by_contra hc
    have hc' : ownsTab β N j Q = true := by simpa using hc
    exact hS ⟨j, by simp [hj, hc']⟩

/-- `ι` is the least owner of `Q` (true table) iff some window `δ` of `ι` is `Q` and the true previous owner of the
directory field `(ι, k, δ)` is `none`. -/
theorem leastScan_iff_prevT {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (Q : ℤ) (ι : Fin I) :
    leastScan (betaTab N σ k) N Q = some ι ↔
      ∃ δ : Fin 3, Q = bigOf N (betaT N σ ι k) - 1 + (δ : ℤ) ∧ prevT N σ ι k δ = none := by
  rw [leastScan_eq_some_iff, ownsTab_betaTab, ownsB_iff]
  constructor
  · rintro ⟨⟨δ, hδ⟩, h2⟩
    refine ⟨δ, hδ, ?_⟩
    unfold prevT
    rw [prevScan_eq_none_iff]
    have hq : portQT N σ (ι : ℕ) k δ = Q := by unfold portQT; rw [hδ]
    rw [hq]
    exact h2
  · rintro ⟨δ, hδ, hp⟩
    refine ⟨⟨δ, hδ⟩, ?_⟩
    unfold prevT at hp
    rw [prevScan_eq_none_iff] at hp
    have hq : portQT N σ (ι : ℕ) k δ = Q := by unfold portQT; rw [hδ]
    rw [hq] at hp
    exact hp

/-! ## The guess part of the directory and the check C14 -/

/-- The guess part of the directory (P6 section `guessOwner`): the input tape `kIn`; for each guess big block
`q < nQ` its number `blk q` on tape `kIn` and the offset `off q` of its owner field (code `cO`). -/
structure GuessDir (K : Type) (nQ : ℕ) where
  kIn : K
  blk : Fin nQ → ℤ
  off : Fin nQ → ℕ

variable {nQ : ℕ} (D : DirLayout K I N) (G : GuessDir K nQ) (u : List Bool)

/-- The stored owner of guess big block `q`. -/
def gOwnS (q : Fin nQ) : Option (Option (Fin I)) := D.cO.read u (G.off q)

/-- The true owner of guess big block `q`: the least big interval whose true start block owns it. -/
def gOwnT (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (q : Fin nQ) : Option (Fin I) :=
  leastScan (betaTab N σ G.kIn) N (G.blk q)

/-- **C14** at guess big block `q`: the stored owner `ι` has a stored start block `b` on the input tape with
`blk q = ⌊b / N⌋ - 1 + δ`, and the stored previous owner of the directory field `(ι, kIn, δ)` is `none`. -/
def C14 (q : Fin nQ) : Prop :=
  ∃ ι : Fin I, ∃ b : ℤ, ∃ δ : Fin 3, gOwnS D G u q = some (some ι) ∧ D.betaS u ι G.kIn = some b ∧
    G.blk q = bigOf N b - 1 + (δ : ℤ) ∧ D.prevS u ι G.kIn δ = some none

/-- **C14, exact form.** If the start-block fields and the previous-owner fields hold the true values for `σ`
(what C2 and C3 give), C14 at `q` holds iff the owner field of `q` holds the true least owner and that owner
exists. -/
theorem C14_iff {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ)) (q : Fin nQ) :
    C14 D G u q ↔ gOwnS D G u q = some (gOwnT G N σ q) ∧ gOwnT (I := I) G N σ q ≠ none := by
  constructor
  · rintro ⟨ι, b, δ, h1, h2, h3, h4⟩
    rw [hβ, Option.some.injEq] at h2
    subst h2
    rw [hprev, Option.some.injEq] at h4
    have hl : gOwnT G N σ q = some ι := (leastScan_iff_prevT (N := N) σ G.kIn (G.blk q) ι).2 ⟨δ, h3, h4⟩
    rw [hl]
    exact ⟨h1, by simp⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨ι, hι⟩ := Option.ne_none_iff_exists'.1 h2
    obtain ⟨δ, hδ, hp⟩ := (leastScan_iff_prevT (N := N) σ G.kIn (G.blk q) ι).1 hι
    refine ⟨ι, betaT N σ ι G.kIn, δ, ?_, hβ ι G.kIn, hδ, ?_⟩
    · rw [h1]
      exact congrArg some hι
    · rw [hprev, hp]

/-- **C14, soundness.** True directory, true owner fields, and every guess block owned: every C14 instance
passes. -/
theorem C14_true {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ))
    (hg : ∀ q, gOwnS D G u q = some (gOwnT G N σ q))
    (hown : ∀ q, ∃ ι : Fin I, OwnsB N (betaT N σ ι G.kIn) (G.blk q)) :
    ∀ q, C14 D G u q := by
  intro q
  refine (C14_iff D G u σ hβ hprev q).2 ⟨hg q, ?_⟩
  obtain ⟨ι, hι⟩ := hown q
  exact (leastScan_ne_none_iff _ _ _).2 ⟨ι, (ownsTab_betaTab N σ G.kIn ι (G.blk q)).2 hι⟩

/-- **C14, uniqueness.** True directory and every C14 instance passes: every owner field holds the true least
owner, and every guess block is owned. -/
theorem C14_unique {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ)) (hC : ∀ q, C14 D G u q) :
    (∀ q, gOwnS D G u q = some (gOwnT G N σ q)) ∧
      ∀ q, ∃ ι : Fin I, OwnsB N (betaT N σ ι G.kIn) (G.blk q) := by
  refine ⟨fun q => ((C14_iff D G u σ hβ hprev q).1 (hC q)).1, fun q => ?_⟩
  obtain ⟨ι, hι⟩ := (leastScan_ne_none_iff _ _ _).1 ((C14_iff D G u σ hβ hprev q).1 (hC q)).2
  exact ⟨ι, (ownsTab_betaTab N σ G.kIn ι (G.blk q)).1 hι⟩

/-- C14 uniqueness at the bit level: every owner field is the code of the true least owner. -/
theorem C14_unique_bits {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ)) (hC : ∀ q, C14 D G u q) :
    ∀ q, field u (G.off q) D.cO.w = D.cO.enc (gOwnT G N σ q) :=
  fun q => ((D.cO.read_eq_some).1 ((C14_unique D G u σ hβ hprev hC).1 q)).2

/-- **C1-C3 and C14 from the checks alone**: if every instance of C1, C2, C3 and C14 passes, the owner fields of
the guess blocks hold the true least owners for the stored skeleton, and every guess block is owned. -/
theorem C14_of_checks (hC1 : ∀ i k, C1 D u i k) (hC2 : ∀ ι k, C2 D u ι k)
    (hC3 : ∀ ι k δ nx, C3 D u ι k δ nx) (hC : ∀ q, C14 D G u q) :
    (∀ q, gOwnS D G u q = some (gOwnT G N (D.sigmaS u) q)) ∧
      ∀ q, ∃ ι : Fin I, OwnsB N (betaT N (D.sigmaS u) ι G.kIn) (G.blk q) := by
  obtain ⟨-, hβ, hown⟩ := dir_unique D u hC1 hC2 hC3
  exact C14_unique D G u (D.sigmaS u) hβ (fun ι k δ => (hown ι k δ).2) hC

/-! ## Link to the count (lane net B, `P1Net.unownedCount`) -/

section Net

open OAI.DepthThreeLowerBound

variable {M : FiniteMultiTapeMachine} {B : ℕ} [NeZero B] {g : ℕ} [NeZero (I * N)]

/-- The stored guess blocks are exactly the big blocks (of `B N` cells) of the guess cells, all on tape `kIn`. -/
structure GuessDir.Covers (G : GuessDir M.K nQ) (L : GuessLayout M g) (B N : ℕ) : Prop where
  tape : ∀ j, (L.cellOf j).1 = G.kIn
  cover : ∀ j, ∃ q, G.blk q = (L.cellOf j).2 / B / N
  hit : ∀ q, ∃ j, (L.cellOf j).2 / B / N = G.blk q

/-- **C14 is the check `unownedCount = 0`.** If the stored guess blocks are exactly the blocks of the guess
cells, every guess block has an owner iff no guess cell is unowned (`P1Net.unownedCount`). -/
theorem owned_iff_unownedCount (L : GuessLayout M g) (G : GuessDir M.K nQ) (hG : G.Covers L B N)
    (σ : Fin (I * N) → M.K → Fin 3) :
    (∀ q, ∃ ι : Fin I, OwnsB N (betaT N σ ι G.kIn) (G.blk q)) ↔ unownedCount (B := B) L σ N I = 0 := by
  rw [unownedCount_eq_zero_iff]
  constructor
  · intro h j
    obtain ⟨q, hq⟩ := hG.cover j
    obtain ⟨ι, hι⟩ := h q
    obtain ⟨δ, hδ⟩ := (ownsB_iff _ _ _).1 hι
    refine ⟨(ι : ℕ), ι.isLt, δ, ?_⟩
    rw [hG.tape j, ← hq, hδ]
    simp only [bigOf, betaT]
    ring
  · intro h q
    obtain ⟨j, hj⟩ := hG.hit q
    obtain ⟨ι, hιI, δ, hδ⟩ := h j
    refine ⟨⟨ι, hιI⟩, (ownsB_iff _ _ _).2 ⟨δ, ?_⟩⟩
    rw [← hj, hδ, hG.tape j]
    simp only [bigOf, betaT, Fin.val_mk]
    ring

/-- **C14 exactly rejects the skeletons with a nonzero scalar exponent.** With a true directory for `σ` and true
owner fields: every C14 instance passes iff `unownedCount = 0`. -/
theorem C14_iff_unownedCount (L : GuessLayout M g) (D : DirLayout M.K I N) (G : GuessDir M.K nQ)
    (hG : G.Covers L B N) (u : List Bool) (σ : Fin (I * N) → M.K → Fin 3)
    (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ))
    (hg : ∀ q, gOwnS D G u q = some (gOwnT G N σ q)) :
    (∀ q, C14 D G u q) ↔ unownedCount (B := B) L σ N I = 0 := by
  rw [← owned_iff_unownedCount L G hG σ]
  constructor
  · intro hC
    exact (C14_unique D G u σ hβ hprev hC).2
  · intro hown
    exact C14_true D G u σ hβ hprev hg hown

/-! ### The Challenge input `withGuess` -/

/-- Number of guess big blocks of `withGuess` (blocks of `P = B N` cells; guess cell `j` at cell `2 j + 1`). -/
def nGuessBlocks (g P : ℕ) : ℕ := if g = 0 then 0 else (2 * g - 1) / P + 1

/-- The guess part of the directory for `withGuess`: block `q` is big block `q` of the input tape. -/
def guessDirWithGuess (M : FiniteMultiTapeMachine) (g P : ℕ) (off : Fin (nGuessBlocks g P) → ℕ) :
    GuessDir M.K (nGuessBlocks g P) where
  kIn := M.inputTape
  blk q := (q : ℕ)
  off := off

theorem cell_block (j B N : ℕ) :
    (2 * (j : ℤ) + 1) / (B : ℤ) / (N : ℤ) = (((2 * j + 1) / (B * N) : ℕ) : ℤ) := by
  have h1 : (2 * (j : ℤ) + 1) = ((2 * j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, ← Int.natCast_ediv, ← Int.natCast_ediv, Nat.div_div_eq_div_mul]

/-- For `withGuess` and `2 ≤ B N`, the blocks `0, ..., (2 g - 1) / (B N)` are exactly the blocks of guess cells. -/
theorem withGuess_cell (x : List Bool) (j : Fin g) :
    ((withGuessLayout (M := M) x g).cellOf j).2 = 2 * ((j : ℕ) : ℤ) + 1 := rfl

theorem covers_withGuess (x : List Bool) (hP : 2 ≤ B * N) (off : Fin (nGuessBlocks g (B * N)) → ℕ) :
    (guessDirWithGuess M g (B * N) off).Covers (withGuessLayout (M := M) x g) B N where
  tape _ := rfl
  cover j := by
    have hg : g ≠ 0 := by have := j.isLt; omega
    have hlt : (2 * (j : ℕ) + 1) / (B * N) < nGuessBlocks g (B * N) := by
      simp only [nGuessBlocks, hg, ↓reduceIte]
      have : (2 * (j : ℕ) + 1) / (B * N) ≤ (2 * g - 1) / (B * N) :=
        Nat.div_le_div_right (by have := j.isLt; omega)
      omega
    refine ⟨⟨(2 * (j : ℕ) + 1) / (B * N), hlt⟩, ?_⟩
    rw [withGuess_cell, cell_block]
    rfl
  hit q := by
    have hq := q.isLt
    have hg : g ≠ 0 := by
      intro h0
      simp [nGuessBlocks, h0] at hq
    have hq' : (q : ℕ) ≤ (2 * g - 1) / (B * N) := by
      simp only [nGuessBlocks, hg, ↓reduceIte] at hq
      omega
    have hqP : (q : ℕ) * (B * N) ≤ 2 * g - 1 :=
      le_trans (Nat.mul_le_mul_right _ hq') (Nat.div_mul_le_self _ _)
    -- the odd cell `c` of block `q`
    obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ : ∃ c, (q : ℕ) * (B * N) ≤ c ∧ c < ((q : ℕ) + 1) * (B * N) ∧
        c % 2 = 1 ∧ c ≤ 2 * g - 1 ∧ 0 < c := by
      rw [Nat.add_mul, Nat.one_mul]
      rcases Nat.even_or_odd ((q : ℕ) * (B * N)) with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨(q : ℕ) * (B * N) + 1, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨(q : ℕ) * (B * N), le_refl _, by omega, by omega, hqP, by omega⟩
    have hj : (c - 1) / 2 < g := by omega
    refine ⟨⟨(c - 1) / 2, hj⟩, ?_⟩
    rw [withGuess_cell, cell_block]
    show (((2 * ((c - 1) / 2) + 1) / (B * N) : ℕ) : ℤ) = (((q : ℕ) : ℤ))
    have hc : 2 * ((c - 1) / 2) + 1 = c := by omega
    rw [hc, Nat.div_eq_of_lt_le hc1 hc2]

/-- **C14 for the Challenge input.** Directory and guess-owner fields true for `σ`, `2 ≤ B N`: every C14 instance
on the guess blocks `0, ..., (2 g - 1) / (B N)` of the input tape passes iff `unownedCount = 0` for
`withGuessLayout x g`. -/
theorem C14_iff_unownedCount_withGuess (x : List Bool) (hP : 2 ≤ B * N) (D : DirLayout M.K I N)
    (off : Fin (nGuessBlocks g (B * N)) → ℕ) (u : List Bool) (σ : Fin (I * N) → M.K → Fin 3)
    (hβ : ∀ ι k, D.betaS u ι k = some (betaT N σ ι k))
    (hprev : ∀ ι k δ, D.prevS u ι k δ = some (prevT N σ ι k δ))
    (hg : ∀ q, gOwnS D (guessDirWithGuess M g (B * N) off) u q =
      some (gOwnT (guessDirWithGuess M g (B * N) off) N σ q)) :
    (∀ q, C14 D (guessDirWithGuess M g (B * N) off) u q) ↔
      unownedCount (B := B) (withGuessLayout (M := M) x g) σ N I = 0 :=
  C14_iff_unownedCount _ D _ (covers_withGuess x hP off) u σ hβ hprev hg

end Net

end P1ChkDir
