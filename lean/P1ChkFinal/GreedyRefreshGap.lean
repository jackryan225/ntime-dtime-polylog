import P1SolGreedy.GreedyFamilies

/-!
# P1ChkFinal.GreedyRefreshGap: at a REFRESH level the families C5-C9 accept every index (lane P1-lean-greedy)

Test of the statement `D5Steps.greedy` (Interfaces/P1Int/ComposeD5.lean) with `G.greedy l = greedyG l`
(Interfaces/P1Int/FormDefs.lean). At a refresh level `l` (`(D.lv l).shrink = false`) every check of the families 4-8
(C5fam, C6fam, C7fam, C8fam, C9fam) accepts, whatever `u` is (below). So the left side of the step is `True`, and the
step would give `greedyG l u` from the earlier groups alone. But `greedyG l` asks that the TERM section of level `l`
agrees with a tuple (`LevUpTo (l + 1)`), and at a refresh level that section has
`bases * termKeys * (termArity + 1) > 0` fields (the refresh block terms, OpenAI `BlockChoices`), which no earlier
group fixes (`c10G (l - 1)` fixes only the panel of level `l`). The paper's C7 also checks the refresh terms ("resp. by
the block widths, for a refresh"; `P1ChkGreedy.C7r`, ChkGreedy/P1ChkGreedy/Refresh.lean), but the family program of
C7 (`P1SolGreedy.C7fam`) covers only shrinking levels (`ShrinkIdx`). So no family checks the refresh terms.
-/

namespace P1ChkFinal.GreedyRefreshGap

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1SolGreedy

theorem not_shrinkIdx (D : Dims) (i : ℕ) (h : (D.lv (i % 2 ^ levBits D)).shrink = false) :
    ¬ ShrinkIdx D i := by
  rintro ⟨-, hs, -⟩
  rw [h] at hs
  exact Bool.false_ne_true hs

theorem C5fam_refresh (Dn : ℕ → Dims) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false) : C5fam Dn x u i :=
  fun hS => absurd hS (not_shrinkIdx _ i h)

theorem C6fam_refresh (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false) : C6fam Dn ag x u i :=
  fun hS => absurd hS (not_shrinkIdx _ i h)

theorem C9fam_refresh (Dn : ℕ → Dims) (x u : List Bool) (l : ℕ)
    (h : ((Dn x.length).lv l).shrink = false) : C9fam Dn x u l := by
  rintro ⟨-, hs⟩
  rw [h] at hs
  exact absurd hs Bool.false_ne_true

section Motif

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem C7fam_refresh (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false) : C7fam B Dn ag x u i := by
  intro hS
  exact absurd hS (not_shrinkIdx (termDims (Dn x.length) (ag x.length)) i h)

theorem C8fam_refresh (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ)
    (h : ((Dn x.length).lv (i % 2 ^ levBits (Dn x.length))).shrink = false) : C8fam B Dn ag x u i := by
  intro hS
  exact absurd hS (not_shrinkIdx _ i h)

end Motif

/-- The refresh term section is not empty: at a refresh level with at least one base, one term key and arity `≥ 0`,
it has `bases * termKeys * (termArity + 1) > 0` fields. -/
theorem refresh_terms_count_pos (L : LevelDims) (hb : 0 < L.bases) (hk : 0 < L.termKeys) :
    0 < L.count .terms := by
  simp only [LevelDims.count]
  exact Nat.mul_pos (Nat.mul_pos hb hk) (Nat.succ_pos _)

end P1ChkFinal.GreedyRefreshGap

#print axioms P1ChkFinal.GreedyRefreshGap.C7fam_refresh
#print axioms P1ChkFinal.GreedyRefreshGap.C9fam_refresh
