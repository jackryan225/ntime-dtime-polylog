import P1Int.ComposeD5
import P1ChkDir.Genuine

/-!
# P1Int.ComposeDir: the step `dir` of `D5Steps` from the proved stage lemma of P1-lean-checks (owner: P1-lean-integ)

Group 1 of D5 (families 0, 1, 2 = C1, C2, C3) with the group predicate `P1ChkDir.DirTrue (dirP6 D ρ)`: the step is
`P1ChkDir.dirF_iff` (lane checks, proved) plus `C1F_out`, `C2F_out`, `C3F_out` for the indices beyond the counts,
once the three counts fit into the `ni = 2^(k-4)` index words.
-/

namespace P1Int

namespace P11

open P1Wit P1ChkDir

/-- **Step `dir` of `D5Steps`** for families given as the check lanes' `C1F`, `C2F`, `C3F` on the bit list `w u`. -/
theorem d5_dir_step {K : Type} (D : Dims) (ρ : K ≃ Fin D.r) (ni : ℕ) (cnt : ℕ → ℕ)
    (hc0 : cnt 0 = D.I * D.N * D.r) (hc1 : cnt 1 = D.I * D.r) (hc2 : cnt 2 = D.I * D.r * 3 * 2)
    (hn0 : D.I * D.N * D.r ≤ ni) (hn1 : D.I * D.r ≤ ni) (hn2 : D.I * D.r * 3 * 2 ≤ ni)
    {U : Type*} (w : U → List Bool) (ck : ℕ → U → ℕ → Bool)
    (hck0 : ∀ u i, ck 0 u i = true ↔ C1F D ρ (w u) i) (hck1 : ∀ u i, ck 1 u i = true ↔ C2F D ρ (w u) i)
    (hck2 : ∀ u i, ck 2 u i = true ↔ C3F D ρ (w u) i) (u : U) :
    (∀ c ≤ 2, ∀ i < ni, i < cnt c → ck c u i = true) ↔ DirTrue (dirP6 D ρ) (w u) := by
  rw [← dirF_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · by_cases hi : i < D.I * D.N * D.r
      · exact (hck0 u i).1 (h 0 (by omega) i (by omega) (by rw [hc0]; exact hi))
      · exact C1F_out D ρ (w u) (by omega)
    · by_cases hi : i < D.I * D.r
      · exact (hck1 u i).1 (h 1 (by omega) i (by omega) (by rw [hc1]; exact hi))
      · exact C2F_out D ρ (w u) (by omega)
    · by_cases hi : i < D.I * D.r * 3 * 2
      · exact (hck2 u i).1 (h 2 (by omega) i (by omega) (by rw [hc2]; exact hi))
      · exact C3F_out D ρ (w u) (by omega)
  · rintro ⟨h1, h2, h3⟩ c hc i _ _
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · exact (hck0 u i).2 (h1 i)
    · exact (hck1 u i).2 (h2 i)
    · exact (hck2 u i).2 (h3 i)

end P11

end P1Int

#print axioms P1Int.P11.d5_dir_step
