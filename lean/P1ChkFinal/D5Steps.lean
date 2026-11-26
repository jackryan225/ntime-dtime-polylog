import P1ChkFinal.Wired

/-!
# P1ChkFinal.D5Steps: the steps `c11`, `c12`, `c13` of the integration's `P1Int.P11.D5Steps`, in its shape

Lane P1-lean-checks (2026-11-25), on the request of P1-lean-integ (board 13:05Z), in the form of integ's
`P1Int.P11.d5_dir_step`: `(earlier groups true) → ((∀ i < ni, i < cnt → ck u i = true) ↔ group predicate)`.
Group predicates (RHS): `c11` = `C11w_iff`'s (stored Ω = prefix sums of the stored final widths); `c12` = `C12w_iff`'s
(payload of length `pre ws N`, zero tail), earlier group `c11`; `c13` = `C13w_iff`'s (a chain `j` equal to the stored chain
with `P1Count.ChainOK b l (Wof x u) j`), families 12 (C13link) and 13 (C13ends).
-/

namespace P1ChkFinal

open P1Wit Module

/-- **Step `c11`** (family 10). -/
theorem d5_c11_step (dims : ℕ → Dims) (x : List Bool) (ni cnt : ℕ) (hc : cnt = cnt11 dims x.length)
    (hni : cnt11 dims x.length ≤ ni) {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool)
    (hck : ∀ u i, ck u i = true ↔ C11w dims x (w u) i) (u : U) :
    (∀ i < ni, i < cnt → ck u i = true) ↔
      ∀ y < finN (dims x.length), rdOmega (dims x.length) (w u) y = pre (wsOf (dims x.length) (w u)) y := by
  rw [← C11w_iff]
  subst hc
  constructor
  · intro h i
    by_cases hi : i < cnt11 dims x.length
    · exact (hck u i).1 (h i (by omega) hi)
    · exact C11w_out dims x (w u) (by omega)
  · intro h i _ _
    exact (hck u i).2 (h i)

/-- **Step `c12`** (family 11), under the group `c11`. -/
theorem d5_c12_step (dims : ℕ → Dims) (x : List Bool) (ni cnt : ℕ) (hc : cnt = cnt12 dims x.length)
    (hni : cnt12 dims x.length ≤ ni) {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool)
    (hck : ∀ u i, ck u i = true ↔ C12w dims x (w u) i) (u : U)
    (h11 : ∀ y < finN (dims x.length), rdOmega (dims x.length) (w u) y = pre (wsOf (dims x.length) (w u)) y) :
    (∀ i < ni, i < cnt → ck u i = true) ↔
      pre (wsOf (dims x.length) (w u)) (finN (dims x.length)) ≤ (rdPayload (dims x.length) (w u)).length ∧
        ∀ c ∈ (rdPayload (dims x.length) (w u)).drop (pre (wsOf (dims x.length) (w u)) (finN (dims x.length))),
          c = false := by
  rw [← C12w_iff dims x (w u) ((C11w_iff dims x (w u)).2 h11)]
  subst hc
  constructor
  · intro h i
    by_cases hi : i < cnt12 dims x.length
    · exact (hck u i).1 (h i (by omega) hi)
    · exact C12w_out dims x (w u) (by omega)
  · intro h i _ _
    exact (hck u i).2 (h i)

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- **Step `c13`** (families 12 = C13link, 13 = C13ends). -/
theorem d5_c13_step (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims)
    (Wof : List Bool → List Bool → ℕ → F) (x : List Bool) (ni : ℕ) (cnt : ℕ → ℕ)
    (hc12 : cnt 12 = cnt13link dims x.length) (hc13 : cnt 13 = cnt13ends dims x.length)
    (hni12 : cnt13link dims x.length ≤ ni) (hni13 : cnt13ends dims x.length ≤ ni)
    {U : Type*} (w : U → List Bool) (ck : ℕ → U → ℕ → Bool)
    (hck12 : ∀ u i, ck 12 u i = true ↔ C13linkw b dims Wof x (w u) i)
    (hck13 : ∀ u i, ck 13 u i = true ↔ C13endsw b l dims x (w u) i) (u : U) :
    (∀ c, 12 ≤ c → c ≤ 13 → ∀ i < ni, i < cnt c → ck c u i = true) ↔
      ∃ j : Fin (finP (dims x.length) + 1) → Fin Dd,
        (∀ v : Fin (finP (dims x.length) + 1), (j v : ℕ) = rdChain (dims x.length) (w u) v) ∧
        P1Count.ChainOK b l (fun i : Fin (finP (dims x.length)) => Wof x (w u) i) j := by
  rw [← C13w_iff b l dims Wof x (w u)]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i < cnt13link dims x.length
      · exact (hck12 u i).1 (h 12 le_rfl (by omega) i (by omega) (by rw [hc12]; exact hi))
      · exact C13linkw_out b dims Wof x (w u) (by omega)
    · by_cases hi : i < cnt13ends dims x.length
      · exact (hck13 u i).1 (h 13 (by omega) le_rfl i (by omega) (by rw [hc13]; exact hi))
      · exact C13endsw_out b l dims x (w u) (by omega)
  · rintro ⟨h12, h13⟩ c hc1 hc2 i _ _
    rcases (show c = 12 ∨ c = 13 by omega) with rfl | rfl
    · exact (hck12 u i).2 (h12 i)
    · exact (hck13 u i).2 (h13 i)

end P1ChkFinal

#print axioms P1ChkFinal.d5_c11_step
#print axioms P1ChkFinal.d5_c12_step
#print axioms P1ChkFinal.d5_c13_step
