import P1Count.Chain

/-!
# P1, wave 2, check C13 (lane P1-lean-W2-chkfinal), chain-link form of G3-chief decision D4 (board 10:49Z)

Paper l.1059: (one per final position `v`) `W_v(z|_v; ι(u)) = 1`. Over `F₂` this is right (`C13_iff_F2`). In Lean
the values `W_v` lie in the finite `F₂`-algebra `F` of the wrapper (P0); there `(∀ v, W_v = 1) ↔ ∏ W_v = 1` is
FALSE (count lane, 09:46Z: `F = F₄`, `W₁ = ω`, `W₂ = ω²`). D4: the witness carries a λ-chain `j_0, ..., j_P`
of basis indices (P6 section `chain`, each `j_v` a number), and the checks are

* `C13link b P W jn v` (family 12, one per final position `v < P`, positions in address order):
  `j_v < D`, `j_{v+1} < D` and `P1Count.mulEntry b (W v) j_v j_{v+1} = 1`;
* `C13ends b l P jn i` (family 13): `i = 0`: `j_0 < D` and `b.repr 1 j_0 = 1`; `i = 1`: `j_P < D` and
  `l (b j_P) = 1`.
* `C13link_iff` (stage form): all links and both ends pass iff the stored numbers are the values of a chain
  `j : Fin (P+1) → Fin D` with `P1Count.ChainOK b l W j`. With `P1Count.lambda_chain`
  (`l (∏ W) = #{chains with ChainOK}` in `ZMod 2`) this is the parity count of C13.
* `C13link_out`, `C13ends_out`: indices out of range accept (D5 amendment, board 10:51Z).

`mulEntry` and `ChainOK` are used VERBATIM from `P1Count.Chain` (D4).
-/

namespace P1ChkFinal

open Finset Module

/-! ## The `F₂` form (the withdrawn brief form; valid only over `ZMod 2`, the case `D = 1`) -/

theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- Over `F₂`: every factor is `1` iff the product is `1`. -/
theorem C13_iff_F2 {ι : Type*} (s : Finset ι) (w : ι → ZMod 2) : (∀ v ∈ s, w v = 1) ↔ ∏ v ∈ s, w v = 1 := by
  refine ⟨fun h => prod_eq_one h, fun h v hv => ?_⟩
  rcases zmod2_eq_zero_or_one (w v) with h0 | h1
  · rw [prod_eq_zero hv h0] at h
    exact absurd h (by decide)
  · exact h1

/-! ## The chain-link checks (D4) -/

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {D : ℕ}

/-- **Check C13link** at final position `v` (family 12): the link `j_v → j_{v+1}` through `W v`, with the range
checks of the two stored numbers. Positions `v ≥ P` accept. -/
def C13link (b : Basis (Fin D) (ZMod 2) F) (P : ℕ) (W : ℕ → F) (jn : ℕ → ℕ) (v : ℕ) : Prop :=
  v < P → ∃ (h : jn v < D) (h' : jn (v + 1) < D), P1Count.mulEntry b (W v) ⟨jn v, h⟩ ⟨jn (v + 1), h'⟩ = 1

/-- **Check C13ends** (family 13): `i = 0` the start entry, `i = 1` the end entry, with range checks; other
indices accept. -/
def C13ends (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (P : ℕ) (jn : ℕ → ℕ) (i : ℕ) : Prop :=
  (i = 0 → ∃ h : jn 0 < D, b.repr 1 ⟨jn 0, h⟩ = 1) ∧ (i = 1 → ∃ h : jn P < D, l (b ⟨jn P, h⟩) = 1)

theorem C13link_out (b : Basis (Fin D) (ZMod 2) F) {P : ℕ} (W : ℕ → F) (jn : ℕ → ℕ) {v : ℕ} (hv : P ≤ v) :
    C13link b P W jn v :=
  fun h => absurd h (not_lt.mpr hv)

theorem C13ends_out (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (P : ℕ) (jn : ℕ → ℕ) {i : ℕ}
    (hi : 2 ≤ i) : C13ends b l P jn i :=
  ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- **C13, soundness.** The numbers of a chain with `ChainOK` pass every link and both ends. -/
theorem C13_true (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ} (W : ℕ → F) (jn : ℕ → ℕ)
    (j : Fin (P + 1) → Fin D) (hj : ∀ v : Fin (P + 1), (j v : ℕ) = jn v)
    (hok : P1Count.ChainOK b l (fun i : Fin P => W i) j) :
    (∀ v, C13link b P W jn v) ∧ (∀ i, C13ends b l P jn i) := by
  obtain ⟨hs, hlink, he⟩ := hok
  refine ⟨fun v hv => ?_, fun i => ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · let i : Fin P := ⟨v, hv⟩
    have h1 : jn v < D := by
      have := (j i.castSucc).isLt
      rw [hj] at this
      exact this
    have h2 : jn (v + 1) < D := by
      have := (j i.succ).isLt
      rw [hj] at this
      exact this
    have e1 : (⟨jn v, h1⟩ : Fin D) = j i.castSucc := Fin.ext (hj i.castSucc).symm
    have e2 : (⟨jn (v + 1), h2⟩ : Fin D) = j i.succ := Fin.ext (hj i.succ).symm
    refine ⟨h1, h2, ?_⟩
    rw [e1, e2]
    exact hlink i
  · have h1 : jn 0 < D := by
      have := (j 0).isLt
      rw [hj] at this
      exact this
    have e1 : (⟨jn 0, h1⟩ : Fin D) = j 0 := Fin.ext (hj 0).symm
    exact ⟨h1, by rw [e1]; exact hs⟩
  · have h1 : jn P < D := by
      have := (j (Fin.last P)).isLt
      rw [hj] at this
      exact this
    have e1 : (⟨jn P, h1⟩ : Fin D) = j (Fin.last P) := Fin.ext (hj (Fin.last P)).symm
    exact ⟨h1, by rw [e1]; exact he⟩

/-- **C13, uniqueness.** If every link and both ends pass, the stored numbers are the values of a chain with
`ChainOK` (the chain is determined by the numbers). -/
theorem C13_unique (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ} (W : ℕ → F) (jn : ℕ → ℕ)
    (hlink : ∀ v, C13link b P W jn v) (hends : ∀ i, C13ends b l P jn i) :
    ∃ j : Fin (P + 1) → Fin D, (∀ v : Fin (P + 1), (j v : ℕ) = jn v) ∧
      P1Count.ChainOK b l (fun i : Fin P => W i) j := by
  have hr : ∀ v : Fin (P + 1), jn v < D := by
    intro v
    rcases Nat.lt_or_ge (v : ℕ) P with hv | hv
    · exact (hlink v hv).1
    · have hvP : (v : ℕ) = P := le_antisymm (Nat.lt_succ_iff.mp v.isLt) hv
      obtain ⟨h, _⟩ := (hends 1).2 rfl
      rw [hvP]
      exact h
  refine ⟨fun v => ⟨jn v, hr v⟩, fun v => rfl, ?_, fun i => ?_, ?_⟩
  · obtain ⟨_, h'⟩ := (hends 0).1 rfl
    exact h'
  · obtain ⟨_, _, hm⟩ := hlink i i.isLt
    exact hm
  · obtain ⟨_, h'⟩ := (hends 1).2 rfl
    exact h'

/-- **C13link_iff** (stage form of D4/D5). -/
theorem C13link_iff (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (P : ℕ) (W : ℕ → F)
    (jn : ℕ → ℕ) :
    ((∀ v, C13link b P W jn v) ∧ (∀ i, C13ends b l P jn i)) ↔
      ∃ j : Fin (P + 1) → Fin D, (∀ v : Fin (P + 1), (j v : ℕ) = jn v) ∧
        P1Count.ChainOK b l (fun i : Fin P => W i) j :=
  ⟨fun h => C13_unique b l W jn h.1 h.2, fun ⟨j, hj, hok⟩ => C13_true b l W jn j hj hok⟩

end P1ChkFinal
