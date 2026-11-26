import P1Count.Chain
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Algebra.Defs

/-!
# P1Count.Bookkeeping: the parity bookkeeping of Lemma P (task P9, lane P1-lean-W2-count)

Problem P1, Case 2. The Prop-level count of the paper's proof of `lem:P`
(research/papers/ntime-dtime-polylog.tex, after `lem:time`), over a finite `F₂`-algebra `F`, with every
check family and every imported identity as an abstract hypothesis (G3-chief, board 1449).

* `stages_iff` (target (i), abstract `lem:unique`): check families in stage order; if stage `k` passes
  exactly when the next group of fields is true (given that the earlier ones are), then all stages pass
  iff all fields are true.
* `CountData`: the objects of one input `x`: skeleton candidates `σ`, branches `ι`, final payload
  assignments `z`, the vertex tensors `W σ ι z i ∈ F` (final positions in a fixed order `i : Fin P`),
  `unowned σ` (exponent of the scalar `2 ^ u(σ)`, check C14) and `acc σ` (accepting guesses with
  skeleton `σ`).
* `CountData.Valid`: a tuple `(σ, ι, z, chain)` passes C14 (`unowned σ = 0`) and the chain check
  (`ChainOK`, file `P1Count.Chain`).
* `CountData.count_mod2` (target (iii), abstract): if the witnesses that pass every check are exactly the
  encodings of the valid tuples, the encoding is injective, and
  `2 ^ unowned σ · ∑_ι ∑_z ∏_i W σ ι z i = acc σ` in `F` (P4 with the scalar, and P5), then the number of
  passing witnesses has the parity of `∑_σ acc σ`, the number of accepting guesses.

Mathlib only.
STATUS (P1-lean-W2-count, 09:45Z wind-down): COMPLETE DRAFT, no `sorry`, NOT YET COMPILED (project p1-count
became ready 09:41Z). First job after the restart: `lake build P1Count.Bookkeeping` (builds Chain too).
-/

namespace P1Count

open Module

noncomputable section

/-! ## (i) Staged checks (abstract form of `lem:unique`) -/

/-- **Telescoping of check families.** `Tr k u`: the first `k` groups of fields of the witness `u` hold
their true values (relative to the free fields of `u`: σ, the term indices, z, the chain). `Stage k u`:
every check of stage `k` passes on `u`. If `Tr 0` always holds, if stage `k` passes exactly when group `k`
is true given that the earlier groups are (`hstep`; this is the form of the lanes' `Ck_unique`), and if
the predicates decrease (`hmono`), then all stages pass iff all groups are true. -/
theorem stages_iff {U : Type*} (K : ℕ) (Stage Tr : ℕ → U → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ k < K, ∀ u, Tr k u → (Stage k u ↔ Tr (k + 1) u))
    (hmono : ∀ k < K, ∀ u, Tr (k + 1) u → Tr k u) (u : U) :
    (∀ k < K, Stage k u) ↔ Tr K u := by
  induction K with
  | zero => exact ⟨fun _ => h0 u, fun _ k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ K ih =>
    have ih' := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      (fun k hk => hmono k (Nat.lt_succ_of_lt hk))
    constructor
    · intro h
      have hK : Tr K u := ih'.1 fun k hk => h k (Nat.lt_succ_of_lt hk)
      exact (hstep K (Nat.lt_succ_self K) u hK).1 (h K (Nat.lt_succ_self K))
    · intro h k hk
      have hK : Tr K u := hmono K (Nat.lt_succ_self K) u h
      rcases Nat.lt_or_ge k K with hk' | hk'
      · exact ih'.2 hK k hk'
      · have hkK : k = K := by omega
        subst hkK
        exact (hstep k (Nat.lt_succ_self k) u hK).2 h

/-- **(i) One passing witness per tuple.** With the stages of `stages_iff` and the final form
`hform` (all groups true iff `u` is the encoding of a good tuple), the witnesses that pass every stage are
exactly the encodings of the good tuples. With `enc` injective this is "exactly one passing witness per
good tuple". -/
theorem pass_iff_of_stages {U Tup : Type*} (enc : Tup → U) (Good : Tup → Prop) (K : ℕ)
    (Stage Tr : ℕ → U → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ k < K, ∀ u, Tr k u → (Stage k u ↔ Tr (k + 1) u))
    (hmono : ∀ k < K, ∀ u, Tr (k + 1) u → Tr k u)
    (hform : ∀ u, Tr K u ↔ ∃ t, Good t ∧ enc t = u) (u : U) :
    (∀ k < K, Stage k u) ↔ ∃ t, Good t ∧ enc t = u :=
  (stages_iff K Stage Tr h0 hstep hmono u).trans (hform u)

/-- **Regrouping.** If every check `i` lies in some group `j < K`, then all checks pass iff every group
passes. (The stage order of the checks need not follow the family numbering: a family may be split over
several stages, e.g. one stage per level.) -/
theorem forall_iff_groups {ι U : Type*} (Chk : ι → U → Prop) (grp : ℕ → ι → Prop) (K : ℕ)
    (hcover : ∀ i, ∃ j < K, grp j i) (u : U) :
    (∀ i, Chk i u) ↔ ∀ j < K, ∀ i, grp j i → Chk i u := by
  constructor
  · intro h j _ i _
    exact h i
  · intro h i
    obtain ⟨j, hj, hg⟩ := hcover i
    exact h j hj i hg

/-- **(i) in group form.** Checks `Chk i`, grouped into stages `grp j` (`j < K`) that cover all checks; the
stage lemmas `hstep` (form of `Ck_unique`, `Ck_true`) and the final form `hform` identify the witnesses that
pass every check with the encodings of the good tuples. -/
theorem pass_iff_of_groups {ι U Tup : Type*} (enc : Tup → U) (Good : Tup → Prop)
    (Chk : ι → U → Prop) (grp : ℕ → ι → Prop) (K : ℕ) (hcover : ∀ i, ∃ j < K, grp j i)
    (Tr : ℕ → U → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ j < K, ∀ u, Tr j u → ((∀ i, grp j i → Chk i u) ↔ Tr (j + 1) u))
    (hmono : ∀ j < K, ∀ u, Tr (j + 1) u → Tr j u)
    (hform : ∀ u, Tr K u ↔ ∃ t, Good t ∧ enc t = u) (u : U) :
    (∀ i, Chk i u) ↔ ∃ t, Good t ∧ enc t = u :=
  (forall_iff_groups Chk grp K hcover u).trans
    (pass_iff_of_stages enc Good K (fun j u => ∀ i, grp j i → Chk i u) Tr h0 hstep hmono hform u)

/-- **The dispatcher, Prop level.** `dec γ` is the check addressed by the selector `γ` (`none`: a number
beyond the last check, which accepts). If every check is addressed by some selector, a witness passes for
every selector iff it passes every check. -/
theorem forall_dispatch_iff {Γ U Idx : Type*} (dec : Γ → Option Idx)
    (hsurj : ∀ c, ∃ γ, dec γ = some c) (Check : Idx → U → Prop) (u : U) :
    (∀ γ, ∀ c, dec γ = some c → Check c u) ↔ ∀ c, Check c u := by
  constructor
  · intro h c
    obtain ⟨γ, hγ⟩ := hsurj c
    exact h γ c hγ
  · intro h γ c _
    exact h c

/-! ## Arithmetic of a finite `F₂`-algebra -/

section Algebra

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F]

/-- In an `F₂`-algebra, `2 = 0`. -/
theorem two_eq_zero_of_algebra : (2 : F) = 0 := by
  have h : (2 : F) = algebraMap (ZMod 2) F 2 := (map_ofNat (algebraMap (ZMod 2) F) 2).symm
  rw [h, show (2 : ZMod 2) = 0 by decide, map_zero]

/-- The scalar `2 ^ u` is the indicator of `u = 0`. -/
theorem two_pow_eq_ite (u : ℕ) : (2 : F) ^ u = if u = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [two_eq_zero_of_algebra, zero_pow h]

/-- A functional with `l 1 = 1` reads natural numbers mod 2. -/
theorem functional_natCast (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1) (n : ℕ) :
    l (n : F) = (n : ZMod 2) := by
  rw [← nsmul_one n, map_nsmul, hl, nsmul_one]

end Algebra

/-! ## The count -/

/-- The objects of the parity count for one input `x` (all finite). -/
structure CountData (F : Type*) where
  /-- Skeleton candidates `σ`. -/
  Sk : Type
  skFin : Fintype Sk
  /-- Branches `ι` (sequences of selected terms) of the compressor execution on `N_{x,σ}`. -/
  Ch : Sk → Type
  chFin : ∀ σ, Fintype (Ch σ)
  /-- Payload assignments `z` (one payload per final wire) of branch `ι`. -/
  Pay : (σ : Sk) → Ch σ → Type
  payFin : ∀ σ ι, Fintype (Pay σ ι)
  /-- Number of final positions of branch `ι`. -/
  P : (σ : Sk) → Ch σ → ℕ
  /-- The vertex tensors `W_v(z|_v; ι) ∈ F`, final positions in the fixed (address) order. -/
  W : (σ : Sk) → (ι : Ch σ) → Pay σ ι → Fin (P σ ι) → F
  /-- `u(σ)`: the number of guess cells in big blocks without an owner (scalar `2 ^ u(σ)`, check C14). -/
  unowned : Sk → ℕ
  /-- The number of accepting guesses whose run has skeleton `σ`. -/
  acc : Sk → ℕ

attribute [instance] CountData.skFin CountData.chFin CountData.payFin

namespace CountData

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (C : CountData F) {D : ℕ}

/-- The tuples `(σ, ι, z, chain)`; a chain has one entry in `Fin D` per final position, plus one. -/
abbrev Tup (D : ℕ) := Σ σ : C.Sk, Σ ι : C.Ch σ, Σ _z : C.Pay σ ι, (Fin (C.P σ ι + 1) → Fin D)

/-- A tuple is valid: check C14 holds (`u(σ) = 0`) and the chain passes the chain check. -/
def Valid (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (t : C.Tup D) : Prop :=
  C.unowned t.1 = 0 ∧ ChainOK b l (C.W t.1 t.2.1 t.2.2.1) t.2.2.2

theorem valid_iff (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (t : C.Tup D) :
    C.Valid b l t ↔ C.unowned t.1 = 0 ∧ ChainOK b l (C.W t.1 t.2.1 t.2.2.1) t.2.2.2 :=
  Iff.rfl

open scoped Classical in
/-- The number of valid tuples over one skeleton, mod 2, is `l (2 ^ u(σ) · ∑_ι ∑_z ∏_i W)`. -/
theorem sum_valid_sigma (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (σ : C.Sk) :
    (∑ r : Σ ι : C.Ch σ, Σ _z : C.Pay σ ι, (Fin (C.P σ ι + 1) → Fin D),
        if C.Valid b l ⟨σ, r⟩ then (1 : ZMod 2) else 0) =
      l ((2 : F) ^ C.unowned σ * ∑ ι, ∑ z, ∏ i, C.W σ ι z i) := by
  by_cases hu : C.unowned σ = 0
  · rw [hu, pow_zero, one_mul, map_sum, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [map_sum, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [lambda_chain b l, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ChainOK b l (C.W σ ι z) j
    · rw [if_pos ((C.valid_iff b l _).2 ⟨hu, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc ((C.valid_iff b l _).1 h).2), if_neg hc]
  · rw [two_pow_eq_ite, if_neg hu, zero_mul, map_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]
    exact fun h => hu ((C.valid_iff b l _).1 h).1

open scoped Classical in
/-- **P9 (3), `count_mod2`, abstract form.** Hypotheses:
* `hP` (P4 with the scalar and P5): `2 ^ u(σ) · ∑_ι ∑_z ∏_i W σ ι z i = acc σ` in `F`;
* `hinj`, `hpass` (target (i)): the witnesses that pass every check are exactly the encodings of the valid
  tuples, and the encoding is injective.
Then the number of passing witnesses has the parity of the number `∑_σ acc σ` of accepting guesses. -/
theorem count_mod2 (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (hP : ∀ σ, (2 : F) ^ C.unowned σ * ∑ ι, ∑ z, ∏ i, C.W σ ι z i = (C.acc σ : F))
    {U : Type*} [Fintype U] (Pass : U → Prop) [DecidablePred Pass] (enc : C.Tup D → U)
    (hinj : Function.Injective enc) (hpass : ∀ u, Pass u ↔ ∃ t, C.Valid b l t ∧ enc t = u) :
    ((Finset.univ.filter Pass).card : ZMod 2) = ((∑ σ, C.acc σ : ℕ) : ZMod 2) := by
  have h1 : Finset.univ.filter Pass = (Finset.univ.filter (C.Valid b l)).image enc := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hpass]
  rw [h1, Finset.card_image_of_injective _ hinj, Finset.natCast_card_filter,
    ← functional_natCast l hl, Nat.cast_sum, map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← hP σ]
  exact C.sum_valid_sigma b l σ

open scoped Classical in
/-- Parity form of `count_mod2`. -/
theorem odd_iff (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (hP : ∀ σ, (2 : F) ^ C.unowned σ * ∑ ι, ∑ z, ∏ i, C.W σ ι z i = (C.acc σ : F))
    {U : Type*} [Fintype U] (Pass : U → Prop) [DecidablePred Pass] (enc : C.Tup D → U)
    (hinj : Function.Injective enc) (hpass : ∀ u, Pass u ↔ ∃ t, C.Valid b l t ∧ enc t = u) :
    Odd (Finset.univ.filter Pass).card ↔ Odd (∑ σ, C.acc σ) := by
  have h := C.count_mod2 b l hl hP Pass enc hinj hpass
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd, h]

open scoped Classical in
/-- **(i) + (iii) together.** The witnesses pass every stage of checks (`stages_iff`), the final form
`hform` identifies the fully true witnesses with the encodings of valid tuples, and `hP` is P4 + P5. -/
theorem odd_iff_of_stages (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (hP : ∀ σ, (2 : F) ^ C.unowned σ * ∑ ι, ∑ z, ∏ i, C.W σ ι z i = (C.acc σ : F))
    {U : Type*} [Fintype U] (enc : C.Tup D → U) (hinj : Function.Injective enc)
    (K : ℕ) (Stage Tr : ℕ → U → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ k < K, ∀ u, Tr k u → (Stage k u ↔ Tr (k + 1) u))
    (hmono : ∀ k < K, ∀ u, Tr (k + 1) u → Tr k u)
    (hform : ∀ u, Tr K u ↔ ∃ t, C.Valid b l t ∧ enc t = u) :
    Odd (Finset.univ.filter fun u => ∀ k < K, Stage k u).card ↔ Odd (∑ σ, C.acc σ) := by
  convert C.odd_iff b l hl hP (fun u => ∀ k < K, Stage k u) enc hinj
    (pass_iff_of_stages enc (C.Valid b l) K Stage Tr h0 hstep hmono hform)

end CountData

end

end P1Count
