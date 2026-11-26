import P1Int.DispCk
import P1Int.DispCnt

/-!
# P1Int.DispOut: the field `out` of `D5Steps` for the deciders `dispCk` and the counts `dispCnt` (lane P1-lean-disp,
item p11_out)

`out`: every check `(c, i)` of stage `0` of `fixedIndex (dispCnt |x|)` accepts. Stage `0` means: `c = 15` (accepts by
definition), or `i ≥ cnt c` (the lanes' `_out` lemmas), or a level family `4 ≤ c ≤ 9` at a level `i % 2^L ≥ top`.
The last case is where a family must accept by its own definition; it holds because the TOP row of the genuine layout
is the final row (`levelDims .. none`): `shrink = false` and `termKeys = 0` (`genuine_top`). Hence
* C5, C6, C8 (`ShrinkIdx D`) and C7fam (`ShrinkIdx (termDims D ag)`, same top and kinds): no shrinking index at `top`;
* C7Rfam (`ShrinkIdx (refDims D)`: kind `!shrink = true` at `top`, BUT bases `bases * termKeys = 0`): no index;
* C9fam (index = level; at `i = top` the level is not shrinking);
* C10w (`C10Idx` needs level `< top`).
-/

namespace P1Int

namespace P11

namespace Disp

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace

open private levelDims layoutRows runPhases from P1Wit.SpaceFacts

/-- The last row of the layout is the final row (kind `none`). -/
theorem layoutRows_last {k : Type} [Field k] (S : BlockSchedule k) :
    ∀ (P g : ℕ) xs, ∃ g' P' : ℕ, (layoutRows S P g xs)[xs.length]? =
      some (levelDims S.expanderExponent (S.degreeExponent 0) g' P' none)
  | P, g, [] => ⟨g, P, rfl⟩
  | P, g, ph :: xs => by
    obtain ⟨g', P', h⟩ := layoutRows_last S (P / ph.divisor) (g - ph.laneLoss) xs
    refine ⟨g', P', ?_⟩
    change (levelDims S.expanderExponent ph.exponent g P (some ph.shrink) ::
      layoutRows S (P / ph.divisor) (g - ph.laneLoss) xs)[xs.length + 1]? = _
    rw [List.getElem?_cons_succ]
    exact h

/-- **The top row of the genuine dims**: not shrinking, no term keys. -/
theorem genuine_top {k : Type} [Field k] {S : BlockSchedule k} (A : S.Templates) (K : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM t g d bigBias termBias : ℕ) :
    ((genuineDims A K V aM t g d bigBias termBias).lv (genuineDims A K V aM t g d bigBias termBias).top).shrink = false ∧
    ((genuineDims A K V aM t g d bigBias termBias).lv (genuineDims A K V aM t g d bigBias termBias).top).termKeys = 0 := by
  obtain ⟨g', P', h⟩ := layoutRows_last S (initialPositions V aM t) (P1Wrap.Params.h t)
    (runPhases S (P1Wrap.Params.T K t))
  have e : (genuineDims A K V aM t g d bigBias termBias).lv (genuineDims A K V aM t g d bigBias termBias).top =
      levelDims S.expanderExponent (S.degreeExponent 0) g' P' none := by
    change ((layoutRows S (initialPositions V aM t) (P1Wrap.Params.h t) (runPhases S (P1Wrap.Params.T K t)))[
      (runPhases S (P1Wrap.Params.T K t)).length]?).getD (levelDims S.expanderExponent 0 0 0 none) = _
    rw [h]
    rfl
  rw [e]
  exact ⟨rfl, rfl⟩

theorem not_shrinkIdx_top (D : Dims) (hsh : (D.lv D.top).shrink = false) {i : ℕ}
    (hi : D.top ≤ i % 2 ^ P1ChkGreedy.levBits D) : ¬ P1ChkGreedy.ShrinkIdx D i := by
  rintro ⟨h1, h2, -⟩
  rw [le_antisymm h1 hi, hsh] at h2
  exact Bool.false_ne_true h2

theorem not_shrinkIdx_term_top (D : Dims) (ag : ℕ → ℕ × ℕ) (hsh : (D.lv D.top).shrink = false) {i : ℕ}
    (hi : D.top ≤ i % 2 ^ P1ChkGreedy.levBits D) : ¬ P1ChkGreedy.ShrinkIdx (P1SolGreedy.termDims D ag) i := by
  rintro ⟨h1, h2, -⟩
  change i % 2 ^ P1ChkGreedy.levBits D ≤ D.top at h1
  change (D.lv (i % 2 ^ P1ChkGreedy.levBits D)).shrink = true at h2
  rw [le_antisymm h1 hi, hsh] at h2
  exact Bool.false_ne_true h2

theorem not_shrinkIdx_ref_top (D : Dims) (hk : (D.lv D.top).termKeys = 0) {i : ℕ}
    (hi : D.top ≤ i % 2 ^ P1ChkGreedy.levBits D) : ¬ P1ChkGreedy.ShrinkIdx (P1ChkFinal.C7R.refDims D) i := by
  rintro ⟨h1, -, h3⟩
  change i % 2 ^ P1ChkGreedy.levBits D ≤ D.top at h1
  change i / 2 ^ P1ChkGreedy.levBits D <
    (D.lv (i % 2 ^ P1ChkGreedy.levBits D)).bases * (D.lv (i % 2 ^ P1ChkGreedy.levBits D)).termKeys at h3
  rw [le_antisymm h1 hi, hk, Nat.mul_zero] at h3
  exact Nat.not_lt_zero _ h3

section TopFam

open OAI.Computability.VPVNP.SpectralGeometry OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1ChkGreedy P1SolGreedy

variable (Dn : ℕ → Dims) (x u : List Bool) (i : ℕ)
  (hsh : ((Dn x.length).lv (Dn x.length).top).shrink = false)
  (hl : (Dn x.length).top ≤ i % 2 ^ P1ChkGreedy.levBits (Dn x.length))

include hsh hl

theorem C5fam_top : C5fam Dn x u i := fun hS => absurd hS (not_shrinkIdx_top (Dn x.length) hsh hl)

theorem C6fam_top (ag : ℕ → ℕ → ℕ × ℕ) : C6fam Dn ag x u i :=
  fun hS => absurd hS (not_shrinkIdx_top (Dn x.length) hsh hl)

theorem C8fam_top {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ag : ℕ → ℕ → ℕ × ℕ) : C8fam B Dn ag x u i :=
  fun hS => absurd hS (not_shrinkIdx_top (Dn x.length) hsh hl)

theorem C9fam_top : C9fam Dn x u i := by
  rintro ⟨h1, h2⟩
  have e : i = (Dn x.length).top := le_antisymm h1 (le_trans hl (Nat.mod_le _ _))
  rw [e, hsh] at h2
  exact absurd h2 Bool.false_ne_true

omit hsh in
theorem C10w_top (fx : P1C10.C10Fix) : P1C10.C10w fx Dn x u i := by
  intro hI
  unfold P1C10.C10Idx at hI
  exact absurd hI.1 (Nat.not_lt.mpr hl)

theorem C7all_top (hk : ((Dn x.length).lv (Dn x.length).top).termKeys = 0)
    {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
    (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
    (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
    {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ag : ℕ → ℕ → ℕ × ℕ) : P1ChkFinal.C7R.C7all P hdH hconn F B Dn ag x u i :=
  And.intro (fun hS => absurd hS (not_shrinkIdx_term_top (Dn x.length) (ag x.length) hsh hl))
    (fun hS => absurd hS (not_shrinkIdx_ref_top (Dn x.length) hk hl))

end TopFam

/-- The checks of stage `0`. -/
theorem stg_zero (X : D5Index) {c i : ℕ} (h : X.stg c i = 0) :
    c = 15 ∨ X.cnt c ≤ i ∨ (4 ≤ c ∧ c ≤ 9 ∧ X.top ≤ X.lev c i) := by
  unfold D5Index.stg at h
  split_ifs at h <;> omega

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
  (a b d bigBias termBias : ℕ)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
  (Wof : List Bool → List Bool → ℕ → F)

open Classical in
/-- **Item p11_out: the field `out`** for `dispCk` and `dispCnt`, at every input. -/
theorem dispCk_out (x u : List Bool) (c : ℕ) (hc : c < 16) (i : ℕ)
    (h : (fixedIndex Bt V a b x d bigBias termBias (dispCnt Bt V a b d bigBias termBias x.length)).stg c i = 0) :
    dispCk Bt V a b d bigBias termBias bs l Wof c x u i = true := by
  have htop := genuine_top Bt (portConsts Bt) (toOAI V) 1 (lpTime a b x.length) (a * (x.length ^ 2 + 1)) d
    bigBias termBias
  rcases stg_zero _ h with h15 | hcnt | ⟨h4, h9, hlev⟩
  · subst h15
    rfl
  · change dispCnt Bt V a b d bigBias termBias x.length c ≤ i at hcnt
    interval_cases c
    · exact decide_eq_true (P1ChkDir.C1F_out _ _ _ hcnt)
    · exact decide_eq_true (P1ChkDir.C2F_out _ _ _ hcnt)
    · exact decide_eq_true (P1ChkDir.C3F_out _ _ _ hcnt)
    · exact decide_eq_true (P1ChkDir.C4w_out _ _ _ _ _ hcnt)
    · exact decide_eq_true (fun hS => absurd hS (P1ChkGreedy.not_shrinkIdx_of_ge _ hcnt))
    · exact decide_eq_true (fun hS => absurd hS (P1ChkGreedy.not_shrinkIdx_of_ge _ hcnt))
    · have h6 : max (P1SolGreedy.cntTerm (gdims Bt V a b d bigBias termBias x.length)
            (genuineAg (gdims Bt V a b d bigBias termBias) x.length))
          (P1ChkFinal.C7R.cntRef (gdims Bt V a b d bigBias termBias x.length)) ≤ i := hcnt
      exact decide_eq_true (And.intro
        (fun hS => absurd hS (P1ChkGreedy.not_shrinkIdx_of_ge _ (le_of_max_le_left h6)))
        (fun hS => absurd hS (P1ChkGreedy.not_shrinkIdx_of_ge _ (le_of_max_le_right h6))))
    · exact decide_eq_true (fun hS => absurd hS (P1ChkGreedy.not_shrinkIdx_of_ge _ hcnt))
    · exact decide_eq_true (P1ChkGreedy.C9fam_out _ _ _ hcnt)
    · exact decide_eq_true (P1C10.C10w_out _ _ _ _ hcnt)
    · exact decide_eq_true (P1ChkFinal.C11w_out _ _ _ hcnt)
    · exact decide_eq_true (P1ChkFinal.C12w_out _ _ _ hcnt)
    · exact decide_eq_true (P1ChkFinal.C13linkw_out _ _ _ _ _ hcnt)
    · exact decide_eq_true (P1ChkFinal.C13endsw_out _ _ _ _ _ hcnt)
    · exact decide_eq_true (P1ChkDir.C14F_out _ _ _ _ _ hcnt)
    · rfl
  · have hl : (gdims Bt V a b d bigBias termBias x.length).top ≤
        i % 2 ^ P1ChkGreedy.levBits (gdims Bt V a b d bigBias termBias x.length) := hlev
    have hsh : ((gdims Bt V a b d bigBias termBias x.length).lv
        (gdims Bt V a b d bigBias termBias x.length).top).shrink = false := htop.1
    have hk : ((gdims Bt V a b d bigBias termBias x.length).lv
        (gdims Bt V a b d bigBias termBias x.length).top).termKeys = 0 := htop.2
    interval_cases c
    · exact decide_eq_true (C5fam_top _ x u i hsh hl)
    · exact decide_eq_true (C6fam_top _ x u i hsh hl _)
    · exact decide_eq_true (C7all_top _ x u i hsh hl hk _ _ _ _ _ _)
    · exact decide_eq_true (C8fam_top _ x u i hsh hl _ _)
    · exact decide_eq_true (C9fam_top _ x u i hsh hl)
    · exact decide_eq_true (C10w_top _ x u i hl _)

end

end Disp

end P11

end P1Int

#print axioms P1Int.P11.Disp.genuine_top
#print axioms P1Int.P11.Disp.dispCk_out
