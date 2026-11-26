import P1Int.WitfillLink

/-!
# P1Int.WitfillGlue: `ChecksHyp` from `ChecksRec` (owner: P1-lean-integ)

`checksHyp_of_rec`: Sol witfill supplies the order of the final sites, the witness code and its injectivity
(`P1Int.P11.witfill_fixed`), so `ChecksHyp` follows from `ChecksRec` (the threshold is raised to witfill's `n₂`).
`openChecks_of_rec : OpenChecksRec → OpenChecks`.
Note (p1intB-43..45): one `obtain` with the whole pattern of `ChecksRec` (an instance `Fintype A` early in a chain
of 15 components) hits the heartbeat limit at `whnf`; destructuring step by step is fast.
-/

namespace P1Int

namespace P11

open Module OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

/-- **`ChecksHyp` from `ChecksRec`.** -/
theorem checksHyp_of_rec (h : ChecksRec Bt κ hκ bs l) : ChecksHyp Bt κ hκ bs l := by
  intro L V a b n₀ hb1 hV
  have h1 := h L V a b n₀ hb1 hV
  rcases h1 with ⟨A, h1⟩
  rcases h1 with ⟨hA, h1⟩
  rcases h1 with ⟨bit, h1⟩
  rcases h1 with ⟨letter, h1⟩
  rcases h1 with ⟨hlet, h1⟩
  rcases h1 with ⟨hbit, h1⟩
  rcases h1 with ⟨answer, h1⟩
  rcases h1 with ⟨hans, h1⟩
  rcases h1 with ⟨chk, h1⟩
  rcases h1 with ⟨c, h1⟩
  rcases h1 with ⟨n₁, h1⟩
  rcases h1 with ⟨bigBias, h1⟩
  rcases h1 with ⟨termBias, h1⟩
  rcases h1 with ⟨hc, hx⟩
  obtain ⟨n₂, hn₂⟩ := witfill_fixed Bt κ hκ V a b D bigBias termBias
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, c, max n₁ n₂, hc, ?_⟩
  intro x hxn
  have hx1 := hx x (le_trans (le_max_left _ _) hxn)
  rcases hx1 with ⟨htot, hx1⟩
  rcases hx1 with ⟨H, hchecks⟩
  refine ⟨htot, ?_⟩
  refine ⟨fixedOrd Bt κ hκ V a b x, ?_⟩
  refine ⟨fixedEnc Bt κ hκ V a b x D bigBias termBias H, ?_⟩
  refine ⟨hn₂ x (le_trans (le_max_right _ _) hxn) H, ?_⟩
  exact hchecks

/-- **Open input 2 from its witfill form.** -/
theorem openChecks_of_rec (h : OpenChecksRec) : OpenChecks := by
  intro S Bt F _ _ _ _ κ hκ D bs l hl hlane hgrow
  exact checksHyp_of_rec Bt κ hκ bs l (h S Bt F κ hκ D bs l hl hlane hgrow)

end P11

end P1Int

#print axioms P1Int.P11.checksHyp_of_rec
#print axioms P1Int.P11.openChecks_of_rec
