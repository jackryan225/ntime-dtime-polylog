import P1ProgEng.KWShrinkC10BundleSpec

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)

noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- The two remaining reads of a radius-three shrink ball are its width and selected term tables. -/
structure PayloadRows (x : X.Base) (db : BallRows) : Prop extends LocalRows X x db where
  oldWidth_eq : ∀ e : OldArc X, hasRow db (addr X e.1.1.1) = true →
    oldWidth a (2 ^ g) db (arcCode X e) = X.packingWidth e
  selected_eq : ∀ (m : X.packingData.Motif) (layout : Bool) (t : Fin 4),
    hasRow db (addr X m.val.1.1.1) = true →
      read 0 (oldTerm a (2 ^ g) db (arcCode X m.val)) (termField layout t.val) =
        (s m).val (layout,t)

theorem read_ofFn_num {T : Type} {n : ℕ} (d : T) (f : Fin n → T) (i : Fin n) :
    read d (List.ofFn f) i.val = f i := by
  simp only [read, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

theorem bundleWidthNum_spec {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
    (bundle : OldBundle X) (hb : (baseGraph X).edist x bundle.1.1 ≤ 2) :
    bundleWidthNum a (2 ^ g) db (bundleCode X bundle) =
      X.packingData.bundleWidth X.packingWidth bundle := by
  let axis := (bitWordFinEquiv (colourBits a)).prodCongr (bitWordFinEquiv a)
  rw [bundleWidthNum, ← Fintype.sum_prod_type (fun uv : Fin (2 ^ colourBits a) × Fin (oldDegree a) =>
    widthIfThick a (2 ^ g) db (bundleCode X bundle, uv.1.val, uv.2.val)), P1P7.bundleWidth_sum]
  refine Fintype.sum_equiv axis.symm _ _ (fun uv => ?_)
  let e : OldArc X := (bundle, axis.symm uv)
  have h₀ : hasRow db (addr X e.1.1.1) = true := h.cover _ (hb.trans (by norm_num))
  have h₁ : hasRow db (addr X (X.packingData.actual e).1.1.1) = true :=
    h.cover _ ((edist_le_three hb (edist_target_le X bundle.1.1 bundle.2)).trans (by norm_num))
  have hc : arcCode X e = (bundleCode X bundle, uv.1.val, uv.2.val) := by
    have eq₁ := (bitWordFinEquiv (colourBits a)).apply_symm_apply uv.1
    have eq₂ := (bitWordFinEquiv a).apply_symm_apply uv.2
    change (bundleCode X bundle, (bitWordFinEquiv _ ((bitWordFinEquiv _).symm uv.1)).val,
      (bitWordFinEquiv _ ((bitWordFinEquiv _).symm uv.2)).val) = _
    rw [eq₁, eq₂]
  change widthIfThick a (2 ^ g) db (bundleCode X bundle, uv.1.val, uv.2.val) =
    if X.packingData.thick (sourcePosition e) ∧ X.packingData.thick (sourcePosition (X.packingData.actual e))
    then X.packingWidth e else 0
  rw [← hc, widthIfThick, codedTarget_spec h.toLocalRows.toGraphRows e h₀, sourceRow_spec, sourceRow_spec,
    codedThick_spec h.toLocalRows.toGraphRows (sourcePosition e) h₀,
    codedThick_spec h.toLocalRows.toGraphRows (sourcePosition (X.packingData.actual e)) h₁,
    h.oldWidth_eq e h₀]
  by_cases hs : X.packingData.thick (sourcePosition e) <;>
    by_cases ht : X.packingData.thick (sourcePosition (X.packingData.actual e)) <;> simp [hs, ht]

end P1ProgEng.SolKWS.C10
