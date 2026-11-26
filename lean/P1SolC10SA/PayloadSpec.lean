import P1SolC10SA.BundleSpec
import P1SolC10SA.TopologySpec

namespace P1SolC10SA.SolShrink

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

/-- The two remaining reads of a radius-six shrink ball are its width and selected term tables. -/
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

def motifAtLane (layout : Bool) (z : OldId X (SD a b)) (l : BitWord g) : X.packingData.Motif :=
  X.packingData.translateMotif z.2.1.val
    (l - (X.packingData.survivingRole layout (sourceRole layout z.1) z.2.1.val).2.2)

theorem withLane_motifAtLane {db : BallRows} (h : GraphRows X db) (layout : Bool) (z : OldId X (SD a b))
    (l : BitWord g) (hs : hasRow db (addr X z.2.1.val.val.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual z.2.1.val.val).1.1.1) = true) :
    withLane (idCode X z).2.1 (residualIndex a (2 ^ g, db, layout) (idCode X z) (wordNum l)) =
      arcCode X (motifAtLane X layout z l).val := by
  unfold residualIndex
  rw [idEnd_spec X h (SD a b) false layout z hs ht]
  have hzero : z.2.1.val.val.1.1.2.2 = 0 := z.2.1.property
  simp only [idCode, pickRole, Bool.cond_false, siteCode, withLane, arcCode, bundleCode, motifAtLane,
    PackingData.translateMotif, translateArc, translateSite, hzero, zero_add, wordNum_sub]

theorem genuineWidth_spec {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
    (layout : Bool) (j : TagW a) (z : OldId X (SD a b))
    (hz : typedEnd X (SD a b) false layout z = (x,j)) (l : BitWord g) :
    genuineWidth B a (SD a b) (2 ^ g, db, layout) (baseMotifRows a (2 ^ g) db) (idCode X z) (wordNum l) =
      splitWidth (X.packingData.termWidths B X.shrinkNumber X.packingWidth s
        (motifAtLane X layout z l) layout z.1) (SD a b z.1) z.2.2 := by
  let m := motifAtLane X layout z l
  obtain ⟨hs, ht⟩ := nearEnds X h.toLocalRows (SD a b) false layout z (by rw [hz]; simp)
  have dist₂ := role_ends X layout (sourceRole layout z.1) z.2.1.val
  have hx : (X.packingData.survivingRole layout (sourceRole layout z.1) z.2.1.val).1 = x :=
    congrArg Prod.fst hz
  rw [hx] at dist₂
  have hc : (baseGraph X).edist x (X.packingData.C z.2.1.val).1.1 ≤ 2 := by
    rcases C_base X z.2.1.val with he | he <;> rw [he]
    · exact dist₂.1
    · exact dist₂.2
  have hb : (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2 := by
    unfold m motifAtLane
    rw [PackingData.bundle_translate]
    exact hc
  obtain ⟨hms, hmt⟩ := bundleEnds X h.toLocalRows m hb
  let bn := X.shrinkNumber (X.packingData.bundle m) ⟨m, rfl⟩
  have hab : splitWidthNum (bundleWidthNum a (2 ^ g) db (bundleCode X (X.packingData.bundle m)))
      (PackingData.pieceCount (oldDegree a) (colourBits a))
      (bundleRankNum a (2 ^ g, db, layout) (baseMotifRows a (2 ^ g) db)
        (bundleCode X (X.packingData.bundle m)) (arcCode X m.val)) =
      X.packingData.abWidth X.shrinkNumber X.packingWidth m := by
    rw [bundleWidthNum_spec B X s h _ hb, bundleRankNum_spec X h.toLocalRows layout m hb]
    exact splitWidthNum_spec _ _ bn
  unfold genuineWidth
  dsimp only
  rw [withLane_motifAtLane X h.toLocalRows.toGraphRows layout z l hs ht]
  rw [rolesRow_spec h.toLocalRows.toGraphRows layout m hms hmt]
  change splitWidthNum (supplyWidthNum B (splitWidthNum
    (bundleWidthNum a (2 ^ g) db (bundleCode X (X.packingData.bundle m))) _ _)
    (oldWidth a (2 ^ g) db (arcCode X m.val)) (read 0 (oldTerm a (2 ^ g) db (arcCode X m.val)) (termField layout z.1.val)))
    (read 1 (List.ofFn (SD a b)) z.1.val) z.2.2.val = _
  rw [hab, h.oldWidth_eq m.val hms, h.selected_eq m layout z.1 hms,
    read_ofFn_num 1 (SD a b) z.1, splitWidthNum_spec _ _ z.2.2,
    supplyWidthNum_spec B _ _ (s m).val (layout, z.1)]
  rfl

theorem widthAt_spec {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (j : TagW a) (i : Fin (2 ^ b)) (l : BitWord g) :
    let w := fun m t => X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t
    let kId := idAt a (∑ t, SD a b t)
      (localFibre a b (2 ^ g) db false layout (packedCode X (x,j))) i.val
    widthAt B a (SD a b) (2 ^ g,db,layout) (baseMotifRows a (2 ^ g) db) kId (wordNum l) =
      outWidths (outState X ready layout w) (x,j) i l := by
  let w := fun m t => X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t
  let f := (X.shrinkStateIndex ready layout).outgoing
  dsimp only
  rw [idAt_numberSide X h.toLocalRows ready false layout (x,j) (by simp) i]
  change widthAt B a (SD a b) (2 ^ g,db,layout) (baseMotifRows a (2 ^ g) db)
    (match f.symm ((x,j),i) with | .inl z => some (idCode X z) | .inr _ => none) (wordNum l) = _
  rcases he : f.symm ((x,j),i) with z | d
  · have hf : f (.inl z) = ((x,j),i) := (Equiv.eq_symm_apply f).mp he.symm
    have hz := (numberSide_end X ready false layout z).symm.trans (congrArg Prod.fst hf)
    change genuineWidth B a (SD a b) (2 ^ g, db, layout) (baseMotifRows a (2 ^ g) db)
      (idCode X z) (wordNum l) = _
    rw [genuineWidth_spec B X s h layout j z hz l]
    let r := (X.packingData.survivingLaneEquiv layout (SD a b)).symm (z,l)
    have hw := X.packingData.shrinkSlotWidth_genuine layout (SD a b) w f r
    simp only [PackingData.shrinkArcEquiv_genuine, r, Equiv.apply_symm_apply, hf] at hw
    exact hw.symm
  · have hf : f (.inr d) = ((x,j),i) := (Equiv.eq_symm_apply f).mp he.symm
    change 0 = _
    have hw := X.packingData.shrinkSlotWidth_padding layout (SD a b) w f d l
    rw [hf] at hw
    exact hw.symm

end P1SolC10SA.SolShrink
