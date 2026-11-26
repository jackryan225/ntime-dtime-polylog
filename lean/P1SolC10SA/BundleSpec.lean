import P1SolC10SA.RankSpec
import P1SolC10SA.PanelProgram

namespace P1SolC10SA.SolShrink

open OAI.Computability.VPVNP.Compression
open P1P7

variable {a g : ℕ} (X : State a (packingLaneBits a g))

noncomputable local instance : DecidableEq X.Base := Classical.decEq _

def projectedBundle (p : OldBundle X) : Packed X × Fin (oldDegree a) :=
  (packedBase p.1, p.2)

theorem bundleKey_spec (u : OldBundle X) :
    bundleKey a (bundleCode X u) = packedCode X (projectedBundle X u).1 * oldDegree a + u.2.val :=
  rfl

theorem bundleKey_eq_iff (u v : OldBundle X) :
    bundleKey a (bundleCode X u) = bundleKey a (bundleCode X v) ↔
      projectedBundle X u = projectedBundle X v := by
  rw [bundleKey_spec X u, bundleKey_spec X v]
  constructor
  · intro h
    have h₁ := congrArg (fun n => n / oldDegree a) h
    have h₂ := congrArg (fun n => n % oldDegree a) h
    change (_ * oldDegree a + u.2.val) / oldDegree a = (_ * oldDegree a + v.2.val) / oldDegree a at h₁
    change (_ * oldDegree a + u.2.val) % oldDegree a = (_ * oldDegree a + v.2.val) % oldDegree a at h₂
    rw [div_radix u.2.isLt, div_radix v.2.isLt] at h₁
    rw [mod_radix u.2.isLt, mod_radix v.2.isLt] at h₂
    exact Prod.ext (packedCode_injective X h₁) (Fin.ext h₂)
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ : u.2 = v.2 := congrArg (fun p : Packed X × Fin (oldDegree a) => p.2) h
    rw [h₁,h₂]

theorem projectedBundle_translate (m : X.packingData.Motif) (l : BitWord g) :
    projectedBundle X (X.packingData.bundle (X.packingData.translateMotif m l)) =
      projectedBundle X (X.packingData.bundle m) := by
  rw [PackingData.bundle_translate]
  rfl

theorem projectedBundle_baseMotif (m : X.packingData.Motif) :
    projectedBundle X (X.packingData.bundle (X.packingData.baseMotif m).val) =
      projectedBundle X (X.packingData.bundle m) :=
  projectedBundle_translate X m (-X.packingData.sourceLane m)

theorem bundleEnds {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (m : X.packingData.Motif) (hb : (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2) :
    hasRow db (addr X m.val.1.1.1) = true ∧
      hasRow db (addr X (X.packingData.actual m.val).1.1.1) = true := by
  change (baseGraph X).edist x (X.packingData.C m).1.1 ≤ 2 at hb
  obtain ⟨hs, ht⟩ := ends_of_base X m (C_base X m)
  exact ⟨h.cover _ ((edist_le_three hb hs).trans (by norm_num)),
    h.cover _ ((edist_le_three hb ht).trans (by norm_num))⟩

/-- The lane-zero label of a motif is an injective code when the actual bundle is fixed. -/
def fibreMotifCode (b : OldBundle X) (m : X.packingData.MotifFiber b) : ArcRow :=
  arcCode X (X.packingData.baseMotif m.val).val.val

theorem fibreMotifCode_injective (b : OldBundle X) : Function.Injective (fibreMotifCode X b) := by
  intro u v h
  have hm : X.packingData.baseMotif u.val = X.packingData.baseMotif v.val :=
    Subtype.ext (Subtype.ext (arcCode_injective X h))
  apply X.packingData.motifFiberIndex_injective X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) b
  change X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
      (X.packingData.baseMotif u.val) =
    X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
      (X.packingData.baseMotif v.val)
  rw [hm]

/-- Restore the lane of a candidate at the given absolute bundle on its projected base. -/
theorem fibreMotifCode_exists (b : OldBundle X) (m : X.packingData.BaseMotif)
    (hm : projectedBundle X (X.packingData.bundle m.val) = projectedBundle X b) :
    ∃ u : X.packingData.MotifFiber b, fibreMotifCode X b u = arcCode X m.val.val := by
  let s := (X.packingData.bundle m.val).1
  let u := X.packingData.translateMotif m.val (b.1.2.2 - s.2.2)
  have hbase : s.1 = b.1.1 := congrArg (fun p => p.1.1) hm
  have htag : s.2.1 = b.1.2.1 := congrArg (fun p => p.1.2) hm
  have hport : (X.packingData.bundle m.val).2 = b.2 :=
    congrArg (fun p : Packed X × Fin (oldDegree a) => p.2) hm
  have hb : X.packingData.bundle u = b := by
    dsimp only [u]
    rw [PackingData.bundle_translate]
    refine Prod.ext (Prod.ext hbase (Prod.ext htag ?_)) hport
    change s.2.2 + (b.1.2.2 - s.2.2) = b.1.2.2
    rw [add_comm, sub_add_cancel]
  refine ⟨⟨u,hb⟩, ?_⟩
  have hz := (X.packingData.baseMotif_translate m.val (b.1.2.2 - s.2.2)).trans
    (X.packingData.baseMotif_coe m)
  exact congrArg (fun m : X.packingData.BaseMotif => arcCode X m.val.val) hz

theorem bundleRankNum_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (layout : Bool) (m : X.packingData.Motif)
    (hb : (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2) :
    bundleRankNum a (2 ^ g, db, layout) (baseMotifRows a (2 ^ g) db)
      (bundleCode X (X.packingData.bundle m)) (arcCode X m.val) =
      (X.shrinkNumber (X.packingData.bundle m) ⟨m,rfl⟩).val := by
  classical
  let b := X.packingData.bundle m
  let enc := fibreMotifCode X b
  let native := (Finset.univ : Finset (X.packingData.MotifFiber b)).filter (fun u => arcKey X u.val.val < arcKey X m.val)
  let rows := (baseMotifRows a (2 ^ g) db).filter (fun r =>
    decide (bundleKey a (rolesRow a (2 ^ g) db layout r).1 = bundleKey a (bundleCode X b)) &&
    decide (motifKey a r < motifKey a (arcCode X m.val)))
  have hrank : ∀ u : X.packingData.MotifFiber b, motifKey a (enc u) = arcKey X u.val.val := by
    intro u
    exact (motifKey_spec _).trans (arcKey_baseMotif X u.val)
  have hl : rows.toFinset = native.image enc := by
    ext r
    simp only [rows, List.mem_toFinset, List.mem_filter, Bool.and_eq_true_iff, Finset.mem_image]
    constructor
    · rintro ⟨hr, hb', hk⟩
      obtain ⟨w, rfl, hs, ht⟩ := (baseMotifRows_spec h.toGraphRows h.addr_mem r).mp hr
      rw [rolesRow_spec h.toGraphRows layout w.val hs ht] at hb'
      have he : projectedBundle X (X.packingData.bundle w.val) = projectedBundle X b :=
        (bundleKey_eq_iff X _ _).mp (of_decide_eq_true hb')
      obtain ⟨u, hu⟩ := fibreMotifCode_exists X b w he
      change enc u = _ at hu
      have hk' := of_decide_eq_true hk
      rw [← hu, hrank u, motifKey_spec] at hk'
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, hu⟩
    · rintro ⟨u, hu, rfl⟩
      let w := X.packingData.baseMotif u.val
      have he := (projectedBundle_baseMotif X u.val).trans (congrArg (projectedBundle X) u.property)
      have hd : (baseGraph X).edist x (X.packingData.bundle w.val).1.1 ≤ 2 := by
        change projectedBundle X (X.packingData.bundle w.val) = projectedBundle X b at he
        have hbase : (X.packingData.bundle w.val).1.1 = b.1.1 :=
          congrArg (fun p : Packed X × Fin (oldDegree a) => p.1.1) he
        rw [hbase]
        exact hb
      obtain ⟨hs,ht⟩ := bundleEnds X h w.val hd
      have hrow : enc u ∈ baseMotifRows a (2 ^ g) db :=
        (baseMotifRows_spec h.toGraphRows h.addr_mem _).mpr ⟨w,rfl,hs,ht⟩
      refine ⟨hrow, decide_eq_true ?_, decide_eq_true ?_⟩
      · change bundleKey a (rolesRow a (2 ^ g) db layout (arcCode X w.val.val)).1 = _
        rw [rolesRow_spec h.toGraphRows layout w.val hs ht]
        exact (bundleKey_eq_iff X _ _).mpr he
      · rw [hrank u, motifKey_spec]
        exact (Finset.mem_filter.mp hu).2
  have hn : rows.Nodup := (baseMotifRows_nodup a (2 ^ g) db).filter _
  change rows.length = _
  rw [← List.toFinset_card_of_nodup hn, hl, Finset.card_image_of_injective _ (fibreMotifCode_injective X b),
    P1P7.bundle_rank, Fintype.card_subtype]

end P1SolC10SA.SolShrink
