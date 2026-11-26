import P1SolC10SA.MotifSpec
import P1SolC10SA.Numbered
import P1P7.ShrinkPanel

namespace P1SolC10SA.SolShrink

open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1P7

theorem idRowsAt_mem {sd : Fin 4 → ℕ} {e : ArcRow} {z : IdRow} :
    z ∈ idRowsAt sd e ↔ ∃ t : Fin 4, ∃ i : Fin (sd t), z = (t.val, e, i.val) := by
  unfold idRowsAt
  constructor
  · intro h
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    exact ⟨_, _, hj.symm⟩
  · rintro ⟨t, i, rfl⟩
    let f := Fintype.equivFin (Σ t : Fin 4, Fin (sd t))
    exact List.mem_ofFn.mpr ⟨f ⟨t, i⟩, congrArg (attachId sd e) (f.symm_apply_apply _)⟩

theorem idRowsAt_nodup (sd : Fin 4 → ℕ) (e : ArcRow) : (idRowsAt sd e).Nodup := by
  unfold idRowsAt
  apply List.nodup_ofFn_ofInjective
  intro j k h
  let f := (Fintype.equivFin (Σ t : Fin 4, Fin (sd t))).symm
  apply f.injective
  have h₁ : (f j).1 = (f k).1 := Fin.ext (congrArg (fun r : IdRow => r.1) h)
  have h₂ : ((f j).2 : ℕ) = (f k).2 := congrArg (fun r : IdRow => r.2.2) h
  rcases hj : f j with ⟨t₁, i₁⟩
  rcases hk : f k with ⟨t₂, i₂⟩
  rw [hj, hk] at h₁ h₂
  change t₁ = t₂ at h₁
  subst t₂
  rw [show i₁ = i₂ from Fin.ext h₂]

theorem idRows_nodup (sd : Fin 4 → ℕ) {ms : List ArcRow} (h : ms.Nodup) :
    (idRows sd ms).Nodup := by
  unfold idRows
  apply List.nodup_flatMap.mpr
  refine ⟨fun e _ => idRowsAt_nodup sd e, h.imp ?_⟩
  intro e e' hn z h₁ h₂
  obtain ⟨t, i, ht⟩ := idRowsAt_mem.mp h₁
  obtain ⟨t', i', ht'⟩ := idRowsAt_mem.mp h₂
  exact hn (congrArg (fun r : IdRow => r.2.1) (ht.symm.trans ht'))

theorem bitWord_number_injective (g : ℕ) : Function.Injective (@wordNum g) :=
  fun _ _ h => (bitWordFinEquiv g).injective (Fin.ext h)

section Geometry

variable {a b g : ℕ} {δ : ℝ}
variable (X : State a (packingLaneBits a g))

abbrev Packed (X : State a (packingLaneBits a g)) := X.Base × TagW a

abbrev OldId (X : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) :=
  Id X.packingData.BaseMotif sd

def packedCode (p : Packed X) : ℕ := tagCount a * addr X p.1 + wordNum p.2

theorem packedCode_injective : Function.Injective (packedCode X) := by
  intro p q h
  unfold packedCode at h
  have h₁ := congrArg (fun n => n / tagCount a) h
  have h₂ := congrArg (fun n => n % tagCount a) h
  have hp : wordNum p.2 < tagCount a := wordNum_lt p.2
  have hq : wordNum q.2 < tagCount a := wordNum_lt q.2
  rw [Nat.mul_add_div (lt_of_le_of_lt (Nat.zero_le _) hp), Nat.mul_add_div (lt_of_le_of_lt (Nat.zero_le _) hq),
    Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hq, Nat.add_zero, Nat.add_zero] at h₁
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at h₂
  exact Prod.ext (X.baseIndex.injective (Fin.ext h₁)) (bitWord_number_injective _ h₂)

theorem arcCode_injective : Function.Injective (arcCode X) := by
  rintro ⟨⟨⟨x, t, r⟩, i⟩, u, h⟩ ⟨⟨⟨x', t', r'⟩, i'⟩, u', h'⟩ he
  simp only [arcCode, bundleCode, siteCode, Prod.mk.injEq] at he
  obtain ⟨⟨⟨hx, ht, hr⟩, hi⟩, hu, hh⟩ := he
  have ex : x = x' := X.baseIndex.injective (Fin.ext hx)
  have et := bitWord_number_injective _ ht
  have er := bitWord_number_injective _ hr
  have ei := Fin.ext hi
  have eu := bitWord_number_injective _ hu
  have eh := bitWord_number_injective _ hh
  subst x' t' r' i' u' h'
  rfl

def idCode {sd : Fin 4 → ℕ} (z : OldId X sd) : IdRow :=
  (z.1.val, arcCode X z.2.1.val.val, z.2.2.val)

theorem idCode_injective (sd : Fin 4 → ℕ) : Function.Injective (idCode X (sd := sd)) := by
  rintro ⟨t, m, i⟩ ⟨t', m', i'⟩ h
  have ht : t = t' := Fin.ext (congrArg (fun r : IdRow => r.1) h)
  subst t'
  have hm : m = m' := Subtype.ext (Subtype.ext (arcCode_injective X (congrArg (fun r : IdRow => r.2.1) h)))
  have hi : i = i' := Fin.ext (congrArg (fun r : IdRow => r.2.2) h)
  rw [hm, hi]

/-- A coded graph chart contains truthful graph fields and both old endpoints of nearby motifs. -/
structure LocalRows (x : X.Base) (db : BallRows) : Prop extends GraphRows X db where
  addr_mem : ∀ i ∈ db.map Prod.fst, ∃ y, addr X y = i
  cover : ∀ y, (baseGraph X).edist x y ≤ 6 → hasRow db (addr X y) = true

def pickRole (incoming layout : Bool) : Fin 4 → PackedRole :=
  bif incoming then targetRole layout else sourceRole layout

theorem endRoleCode_spec (incoming layout : Bool) (t : Fin 4) :
    endRoleCode incoming layout t.val = roleCode (pickRole incoming layout t) := by
  cases incoming <;> cases layout <;>
    simp only [endRoleCode, roleTable, pickRole, Bool.cond_true, Bool.cond_false, read,
      List.getElem?_ofFn, t.isLt, dite_true, Option.getD_some]

abbrev typedEnd (sd : Fin 4 → ℕ) (incoming layout : Bool) (z : OldId X sd) : Packed X :=
  endpoint (X.packingData.roleBase layout) (pickRole incoming layout) z

theorem idEnd_spec {db : BallRows} (h : GraphRows X db) (sd : Fin 4 → ℕ)
    (incoming layout : Bool) (z : OldId X sd)
    (hs : hasRow db (addr X z.2.1.val.val.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual z.2.1.val.val).1.1.1) = true) :
    idEnd a incoming (2 ^ g, db, layout) (idCode X z) =
      siteCode X (X.packingData.survivingRole layout (pickRole incoming layout z.1) z.2.1.val) := by
  unfold idEnd idCode
  dsimp only
  rw [rolesRow_spec h layout z.2.1.val hs ht, endRoleCode_spec]
  cases pickRole incoming layout z.1 <;> rfl

theorem child_idEnd_spec {db : BallRows} (h : GraphRows X db) (sd : Fin 4 → ℕ)
    (incoming layout : Bool) (z : OldId X sd)
    (hs : hasRow db (addr X z.2.1.val.val.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual z.2.1.val.val).1.1.1) = true) :
    childCode a (idEnd a incoming (2 ^ g, db, layout) (idCode X z)) =
      packedCode X (typedEnd X sd incoming layout z) := by
  rw [idEnd_spec X h sd incoming layout z hs ht]
  rfl

theorem nearEnds {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (sd : Fin 4 → ℕ) (incoming layout : Bool) (z : OldId X sd)
    (hw : (baseGraph X).edist x (typedEnd X sd incoming layout z).1 ≤ 4) :
    hasRow db (addr X z.2.1.val.val.1.1.1) = true ∧
      hasRow db (addr X (X.packingData.actual z.2.1.val.val).1.1.1) = true := by
  obtain ⟨h₁, h₂⟩ := role_ends X layout (pickRole incoming layout z.1) z.2.1.val
  let p := (typedEnd X sd incoming layout z).1
  have narrow (y : X.Base) (hy : (baseGraph X).edist p y ≤ 2) :
      (baseGraph X).edist x y ≤ 6 :=
    (SimpleGraph.edist_triangle (v := p)).trans ((add_le_add hw hy).trans (by norm_num))
  exact ⟨h.cover _ (narrow _ h₁), h.cover _ (narrow _ h₂)⟩

noncomputable abbrev ballIds (a b l : ℕ) (db : BallRows) : List IdRow :=
  idRows (SD a b) (baseMotifRows a l db)

theorem idRows_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (sd : Fin 4 → ℕ) (r : IdRow) :
    r ∈ idRows sd (baseMotifRows a (2 ^ g) db) ↔
      ∃ z : OldId X sd, idCode X z = r ∧
        hasRow db (addr X z.2.1.val.val.1.1.1) = true ∧
        hasRow db (addr X (X.packingData.actual z.2.1.val.val).1.1.1) = true := by
  unfold idRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hr⟩
    obtain ⟨t, i, rfl⟩ := idRowsAt_mem.mp hr
    obtain ⟨m, rfl, hs, ht⟩ := (baseMotifRows_spec h.toGraphRows h.addr_mem e).mp he
    exact ⟨⟨t, m, i⟩, rfl, hs, ht⟩
  · rintro ⟨z, rfl, hs, ht⟩
    refine ⟨arcCode X z.2.1.val.val, ?_, idRowsAt_mem.mpr ⟨z.1, z.2.2, rfl⟩⟩
    exact (baseMotifRows_spec h.toGraphRows h.addr_mem _).mpr ⟨z.2.1, rfl, hs, ht⟩

theorem idFibre_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (sd : Fin 4 → ℕ) (incoming layout : Bool) (p : Packed X)
    (hp : (baseGraph X).edist x p.1 ≤ 4) (r : IdRow) :
    r ∈ idFibre a incoming (2 ^ g, db, layout) (packedCode X p)
      (idRows sd (baseMotifRows a (2 ^ g) db)) ↔
      ∃ z : OldId X sd, typedEnd X sd incoming layout z = p ∧ idCode X z = r := by
  unfold idFibre
  rw [List.mem_filter]
  constructor
  · rintro ⟨hr, he⟩
    obtain ⟨z, rfl, hs, ht⟩ := (idRows_spec X h sd r).mp hr
    have hq := of_decide_eq_true he
    rw [child_idEnd_spec X h.toGraphRows sd incoming layout z hs ht] at hq
    exact ⟨z, packedCode_injective X hq, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hs, ht⟩ := nearEnds X h sd incoming layout z (by rw [hz]; exact hp)
    refine ⟨(idRows_spec X h sd _).mpr ⟨z, rfl, hs, ht⟩, decide_eq_true ?_⟩
    exact (child_idEnd_spec X h.toGraphRows sd incoming layout z hs ht).trans (congrArg (packedCode X) hz)

theorem keyLT_spec (sd : Fin 4 → ℕ) (u v : OldId X sd) :
    keyLT (idKey a (∑ t, sd t) (idCode X u), idKey a (∑ t, sd t) (idCode X v)) = true ↔
      okey sd X u < okey sd X v := by
  simp only [keyLT, idKey, idCode, motifKey_spec, okey, Prod.Lex.toLex_lt_toLex,
    Bool.or_eq_true, Bool.and_eq_true_iff]
  constructor
  · rintro (h | ⟨he, hl⟩)
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr ⟨of_decide_eq_true he, of_decide_eq_true hl⟩
  · rintro (h | ⟨he, hl⟩)
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr ⟨decide_eq_true he, decide_eq_true hl⟩

noncomputable abbrev localFibre (a b l : ℕ) (db : BallRows) (incoming layout : Bool) (p : ℕ) : List IdRow :=
  idFibre a incoming (l, db, layout) p (ballIds a b l db)

theorem idRank_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (sd : Fin 4 → ℕ) (incoming layout : Bool) (p : Packed X)
    (hp : (baseGraph X).edist x p.1 ≤ 4) (z : OldId X sd) :
    idRank a (∑ t, sd t)
      (idFibre a incoming (2 ^ g, db, layout) (packedCode X p) (idRows sd (baseMotifRows a (2 ^ g) db)))
      (idCode X z) =
    ((fib X sd layout (pickRole incoming layout) p).filter (fun w => okey sd X w < okey sd X z)).card := by
  classical
  let zs := idFibre a incoming (2 ^ g, db, layout) (packedCode X p)
    (idRows sd (baseMotifRows a (2 ^ g) db))
  let ok := fun r => keyLT (idKey a (∑ t, sd t) r, idKey a (∑ t, sd t) (idCode X z))
  let typed := (fib X sd layout (pickRole incoming layout) p).filter (fun w => okey sd X w < okey sd X z)
  have hn : (zs.filter ok).Nodup :=
    ((idRows_nodup sd (baseMotifRows_nodup a (2 ^ g) db)).filter _).filter _
  have hset : (zs.filter ok).toFinset = typed.image (idCode X) := by
    ext r
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hr, hk⟩
      obtain ⟨u, he, rfl⟩ := (idFibre_spec X h sd incoming layout p hp _).mp hr
      refine ⟨u, Finset.mem_filter.mpr ⟨(mem_fib X sd layout _ _ _).mpr he, ?_⟩, rfl⟩
      exact (keyLT_spec X sd u z).mp hk
    · rintro ⟨u, he, rfl⟩
      obtain ⟨he, hk⟩ := Finset.mem_filter.mp he
      exact ⟨(idFibre_spec X h sd incoming layout p hp _).mpr
        ⟨u, (mem_fib X sd layout _ _ _).mp he, rfl⟩, (keyLT_spec X sd u z).mpr hk⟩
  change (zs.filter ok).length = typed.card
  rw [← List.toFinset_card_of_nodup hn, hset, Finset.card_image_of_injective _ (idCode_injective X sd)]

noncomputable abbrev numberSide (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (incoming layout : Bool) :=
  bif incoming then (X.shrinkStateIndex ready layout).incoming else (X.shrinkStateIndex ready layout).outgoing

theorem numberSide_end (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (incoming layout : Bool) (z : OldId X (SD a b)) :
    (numberSide X ready incoming layout (.inl z)).1 = typedEnd X (SD a b) incoming layout z := by
  cases incoming
  · exact (X.shrinkStateIndex ready layout).src_eq (.inl z)
  · exact (X.shrinkStateIndex ready layout).dst_eq (.inl z)

theorem numberSide_rank {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (incoming layout : Bool) (p : Packed X) (hp : (baseGraph X).edist x p.1 ≤ 4)
    (z : OldId X (SD a b)) (hz : typedEnd X (SD a b) incoming layout z = p) :
    (numberSide X ready incoming layout (.inl z)).2.val =
      idRank a (∑ t, SD a b t) (localFibre a b (2 ^ g) db incoming layout (packedCode X p)) (idCode X z) := by
  rw [idRank_spec X h (SD a b) incoming layout p hp z, ← hz]
  cases incoming
  · exact out_rank X ready layout z
  · exact in_rank X ready layout z

theorem idAt_present {total : ℕ} {zs : List IdRow} {z : IdRow} (hz : z ∈ zs)
    (huniq : ∀ w ∈ zs, idRank a total zs w = idRank a total zs z → w = z) :
    idAt a total zs (idRank a total zs z) = some z := by
  unfold idAt
  have hm : (idRank a total zs z, some z) ∈ zs.map (fun u => (idRank a total zs u, some u)) :=
    List.mem_map.mpr ⟨z, hz, rfl⟩
  apply lookup_eq_of_mem hm
  intro w hw
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hw
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  rw [huniq u hu h₁] at h₂
  exact h₂.symm

theorem idAt_absent {total : ℕ} {zs : List IdRow} {k : ℕ}
    (h : ∀ z ∈ zs, idRank a total zs z ≠ k) : idAt a total zs k = none := by
  unfold idAt
  apply lookup_default_of_absent
  intro hk
  rw [List.map_map] at hk
  obtain ⟨z, hz, he⟩ := List.mem_map.mp hk
  exact h z hz he

theorem idAt_numberSide {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (incoming layout : Bool) (p : Packed X) (hp : (baseGraph X).edist x p.1 ≤ 4) (k : Fin (2 ^ b)) :
    idAt a (∑ t, SD a b t) (localFibre a b (2 ^ g) db incoming layout (packedCode X p)) k.val =
      match (numberSide X ready incoming layout).symm (p, k) with
      | .inl z => some (idCode X z)
      | .inr _ => none := by
  let f := numberSide X ready incoming layout
  let zs := localFibre a b (2 ^ g) db incoming layout (packedCode X p)
  have frame (z : OldId X (SD a b)) (hz : typedEnd X (SD a b) incoming layout z = p) :
      f (.inl z) = (p, k) ↔ idRank a (∑ t, SD a b t) zs (idCode X z) = k.val := by
    have hp₁ : (f (.inl z)).1 = p := (numberSide_end X ready incoming layout z).trans hz
    have hp₂ := numberSide_rank X h ready incoming layout p hp z hz
    constructor
    · intro ha
      exact hp₂.symm.trans (congrArg (fun w => (w.2 : ℕ)) ha)
    · intro ha
      exact Prod.ext hp₁ (Fin.ext (hp₂.trans ha))
  have mem (r : IdRow) : r ∈ zs ↔
      ∃ z : OldId X (SD a b), typedEnd X (SD a b) incoming layout z = p ∧ idCode X z = r :=
    idFibre_spec X h (SD a b) incoming layout p hp r
  change idAt a (∑ t, SD a b t) zs k.val = _
  rcases ht : f.symm (p, k) with z | d
  · have hf : f (.inl z) = (p, k) := (Equiv.eq_symm_apply f).mp ht.symm
    have he : typedEnd X (SD a b) incoming layout z = p :=
      (numberSide_end X ready incoming layout z).symm.trans (congrArg Prod.fst hf)
    have hr := (frame z he).mp hf
    change idAt a (∑ t, SD a b t) zs k.val = some (idCode X z)
    rw [← hr]
    apply idAt_present ((mem _).mpr ⟨z, he, rfl⟩)
    intro w hw hwr
    obtain ⟨u, hue, rfl⟩ := (mem w).mp hw
    have hfu := (frame u hue).mpr (hwr.trans hr)
    have hu : u = z := Sum.inl.inj (f.injective (hfu.trans hf.symm))
    rw [hu]
  · have hf : f (.inr d) = (p, k) := (Equiv.eq_symm_apply f).mp ht.symm
    change idAt a (∑ t, SD a b t) zs k.val = none
    apply idAt_absent
    intro w hw hwr
    obtain ⟨u, hue, rfl⟩ := (mem w).mp hw
    have hfu := (frame u hue).mpr hwr
    have hbad := f.injective (hfu.trans hf.symm)
    cases hbad

end Geometry

end P1SolC10SA.SolShrink
