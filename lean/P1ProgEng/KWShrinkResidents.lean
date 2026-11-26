import P1ProgEng.KWShrinkC10Bridge
import P1P5.KWRefresh
import P1P7.KernelRes

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7 P1P5.KW
open C10
open scoped P1ChkFinal.AstraC10

/-- The residual lane count and old table, with layout and the new site. -/
abbrev ResidentFrame := RoleArgs × SiteRow

def residentFrame (a : ℕ) (u : ShrinkKIn) : ResidentFrame :=
  let p := u.1.1.1
  let site := (p.1.1, u.1.1.2)
  ((laneCount a (rootTerms p.1.2 p.1.1), p.1.2, p.2), site)

@[fun_prop] theorem residentFrame_poly (a : ℕ) : Poly (residentFrame a) := by
  unfold residentFrame
  dsimp only
  fun_prop

theorem laneCount_spec {a g : ℕ} {terms : OldTerms}
    (h : terms.length = 2 ^ packingLaneBits a g) : laneCount a terms = 2 ^ g := by
  have hpow : 2 ^ packingLaneBits a g = (2 ^ colourBits a * oldDegree a * tagCount a) * 2 ^ g := by
    simp only [packingLaneBits, pow_add, colourBits, oldDegree, tagCount, Nat.mul_assoc]
  rw [laneCount, h, hpow, Nat.mul_div_cancel_left]
  positivity

theorem residentFrame_true {a b g : ℕ} {δ factor : ℝ} {k : Type} [Field k]
    (B : FixedBlock k demandSource demandTarget supply
      (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
    (j : TagW a) (l : BitWord g) (ps : List PosCode)
    (z : (X.shrinkNext B ready s).network.Half ((x,j),l)) (pad : Tally) :
    residentFrame a (shrinkKIn B ready g X s x j l ps z pad) =
      ((2 ^ g, codedBall B X s x, layoutBit B X s), siteCode X (x,j,l)) := by
  change ((laneCount a (rootTerms (codedBall B X s x) (addr X x)), codedBall B X s x,
    layoutBit B X s), siteCode X (x,j,l)) = _
  rw [laneCount_spec (a := a) (g := g) (codedBall_terms_length B X s x)]

def roleRow (a : ℕ) (role : PackedRole) (f : RoleArgs) (e : ArcRow) : SiteRow :=
  roleAt (rolesRow a f.1 f.2.1 f.2.2 e) (roleCode role)

@[fun_prop] theorem roleRow_poly (a : ℕ) (r : PackedRole) :
    Poly (fun p : RoleArgs × ArcRow => roleRow a r p.1 p.2) := by
  unfold roleRow
  fun_prop

/-- Keep the lane-zero motifs of the requested base and tag, then move their
role to the requested absolute lane. -/
noncomputable def roleMembers (a : ℕ) (r : PackedRole) (p : ResidentFrame) : List ArcRow :=
  let ms := baseMotifRows a p.1.1 p.1.2.1
  let rows := ms.filter fun e =>
    decide (childCode a (roleRow a r p.1 e) = childCode a p.2)
  rows.map fun e => withLane e (p.2.2.2 ^^^ (roleRow a r p.1 e).2.2)

theorem roleMembers_poly (a : ℕ) (r : PackedRole) : Poly (roleMembers a r) := by
  have hm : Poly (fun p : ResidentFrame => baseMotifRows a p.1.1 p.1.2.1) := by fun_prop
  have ht : Poly (fun p : ResidentFrame × ArcRow =>
      decide (childCode a (roleRow a r p.1.1 p.2) = childCode a p.1.2)) := C10.eqOn_poly (by fun_prop) (by fun_prop)
  have hkeep := (Code.Poly.identity.pair hm).compose (filterWith_poly _ ht)
  have hmap : Poly (fun p : ResidentFrame × ArcRow =>
      withLane p.2 (p.1.2.2.2 ^^^ (roleRow a r p.1.1 p.2).2.2)) := by fun_prop
  exact (Code.Poly.identity.pair hkeep).compose (mapWith_poly _ hmap)

noncomputable def residentRows (a : ℕ) (p : ResidentFrame) : List (ℕ × ArcRow) :=
  (List.ofFn fun j : Fin 6 =>
    (roleMembers a (partyRole p.1.2.2 j) p).map fun e => (j.val, e)).flatten

noncomputable def ownerRows (a : ℕ) (p : ResidentFrame) : List (ℕ × ArcRow) :=
  (List.ofFn fun t : Fin 4 =>
    (roleMembers a (internalRole p.1.2.2 t) p).map fun e => (t.val, e)).flatten

private theorem roleMembers_layout_poly (a : ℕ) (r : Bool → PackedRole) :
    Poly (fun p : ResidentFrame => roleMembers a (r p.1.2.2) p) := by
  have hb : Poly (fun p : ResidentFrame => p.1.2.2) := by fun_prop
  convert Code.Poly.choose hb (roleMembers_poly a (r true)) (roleMembers_poly a (r false)) using 1
  funext p
  cases p.1.2.2 <;> rfl

@[fun_prop] theorem residentRows_poly (a : ℕ) : Poly (residentRows a) := by
  unfold residentRows
  apply Code.Poly.compose _ flatten_poly
  apply fixedList_poly
  intro j
  exact (roleMembers_layout_poly a (fun l => partyRole l j)).compose
    (Code.Poly.maps _ (by fun_prop))

@[fun_prop] theorem ownerRows_poly (a : ℕ) : Poly (ownerRows a) := by
  unfold ownerRows
  apply Code.Poly.compose _ flatten_poly
  apply fixedList_poly
  intro t
  exact (roleMembers_layout_poly a (fun l => internalRole l t)).compose
    (Code.Poly.maps _ (by fun_prop))

theorem roleMembers_nodup (a : ℕ) (r : PackedRole) (p : ResidentFrame) :
    (roleMembers a r p).Nodup := by
  unfold roleMembers
  dsimp only
  apply (List.nodup_map_iff_inj_on ((baseMotifRows_nodup _ _ _).filter _)).mpr
  intro e he w hw hew
  have hm := (List.mem_filter.mp he).1
  have hn := (List.mem_filter.mp hw).1
  have erase (z : ArcRow) (hz : z ∈ baseMotifRows a p.1.1 p.1.2.1) :
      withLane z 0 = z := by
    unfold baseMotifRows at hz
    obtain ⟨_, _, hz⟩ := List.mem_flatMap.mp (List.mem_filter.mp hz).1
    obtain ⟨_, rfl⟩ := mem_baseMotifCandidates.mp hz
    rfl
  have hew' := congrArg (fun z => withLane z 0) hew
  change withLane e 0 = withLane w 0 at hew'
  rw [erase e hm, erase w hn] at hew'
  exact hew'

noncomputable def roleRows {n : ℕ} (a : ℕ) (r : Bool → Fin n → PackedRole)
    (p : ResidentFrame) : List (ℕ × ArcRow) :=
  (List.finRange n).flatMap fun i => (roleMembers a (r p.1.2.2 i) p).map fun e => (i.val,e)

theorem roleRows_nodup {n : ℕ} (a : ℕ) (r : Bool → Fin n → PackedRole) (p : ResidentFrame) :
    (roleRows a r p).Nodup := by
  unfold roleRows
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact (roleMembers_nodup a _ p).map (fun _ _ e => congrArg Prod.snd e)
  · apply (List.nodup_finRange n).imp
    intro i j h z hi hj
    obtain ⟨ei, _, rfl⟩ := List.mem_map.mp hi
    obtain ⟨ej, _, he⟩ := List.mem_map.mp hj
    exact h (Fin.ext (congrArg Prod.fst he).symm)

theorem residentRows_eq (a : ℕ) (p : ResidentFrame) :
    residentRows a p = roleRows a partyRole p := by
  unfold residentRows roleRows
  rw [List.ofFn_eq_map, List.flatten_eq_flatMap, List.flatMap_map]
  rfl

theorem ownerRows_eq (a : ℕ) (p : ResidentFrame) :
    ownerRows a p = roleRows a internalRole p := by
  unfold ownerRows roleRows
  rw [List.ofFn_eq_map, List.flatten_eq_flatMap, List.flatMap_map]
  rfl

section Geometry

variable {a g : ℕ} (X : State a (packingLaneBits a g))

theorem roleRow_spec {db : BallRows} (h : GraphRows X db) (layout : Bool)
    (r : PackedRole) (m : X.packingData.Motif)
    (hs : hasRow db (addr X m.val.1.1.1) = true)
    (ht : hasRow db (addr X (X.packingData.actual m.val).1.1.1) = true) :
    roleRow a r (2 ^ g, db, layout) (arcCode X m.val) =
      siteCode X (X.packingData.survivingRole layout r m) := by
  unfold roleRow
  dsimp only
  rw [rolesRow_spec h layout m hs ht]
  cases r <;> rfl

theorem roleMembers_spec {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (layout : Bool) (r : PackedRole) (j : TagW a) (l : BitWord g) (row : ArcRow) :
    row ∈ roleMembers a r ((2 ^ g, db, layout), siteCode X (x,j,l)) ↔
    ∃ m : X.packingData.Motif, arcCode X m.val = row ∧
      X.packingData.survivingRole layout r m = (x,j,l) := by
  let role := X.packingData.survivingRole layout r
  let he := X.packingData.survivingRole_translate layout r
  let equiv := X.packingData.roleLaneEquiv role he
  have atLane (m : X.packingData.BaseMotif) :
      role (equiv.symm (m,l)) = ((role m.val).1,(role m.val).2.1,l) :=
    (X.packingData.roleLane_endpoints role role he he m l).1
  have hcode (m : X.packingData.BaseMotif) (hs : hasRow db (addr X m.val.val.1.1.1) = true)
      (ht : hasRow db (addr X (X.packingData.actual m.val.val).1.1.1) = true) :
      withLane (arcCode X m.val.val) (wordNum l ^^^
        (roleRow a r (2 ^ g, db, layout) (arcCode X m.val.val)).2.2) =
      arcCode X (equiv.symm (m,l)).val := by
    rw [roleRow_spec X h.toGraphRows layout r m.val hs ht]
    change _ = arcCode X (X.packingData.translateMotif m.val (l - (role m.val).2.2)).val
    have hz : m.val.val.1.1.2.2 = 0 := m.property
    simp only [siteCode, withLane, arcCode, bundleCode, PackingData.translateMotif,
      translateArc, translateSite, hz, zero_add, wordNum_sub, role]
  have hrow (m : X.packingData.BaseMotif)
      (hs : hasRow db (addr X m.val.val.1.1.1) = true)
      (ht : hasRow db (addr X (X.packingData.actual m.val.val).1.1.1) = true) :
      childCode a (roleRow a r (2 ^ g,db,layout) (arcCode X m.val.val)) =
        childCode a (siteCode X (x,j,l)) ↔
      role (equiv.symm (m,l)) = (x,j,l) := by
    rw [roleRow_spec X h.toGraphRows layout r m.val hs ht, atLane]
    change packedCode X ((role m.val).1,(role m.val).2.1) = packedCode X (x,j) ↔ _
    constructor
    · intro hh
      have hh := packedCode_injective X hh
      exact congrArg (fun p : Packed X => (p.1,p.2,l)) hh
    · intro hh
      exact congrArg (fun p : OldSite X => packedCode X (p.1,p.2.1)) hh
  unfold roleMembers
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨e, ⟨hme, hm⟩, rfl⟩
    obtain ⟨m, rfl, hs, ht⟩ := (baseMotifRows_spec h.toGraphRows h.addr_mem e).mp hme
    exact ⟨equiv.symm (m,l), (hcode m hs ht).symm,
      (hrow m hs ht).mp (of_decide_eq_true hm)⟩
  · rintro ⟨m, rfl, hm⟩
    change role m = (x,j,l) at hm
    let q := X.packingData.baseMotif m
    have hqm : equiv.symm (q,l) = m := by
      apply equiv.injective
      rw [Equiv.apply_symm_apply]
      change (q,l) = (q,(role m).2.2)
      rw [hm]
    have hbase : (role q.val).1 = x := by
      have hq := atLane q
      rw [hqm, hm] at hq
      exact (congrArg Prod.fst hq).symm
    obtain ⟨hd₁, hd₂⟩ := role_ends X layout r q.val
    rw [show (X.packingData.survivingRole layout r q.val).1 = x from hbase] at hd₁ hd₂
    have hs := h.cover _ (hd₁.trans (by norm_num))
    have ht := h.cover _ (hd₂.trans (by norm_num))
    refine ⟨arcCode X q.val.val, ⟨(baseMotifRows_spec h.toGraphRows h.addr_mem _).mpr
      ⟨q,rfl,hs,ht⟩, decide_eq_true ((hrow q hs ht).mpr ((congrArg role hqm).trans hm))⟩, ?_⟩
    exact (hcode q hs ht).trans (congrArg (fun m : X.packingData.Motif => arcCode X m.val) hqm)

theorem roleRows_spec {n : ℕ} {x : X.Base} {db : BallRows} (h : LocalRows X x db)
    (layout : Bool) (r : Bool → Fin n → PackedRole) (j : TagW a) (l : BitWord g)
    (row : ℕ × ArcRow) :
    row ∈ roleRows a r ((2 ^ g,db,layout), siteCode X (x,j,l)) ↔
    ∃ p : {p : X.packingData.Motif × Fin n //
        X.packingData.survivingRole layout (r layout p.2) p.1 = (x,j,l)},
      (p.val.2.val, arcCode X p.val.1.val) = row := by
  unfold roleRows
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨i,e,he,rfl⟩
    obtain ⟨m, rfl, hm⟩ := (roleMembers_spec X h layout (r layout i) j l e).mp he
    exact ⟨⟨(m,i),hm⟩,rfl⟩
  · rintro ⟨⟨⟨m,i⟩,hm⟩,rfl⟩
    exact ⟨i,arcCode X m.val,
      (roleMembers_spec X h layout (r layout i) j l _).mpr ⟨m,rfl,hm⟩,rfl⟩

end Geometry

end P1ProgEng.SolKWS
