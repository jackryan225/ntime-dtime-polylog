import P1ProgEng.KWShrinkOldWords
import P1ProgEng.KWShrinkWidths
import P1ProgEng.KWShrinkWordLayout
import P1P7.KernelThick

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.MultitapeWeakETH
open P1P7 P1P5.KW
open C10
open scoped P1ChkFinal.AstraC10

noncomputable section

abbrev DemandArgs := RoleArgs × List PosCode × ArcRow

def demandBundle (a : ℕ) (p : RoleArgs × ArcRow) : BundleRow :=
  (rolesRow a p.1.1 p.1.2.1 p.1.2.2 p.2).1

@[fun_prop] theorem demandBundle_poly (a : ℕ) : Poly (demandBundle a) := by
  unfold demandBundle
  fun_prop

/-- All colour and label coordinates of the bundle, in thick-key order.
A coordinate which fails either thickness test contributes an empty word. -/
def thickWord (a : ℕ) (incoming : Bool) (i : Fin (2 ^ colourBits a * oldDegree a))
    (p : RoleArgs × List PosCode × BundleRow) : List Bool :=
  let q : Fin (2 ^ colourBits a) × Fin (oldDegree a) := finProdFinEquiv.symm i
  let e : ArcRow := (p.2.2,q.1.val,q.2.val)
  let db := p.1.2.1
  let actual := codedTarget a p.1.1 db e
  bif codedThick a db (sourceRow e) && codedThick a db (sourceRow actual)
    then packedWord a incoming (p.1,p.2.1,e) else []

theorem thickWord_poly (a : ℕ) (incoming : Bool) (i : Fin (2 ^ colourBits a * oldDegree a)) :
    Poly (thickWord a incoming i) := by
  unfold thickWord
  dsimp only
  apply Code.Poly.choose <;> fun_prop

def thickWords (a : ℕ) (incoming : Bool) (p : RoleArgs × List PosCode × BundleRow) :
    List (List Bool) :=
  List.ofFn fun i => thickWord a incoming i p

theorem thickWords_poly (a : ℕ) (incoming : Bool) : Poly (thickWords a incoming) :=
  fixedList_poly _ (thickWord_poly a incoming)

/-- Offset of the AB slice in the thick words of its bundle. -/
def codedABOffset (a : ℕ) (p : RoleArgs × ArcRow) : ℕ :=
  let f := p.1
  let b := demandBundle a p
  let w := bundleWidthNum a f.1 f.2.1 b
  let q := PackingData.pieceCount (oldDegree a) (colourBits a)
  let rank := bundleRankNum a f (baseMotifRows a f.1 f.2.1) b p.2
  widthPrefix (List.ofFn (fun i : Fin q => splitWidthNum w q i.val),rank)

@[fun_prop] theorem codedABOffset_poly (a : ℕ) : Poly (codedABOffset a) := by
  unfold codedABOffset
  dsimp only
  apply Code.Poly.compose _ widthPrefix_poly
  apply Code.Poly.pair
  · apply fixedList_poly
    intro i
    fun_prop
  · fun_prop

def demandABWord (a : ℕ) (incoming : Bool) (p : DemandArgs) : List Bool :=
  let m := (p.1,p.2.2)
  let words := (thickWords a incoming (p.1,p.2.1,demandBundle a m)).flatten
  (words.drop (codedABOffset a m)).take (codedAB a m)

theorem demandABWord_poly (a : ℕ) (incoming : Bool) : Poly (demandABWord a incoming) := by
  unfold demandABWord
  dsimp only
  have hw : Poly (fun p : DemandArgs => (thickWords a incoming
      (p.1,p.2.1,demandBundle a (p.1,p.2.2))).flatten) :=
    ((show Poly (fun p : DemandArgs => (p.1,p.2.1,demandBundle a (p.1,p.2.2))) from by fun_prop)
      |>.compose (thickWords_poly a incoming)).compose flatten_poly
  exact P1ProgEng.SolKWR.poly_take (by fun_prop) (P1ProgEng.SolKWR.poly_drop (by fun_prop) hw)

def demandCDWord (a : ℕ) (atTarget : Bool) (p : DemandArgs) : List Bool :=
  let e := p.2.2
  let srcThick := codedThick a p.1.2.1 (sourceRow e)
  bif srcThick then packedWord a (!atTarget) p else packedWord a atTarget p

theorem demandCDWord_poly (a : ℕ) (atTarget : Bool) : Poly (demandCDWord a atTarget) := by
  unfold demandCDWord
  dsimp only
  apply Code.Poly.choose <;> fun_prop

def demandWord (a : ℕ) (j : Fin 6) (q : MotifFields.Ends demandSource demandTarget j) :
    DemandArgs → List Bool :=
  match q with
  | .inl e => bif e.val then demandCDWord a false else demandABWord a false
  | .inr e => bif e.val then demandCDWord a true else demandABWord a true

theorem demandWord_poly (a : ℕ) (j : Fin 6) (q : MotifFields.Ends demandSource demandTarget j) :
    Poly (demandWord a j q) := by
  rcases q with ⟨e,he⟩ | ⟨e,he⟩ <;> cases e <;>
    first | exact demandCDWord_poly _ _ | exact demandABWord_poly _ _

end
end P1ProgEng.SolKWS

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.MultitapeWeakETH
open P1P7 P1P5.KW
open C10

noncomputable section

set_option maxHeartbeats 450000
set_option maxRecDepth 3000


variable {a g : ℕ} {k : Type} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)

variable (layout : Bool)

variable {x : X.Base} {v : (X.Base × TagW a) × BitWord g}

variable (pa : Placed (oplace (g := g) X layout) X.network.Half v) (ps : List PosCode)
variable (hps : @PositionList a (packingLaneBits a g) X ((X.Base × TagW a) × BitWord g)
  (oplace (g := g) X layout) v pa ps)
variable {db : BallRows} (hdb : PayloadRows (g := g) B X s x db)
variable (m : X.packingData.Motif)
variable (hb : (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2)

local notation "frame₀" => (2 ^ g,db,layout)
local notation "bd" => (PackingData.bundle X.packingData m)
local notation "dnum" => (X.shrinkNumber bd)
local notation "darg" => (frame₀,ps,arcCode X m.val)
local notation "pulled" => (packedPull (g := g) X layout pa)
local notation "wAB" => (PackingData.abWidth X.packingData X.shrinkNumber X.packingWidth m)
local notation "wBD" => (PackingData.bundleWidth X.packingData X.packingWidth bd)

include hdb hb in
theorem demandBundle_spec : demandBundle a (frame₀,arcCode X m.val) = bundleCode X bd := by
  unfold demandBundle
  dsimp only
  obtain ⟨hs,ht⟩ := bundleEnds X hdb.toLocalRows m hb
  rw [rolesRow_spec hdb.toLocalRows.toGraphRows layout m hs ht]

private theorem abWidth_fibre (b : OldBundle X) (u : X.packingData.MotifFiber b) :
    X.packingData.abWidth X.shrinkNumber X.packingWidth u.val =
      splitWidth (X.packingData.bundleWidth X.packingWidth b)
        (PackingData.pieceCount (oldDegree a) (colourBits a)) (X.shrinkNumber b u) := by
  obtain ⟨n, hn⟩ := u
  subst b
  rfl

include hdb hb in
theorem codedABOffset_spec :
    codedABOffset a (frame₀,arcCode X m.val) =
      ∑ t : X.packingData.MotifFiber bd, if dnum t < dnum ⟨m,rfl⟩ then
        X.packingData.abWidth X.shrinkNumber X.packingWidth t.val else 0 := by
  unfold codedABOffset
  dsimp only
  rw [demandBundle_spec B X s layout hdb m hb,
    bundleWidthNum_spec B X s hdb _ hb,
    bundleRankNum_spec X hdb.toLocalRows layout m hb]
  apply widthPrefix_equiv dnum
  intro u
  rw [splitWidthNum_spec, abWidth_fibre]

def thickAxis (a : ℕ) :
    BitWord (colourBits a) × BitWord a ≃ Fin (2 ^ colourBits a * oldDegree a) :=
  ((bitWordFinEquiv (colourBits a)).prodCongr (bitWordFinEquiv a)).trans finProdFinEquiv

abbrev thickCandidate (i : Fin (2 ^ colourBits a * oldDegree a)) : OldArc X :=
  (bd, (thickAxis a).symm i)

theorem thickCandidate_code (i : Fin (2 ^ colourBits a * oldDegree a)) :
    arcCode X (thickCandidate X m i) =
      (bundleCode X bd, (finProdFinEquiv.symm i : Fin (2 ^ colourBits a) × Fin (oldDegree a)).1.val,
        (finProdFinEquiv.symm i : Fin (2 ^ colourBits a) × Fin (oldDegree a)).2.val) := by
  let q : Fin (2 ^ colourBits a) × Fin (oldDegree a) := finProdFinEquiv.symm i
  change (bundleCode X bd,
    (bitWordFinEquiv (colourBits a) ((bitWordFinEquiv (colourBits a)).symm q.1)).val,
    (bitWordFinEquiv a ((bitWordFinEquiv a).symm q.2)).val) =
      (bundleCode X bd, q.1.val, q.2.val)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem thickCandidate_key (t : X.packingData.ThickFiber bd) :
    thickCandidate X m (⟨tkey X t.val, (X.packingData.thickFiberIndex t.val.val.1 ⟨t.val,rfl⟩).isLt⟩) = t.val.val := by
  obtain ⟨⟨e,he⟩,h⟩ := t
  change e.1 = bd at h
  have hv : X.packingData.thickFiberIndex e.1 ⟨⟨e,he⟩,rfl⟩ = thickAxis a e.2 := rfl
  change (bd,(thickAxis a).symm (X.packingData.thickFiberIndex e.1 ⟨⟨e,he⟩,rfl⟩)) = e
  rw [hv, Equiv.symm_apply_apply, ← h]

include hdb hb in
theorem thickWord_spec (incoming : Bool) (i : Fin (2 ^ colourBits a * oldDegree a)) :
    let e := thickCandidate X m i
    thickWord a incoming i (frame₀,ps,bundleCode X bd) =
      if X.packingData.thick (sourcePosition e) ∧ X.packingData.thick (sourcePosition (X.packingData.actual e)) then
        packedWord a incoming (frame₀,ps,arcCode X e) else [] := by
  let e := thickCandidate X m i
  have hs := hdb.cover _ (hb.trans (by norm_num))
  have ht := hdb.cover _ (edist_le_three hb (edist_target_le X bd.1.1 bd.2))
  change hasRow db (addr X e.1.1.1) = true at hs
  change hasRow db (addr X (X.packingData.actual e).1.1.1) = true at ht
  unfold thickWord
  dsimp only
  rw [← thickCandidate_code X m i, codedTarget_spec hdb.toLocalRows.toGraphRows e hs,
    sourceRow_spec, sourceRow_spec,
    codedThick_spec hdb.toLocalRows.toGraphRows (sourcePosition e) hs,
    codedThick_spec hdb.toLocalRows.toGraphRows (sourcePosition (X.packingData.actual e)) ht]
  by_cases h₁ : X.packingData.thick (sourcePosition e) <;>
    by_cases h₂ : X.packingData.thick (sourcePosition (X.packingData.actual e)) <;> simp [h₁,h₂,e]

local notation "roleA₀" => (PackingData.roleA X.packingData m)
local notation "roleB₀" => (PackingData.roleB X.packingData m)

theorem thickPlacement (incoming : Bool) (t : X.packingData.ThickFiber bd)
    (hp : v = packedSiteEquiv (bif incoming then roleB₀ else roleA₀)) :
    v = X.packingData.shrinkPlace layout (sourcePosition (bif incoming then X.packingData.actual t.val.val else t.val.val)) := by
  cases incoming
  · exact hp.trans (congrArg packedSiteEquiv ((congrArg Prod.fst t.property.symm).trans
      (X.packingData.place_thick_source layout t.val).symm))
  · exact hp.trans (congrArg packedSiteEquiv
      ((congrArg (fun b => (X.packingData.siteGraph.target b).1) t.property.symm).trans
      (X.packingData.place_thick_target layout t.val).symm))

def thickHalf {v₀ : (X.Base × TagW a) × BitWord g}
    (layout' : Bool) (pa' : Placed (oplace (g := g) X layout') X.network.Half v₀)
    (m' : X.packingData.Motif) (incoming : Bool)
    (t : X.packingData.ThickFiber (X.packingData.bundle m'))
    (hp : v₀ = packedSiteEquiv (bif incoming then X.packingData.roleB m' else X.packingData.roleA m')) :
    Fin (X.packingWidth t.val.val) → Bool := by
  let h := packedPull (g := g) X layout' pa'
  cases incoming
  · exact (h (sourcePosition t.val.val) (thickPlacement X layout' m' false t hp)).1 t.val.val rfl
  · exact (h (sourcePosition (X.packingData.actual t.val.val))
      (thickPlacement X layout' m' true t hp)).2 t.val.val rfl

include hps hdb hb in
theorem thickWord_at (incoming : Bool) (t : X.packingData.ThickFiber bd)
    (hp : v = packedSiteEquiv (bif incoming then roleB₀ else roleA₀)) :
    thickWord a incoming (⟨tkey X t.val, (X.packingData.thickFiberIndex t.val.val.1 ⟨t.val,rfl⟩).isLt⟩)
      (frame₀,ps,bundleCode X bd) = List.ofFn (thickHalf X layout pa m incoming t hp) := by
  rw [thickWord_spec B X s layout ps hdb m hb, thickCandidate_key X m t, ite_eq_left t.val.property]
  cases incoming
  · exact packedWord_out X layout pa ps hps t.val.val (thickPlacement X layout m false t hp)
  · have hs : hasRow db (addr X t.val.val.1.1.1) = true := by
      rw [show t.val.val.1.1.1 = bd.1.1 from congrArg (fun q => q.1.1) t.property]
      exact hdb.cover _ (hb.trans (by norm_num))
    exact packedWord_in X layout pa ps hps hdb.toLocalRows.toGraphRows t.val.val hs
      (thickPlacement X layout m true t hp)

include hps hdb hb in
theorem thickPrefix_spec (incoming : Bool) (hp : v = packedSiteEquiv (bif incoming then roleB₀ else roleA₀))
    (cut : ℕ) :
    (∑ i : Fin (2 ^ colourBits a * oldDegree a),
      if i.val < cut then (thickWord a incoming i (frame₀,ps,bundleCode X bd)).length else 0) =
      ∑ t : X.packingData.ThickFiber bd, if tkey X t.val < cut then X.packingWidth t.val.val else 0 := by
  classical
  let e (t : X.packingData.ThickFiber bd) : Fin (2 ^ colourBits a * oldDegree a) :=
    ⟨tkey X t.val, (X.packingData.thickFiberIndex t.val.val.1 ⟨t.val,rfl⟩).isLt⟩
  let w (i : Fin (2 ^ colourBits a * oldDegree a)) :=
    if i.val < cut then (thickWord a incoming i (frame₀,ps,bundleCode X bd)).length else 0
  change (∑ i, w i) = _
  rw [sum_by_injective e (fun _ _ he => tkey_injective X bd (congrArg Fin.val he)) w]
  · apply Finset.sum_congr rfl
    intro t _
    simp only [w,e,thickWord_at B X s layout pa ps hps hdb m hb incoming t hp, List.length_ofFn]
  · intro i hi
    dsimp only [w]
    rw [thickWord_spec B X s layout ps hdb m hb]
    have hn : ¬ (X.packingData.thick (sourcePosition (thickCandidate X m i)) ∧
        X.packingData.thick (sourcePosition (X.packingData.actual (thickCandidate X m i)))) := by
      intro ht
      let u : X.packingData.ThickFiber bd := ⟨⟨thickCandidate X m i,ht⟩,rfl⟩
      apply hi u
      apply Fin.ext
      change (X.packingData.thickFiberIndex bd u).val = i.val
      change ((thickAxis a) ((thickAxis a).symm i)).val = i.val
      rw [Equiv.apply_symm_apply]
    rw [ite_eq_right hn]
    simp only [List.length_nil, ite_self]

theorem orderedBits_prefix {A : Type} [Fintype A] {n : ℕ} (o : A ≃ Fin n)
    (w : A → ℕ) (x : A) (i : Fin (w x)) :
    (PackingData.orderedBits o w ⟨x,i⟩).val =
      (∑ y : A, if o y < o x then w y else 0) + i.val := by
  rw [orderedBits_val, finSigmaFinEquiv_apply, Fin.val_cast]
  apply congrArg (fun n => n + i.val)
  refine (sum_prefix (fun j => w (o.symm j)) (o x)).trans ?_
  exact Fintype.sum_equiv o.symm _ _ (fun j => by rw [Equiv.apply_symm_apply]; rfl)

set_option maxHeartbeats 900000 in
include hps hdb hb in
theorem demandABWord_spec (incoming : Bool) (hp : v = packedSiteEquiv (bif incoming then roleB₀ else roleA₀)) :
    demandABWord a incoming darg = List.ofFn (fun i : Fin wAB =>
      let z := X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth bd ⟨⟨m,rfl⟩,i⟩
      thickHalf X layout pa m incoming z.1 hp z.2) := by
  classical
  let rows (i : Fin (2 ^ colourBits a * oldDegree a)) :=
    thickWord a incoming i (frame₀,ps,bundleCode X bd)
  let q : X.packingData.MotifFiber bd := ⟨m,rfl⟩
  let baseOff := ∑ t : X.packingData.MotifFiber bd, if dnum t < dnum q then
    X.packingData.abWidth X.shrinkNumber X.packingWidth t.val else 0
  unfold demandABWord
  dsimp only
  rw [demandBundle_spec B X s layout hdb m hb, codedABOffset_spec B X s layout hdb m hb,
    codedAB_spec B X s hdb layout m hb]
  change (((List.ofFn rows).flatten).drop baseOff).take wAB = _
  have htotal : (List.ofFn rows).flatten.length = wBD := by
    rw [flatten_ofFn_lengths]
    have h := thickPrefix_spec B X s layout pa ps hps hdb m hb incoming hp
      (2 ^ colourBits a * oldDegree a)
    simpa only [rows, Fin.isLt, ite_true, tkey, PackingData.bundleWidth] using h
  apply slice_of_reads false
  · rw [htotal, ← X.packingData.sum_abWidth (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.packingWidth bd]
    change baseOff + X.packingData.abWidth X.shrinkNumber X.packingWidth q.val ≤ _
    rw [show X.packingData.abWidth X.shrinkNumber X.packingWidth q.val =
      ∑ t : X.packingData.MotifFiber bd, if t = q then X.packingData.abWidth X.shrinkNumber X.packingWidth t.val else 0 by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]]
    unfold baseOff
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : t = q
    · subst t
      simp only [lt_irrefl, ite_false, ite_true, zero_add, le_refl]
    · by_cases hl : dnum t < dnum q <;> simp [ht,hl]
  · intro i
    let z := X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth bd ⟨q,i⟩
    let key : Fin (2 ^ colourBits a * oldDegree a) :=
      ⟨tkey X z.1.val, (X.packingData.thickFiberIndex z.1.val.val.1 ⟨z.1.val,rfl⟩).isLt⟩
    have ht : rows key = List.ofFn (thickHalf X layout pa m incoming z.1 hp) :=
      thickWord_at B X s layout pa ps hps hdb m hb incoming z.1 hp
    have hx := read_flatten_point false rows key _ ht z.2
    have hf := thickPrefix_spec B X s layout pa ps hps hdb m hb incoming hp key.val
    rw [hf] at hx
    have indexEq := ((demandBitEquiv_eq_iff X.packingData (State.two_le_packingColors a)
      (Nat.two_pow_pos a) X.shrinkNumber X.shrinkOrder X.packingWidth bd q i z.1 z.2).mp
        (Sigma.eta z).symm)
    rw [orderedBits_prefix, orderedBits_prefix] at indexEq
    change baseOff + i.val =
      (∑ y : X.packingData.ThickFiber bd, if X.shrinkOrder bd y < X.shrinkOrder bd z.1 then
        X.packingWidth y.val.val else 0) + z.2.val at indexEq
    simp only [sortedThick_lt' X bd] at indexEq
    rw [indexEq]
    exact hx

theorem inputBits_wordBits {n : ℕ} (i : Fin (2 ^ n)) :
    MotifEntry.inputBits i = RAMSerialization.wordBits n i :=
  funext fun q => (CursorNetwork.addressWord_bit i q).symm

theorem inputBits_wordBits_symm {n : ℕ} (f : Fin n → Bool) :
    MotifEntry.inputBits ((RAMSerialization.wordBits n).symm f) = f :=
  (inputBits_wordBits _).trans (Equiv.apply_symm_apply _ _)

theorem ofFn_inputBits_symm {n : ℕ} (f : Fin n → Bool) :
    List.ofFn (MotifEntry.inputBits ((RAMSerialization.wordBits n).symm f)) = List.ofFn f :=
  congrArg List.ofFn (inputBits_wordBits_symm f)

theorem ofFn_inputBits_from {n : ℕ} {f : Fin n → Bool} {xs : List Bool}
    (h : xs = List.ofFn f) :
    xs = List.ofFn (MotifEntry.inputBits ((RAMSerialization.wordBits n).symm f)) :=
  h.trans (ofFn_inputBits_symm f).symm

def actualDemand {v₀ : (X.Base × TagW a) × BitWord g}
    (layout' : Bool) (pa' : Placed (oplace (g := g) X layout') X.network.Half v₀)
    (m' : X.packingData.Motif) (p : Fin 6) (hp : v₀ = X.packingData.shrinkPartySite layout' m' p) :
    HalfBits demandSource demandTarget (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m') p :=
  X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X.shrinkNumber X.shrinkOrder X.packingWidth layout' m' p
      (P1P7.SolKernloc.placedAlong (p := X.packingData.shrinkPlace layout')
        (F := (X.packingData.oldWireNetwork X.packingWidth).Half) hp
        (packedPull (g := g) X layout' pa'))

set_option maxHeartbeats 900000 in
include hps hdb hb in
theorem demandWord_spec (p : Fin 6) (hp : v = X.packingData.shrinkPartySite layout m p)
    (e : MotifFields.Ends demandSource demandTarget p) :
    demandWord a p e darg =
      match e with
      | .inl u => List.ofFn (MotifEntry.inputBits ((actualDemand X layout pa m p hp).1 u.val u.property))
      | .inr u => List.ofFn (MotifEntry.inputBits ((actualDemand X layout pa m p hp).2 u.val u.property)) := by
  obtain ⟨hs,ht⟩ := bundleEnds X hdb.toLocalRows m hb
  rcases e with ⟨e,he⟩ | ⟨e,he⟩ <;> subst p <;> cases e
  · simp only [demandWord, Bool.cond_false, actualDemand, PackingData.shrinkLocalDemandArg]
    refine @ofFn_inputBits_from (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m false) _ _ ?_
    refine (demandABWord_spec B X s layout pa ps hps hdb m hb false hp).trans ?_
    unfold PackingData.localAWord PackingData.shrinkPlacedHalf
    simp only [PackingData.shrinkDemandWidths, demandWidths, P1P7.SolKernloc.placedAlong, thickHalf]
  · change demandCDWord a false darg = _
    unfold demandCDWord
    dsimp only
    rw [sourceRow_spec, codedThick_spec hdb.toLocalRows.toGraphRows _ hs]
    simp only [actualDemand, PackingData.shrinkLocalDemandArg]
    refine @ofFn_inputBits_from (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m true) _ _ ?_
    unfold PackingData.localCWord
    by_cases hh : X.packingData.thick (sourcePosition m.val)
    · rw [decide_eq_true hh, Bool.cond_true]
      erw [dite_eq_left hh]
      have hp' := (hp.trans (X.packingData.shrinkPartySite_C layout m))
      rw [PackingData.C, ite_eq_left hh] at hp'
      simpa only [Bool.not_false, PackingData.shrinkDemandWidths, demandWidths, PackingData.shrinkPlacedHalf, P1P7.SolKernloc.placedAlong] using
        packedWord_in X layout pa ps hps hdb.toLocalRows.toGraphRows m.val hs hp'
    · rw [decide_eq_false hh, Bool.cond_false]
      erw [dite_eq_right hh]
      have hp' := (hp.trans (X.packingData.shrinkPartySite_C layout m))
      rw [PackingData.C, ite_eq_right hh] at hp'
      simpa only [PackingData.shrinkDemandWidths, demandWidths, PackingData.shrinkPlacedHalf, P1P7.SolKernloc.placedAlong] using
        packedWord_out X layout pa ps hps (db := db) m.val hp'
  · simp only [demandWord, Bool.cond_false, actualDemand, PackingData.shrinkLocalDemandArg]
    refine @ofFn_inputBits_from (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m false) _ _ ?_
    refine (demandABWord_spec B X s layout pa ps hps hdb m hb true hp).trans ?_
    unfold PackingData.localBWord PackingData.shrinkPlacedHalf
    simp only [PackingData.shrinkDemandWidths, demandWidths, P1P7.SolKernloc.placedAlong, thickHalf]
  · change demandCDWord a true darg = _
    unfold demandCDWord
    dsimp only
    rw [sourceRow_spec, codedThick_spec hdb.toLocalRows.toGraphRows _ hs]
    simp only [actualDemand, PackingData.shrinkLocalDemandArg]
    refine @ofFn_inputBits_from (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m true) _ _ ?_
    unfold PackingData.localDWord
    have hp' : v = X.packingData.shrinkPlace layout (X.packingData.D m) := hp
    by_cases hh : X.packingData.thick (sourcePosition m.val)
    · rw [decide_eq_true hh, Bool.cond_true]
      erw [dite_eq_left hh]
      rw [PackingData.D, ite_eq_left hh] at hp'
      simpa only [Bool.not_true, PackingData.shrinkDemandWidths, demandWidths, PackingData.shrinkPlacedHalf, P1P7.SolKernloc.placedAlong] using
        packedWord_out X layout pa ps hps (db := db) m.val hp'
    · rw [decide_eq_false hh, Bool.cond_false]
      erw [dite_eq_right hh]
      rw [PackingData.D, ite_eq_right hh] at hp'
      simpa only [PackingData.shrinkDemandWidths, demandWidths, PackingData.shrinkPlacedHalf, P1P7.SolKernloc.placedAlong] using
        packedWord_in X layout pa ps hps hdb.toLocalRows.toGraphRows m.val hs hp'

end
end P1ProgEng.SolKWS
