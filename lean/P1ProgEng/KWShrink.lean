import P1ProgEng.KWShrinkDemand
import P1ProgEng.KWShrinkEntrySupply

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifSelector
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.PairSimulation.LocalHistory
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH
open P1P7 P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10

namespace P1ProgEng.SolKWS

open C10
open P1ProgEng.SolKWR (HalfCode poly_tallyCap poly_bank bank_congr)

noncomputable section

variable {k : Type} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

def anchorWord (a b : ℕ) (p : Fin 6) (u : EntryArgs) : Bits.Word :=
  false :: supplyWord B a b p (MotifFields.anchorPort supply p) u

theorem anchorWord_poly (a b : ℕ) (p : Fin 6) : Poly (anchorWord B a b p) :=
  ((Code.Poly.const false).pair (supplyWord_poly B a b p _)).compose Code.Poly.cons

def widthTally (a b C : ℕ) (p : Fin 6) (d : Bool) (u : EntryArgs) : Tally :=
  tally (min ((bif d then codedCD a else codedAB a) (u.1.1,u.2.2.2))
    (C * (anchorWord B a b p u).length))

theorem widthTally_poly (a b C : ℕ) (p : Fin 6) (d : Bool) :
    Poly (widthTally B a b C p d) := by
  cases d <;> unfold widthTally <;> simp only [Bool.cond_false,Bool.cond_true] <;>
    exact poly_tallyCap C (by fun_prop) (anchorWord_poly B a b p)

def payloadTally (a b C : ℕ) (p : Fin 6) (e : Bool × Fin 4) (u : EntryArgs) : Tally :=
  tally (min (codedPayload a e (u.1.1,u.2.2.2)) (C * (anchorWord B a b p u).length))

theorem payloadTally_poly (a b C : ℕ) (p : Fin 6) (e : Bool × Fin 4) :
    Poly (payloadTally B a b C p e) :=
  poly_tallyCap C (by fun_prop) (anchorWord_poly B a b p)

def fixedCode (a b C : ℕ) (p : Fin 6) (u : EntryArgs) : MotifFields.FixedInput (Fin 6) :=
  (((MotifFields.bank (fun d => widthTally B a b C p d u), ⟨p⟩),
    MotifFields.bank (fun e => demandWord a p e (u.1.1,u.2.1,u.2.2.2))),
    MotifFields.bank (fun q => (supplyWord B a b p q u, payloadTally B a b C p (MotifFields.edge supply p q) u)),
    MotifFields.bank (fun e => payloadTally B a b C p e u))

theorem fixedCode_poly (a b C : ℕ) (p : Fin 6) : Poly (fixedCode B a b C p) := by
  have hproj : Poly (fun u : EntryArgs => (u.1.1,u.2.1,u.2.2.2)) := by fun_prop
  exact (((poly_bank _ (widthTally_poly B a b C p)).pair (Code.Poly.const (StackInterpreter.Label.mk p))).pair
    (poly_bank _ (fun q => hproj.compose (demandWord_poly a p q)))).pair
    ((poly_bank _ (fun q => (supplyWord_poly B a b p q).pair (payloadTally_poly B a b C p _))).pair
      (poly_bank _ (payloadTally_poly B a b C p)))

abbrev EntryShared := ResidentFrame × List PosCode × HalfCode × Bits.Word

def writeResident (a b C : ℕ) (u : EntryShared × (ℕ × ArcRow)) : MotifFields.FixedInput (Fin 6) :=
  read ((([],⟨0⟩),[]),[],[]) (List.ofFn fun p : Fin 6 =>
    fixedCode B a b C p (u.1.1,u.1.2.1,(u.1.2.2.1,u.1.2.2.2),u.2.2)) u.2.1

theorem writeResident_poly (a b C : ℕ) : Poly (writeResident B a b C) := by
  have htab : Poly (fun u : EntryShared × (ℕ × ArcRow) =>
      List.ofFn (fun p : Fin 6 =>
        fixedCode B a b C p (u.1.1,u.1.2.1,(u.1.2.2.1,u.1.2.2.2),u.2.2))) := by
    apply fixedList_poly
    intro p
    exact (show Poly (fun u : EntryShared × (ℕ × ArcRow) =>
      (u.1.1,u.1.2.1,(u.1.2.2.1,u.1.2.2.2),u.2.2) : _ → EntryArgs) from by fun_prop).compose
        (fixedCode_poly B a b C p)
  have hi : Poly (fun u : EntryShared × (ℕ × ArcRow) => u.2.1) := by fun_prop
  exact (htab.pair hi).compose (read_poly
    (((([],⟨0⟩),[]),[],[]) : MotifFields.FixedInput (Fin 6)))

def writeTerm (a b C : ℕ) (u : EntryShared) : List (MotifFields.FixedInput (Fin 6)) :=
  (residentRows a u.1).map fun r => writeResident B a b C (u,r)

theorem writeTerm_poly (a b C : ℕ) : Poly (writeTerm B a b C) :=
  (Code.Poly.identity.pair (Easy.fst.poly.compose (residentRows_poly a))).compose
    (mapWith_poly _ (writeResident_poly B a b C))

def planWords (a : ℕ) (u : ShrinkKIn) : List Bits.Word :=
  internalWords ((ownerWidths B a (residentFrame a u)).sum,u.2)

theorem planWords_poly (a : ℕ) : Poly (planWords B a) := by
  have hw0 : Poly (fun f : ResidentFrame => (ownerWidths B a f).sum) :=
    Code.Poly.compose (ownerWidths_poly B a) P1ProgEng.SolKWS.sum_poly
  have hw := Code.Poly.compose (residentFrame_poly a) hw0
  exact (hw.pair (Easy.snd.poly : Poly (Prod.snd : ShrinkKIn → Tally))).compose internalWords_poly

def planAt (a b C : ℕ) (p : ShrinkKIn × Bits.Word) : List (MotifFields.FixedInput (Fin 6)) :=
  writeTerm B a b C (residentFrame a p.1,p.1.1.2.1,p.1.1.2.2,p.2)

theorem planAt_poly (a b C : ℕ) : Poly (planAt B a b C) := by
  have hframe := (Easy.fst.poly : Poly (Prod.fst : ShrinkKIn × Bits.Word → ShrinkKIn)).compose
    (residentFrame_poly a)
  have hargs : Easy (fun p : ShrinkKIn × Bits.Word => p.1.1.2) :=
    (Easy.fst.compose Easy.fst).compose Easy.snd
  have hshared : Poly (fun p : ShrinkKIn × Bits.Word =>
      (p.1.1.2.1,p.1.1.2.2,p.2)) :=
    ((hargs.compose Easy.fst).pair ((hargs.compose Easy.snd).pair Easy.snd)).poly
  exact (hframe.pair hshared).compose (writeTerm_poly B a b C)

def mapPlan (a b C : ℕ) (p : ShrinkKIn × List Bits.Word) : List (List (MotifFields.FixedInput (Fin 6))) :=
  p.2.map fun h => planAt B a b C (p.1,h)

theorem mapPlan_poly (a b C : ℕ) : Poly (mapPlan B a b C) :=
  mapWith_poly (planAt B a b C) (planAt_poly B a b C)

def writePlan (a b C : ℕ) (u : ShrinkKIn) : List (List (MotifFields.FixedInput (Fin 6))) :=
  mapPlan B a b C (u,planWords B a u)

theorem writePlan_poly (a b C : ℕ) : Poly (writePlan B a b C) := by
  have hp : Poly (fun u : ShrinkKIn => (u,planWords B a u)) :=
    Code.Poly.pair (Code.Poly.identity : Poly (id : ShrinkKIn → ShrinkKIn)) (planWords_poly B a)
  have h := Code.Poly.compose hp (mapPlan_poly B a b C)
  exact h

def EntryWidthCap (C : ℕ) : Prop :=
  ∀ (w : Bool → ℕ) (u : Bool × Fin 4 → ℕ), u ∈ outerIndices B w →
    ∀ e : Bool × Fin 4,
      (∀ d, w d ≤ C * (supplyWidths B w u e + 1)) ∧
      (∀ p, u p ≤ C * (supplyWidths B w u e + 1))

abbrev ResidentIndex {a g : ℕ} (X : State a (packingLaneBits a g))
    (layout : Bool) (v : (X.Base × TagW a) × BitWord g) :=
  {p : X.packingData.Motif × Fin 6 // X.packingData.shrinkPartySite layout p.1 p.2 = v}

section Spec

set_option maxHeartbeats 650000
set_option maxRecDepth 3000

variable {a b g : ℕ} {δ : ℝ}
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
variable (layout : Bool) (x : X.Base) (j : TagW a) (l : BitWord g)
local notation "outSite" => ((x,j),l)
local notation "Y" => (P1P7.SolKernloc.outputState (g := g) B ready X s layout)

local notation "Own" => (Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X s) layout) outSite)
local notation "BRows" => (codedBall B X s x)
local notation "hdb" => (codedBall_payload B X s x)
local notation "frame" => ((2 ^ g,BRows,layout),siteCode X (x,j,l))
local notation "Residents" => (ResidentIndex X layout outSite)

theorem residentRows_spec (row : ℕ × ArcRow) :
    row ∈ residentRows a frame ↔ ∃ r : Residents, encodeIndex X r.val = row := by
  rw [residentRows_eq, roleRows_spec X (hdb).toLocalRows]
  constructor
  · rintro ⟨⟨u,hu⟩,rfl⟩
    exact ⟨⟨u,congrArg packedSiteEquiv hu⟩,rfl⟩
  · rintro ⟨⟨u,hu⟩,rfl⟩
    exact ⟨⟨u,packedSiteEquiv.injective hu⟩,rfl⟩

def residentOrder : Fin (residentRows a frame).length ≃ Residents :=
  rowEquiv (by rw [residentRows_eq]; exact roleRows_nodup _ _ _)
    ((encodeIndex_injective X).comp Subtype.val_injective) (residentRows_spec B X s layout x j l)

theorem residentOrder_encode (i : Fin (residentRows a frame).length) :
    encodeIndex X (residentOrder B X s layout x j l i).val = (residentRows a frame)[i.val] :=
  rowEquiv_encode _ _ (residentRows_spec B X s layout x j l) i

def actualEntry {v : (X.Base × TagW a) × BitWord g}
    (placed : Placed (oplace (g := g) X layout) X.network.Half v)
    (z : (Y).network.Half v)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X s) layout) v)
    (r : ResidentIndex X layout v) : EntryInput B := by
  let m := r.val.1
  let p := r.val.2
  refine ⟨X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m, (s m).val, p, ?_, ?_⟩
  · exact actualDemand X layout placed m p r.property.symm
  · exact @actualSupply k _ factor B a b g δ ready X s layout m p v r.property.symm h z

local notation "codeOf" => (assignmentCode B X s hdb layout j l)

theorem fixedCode_correct (pa : Placed (oplace (g := g) X layout) X.network.Half outSite)
    (ps : List PosCode) (hps : PositionList X (oplace (g := g) X layout) outSite pa ps)
    (z : (Y).network.Half outSite)
    (C : ℕ) (hC : EntryWidthCap B C) (h : Own) (r : Residents) :
    fixedCode B a b C r.val.2 (supplyArgs B X s layout j l hdb r.val.1 h ps
      (@outputHalfCode k _ factor B a b g δ ready X s layout outSite z)) =
      MotifFields.fixedInput B (@actualEntry k _ factor B a b g δ ready X s layout outSite pa z h r) := by
  let m := r.val.1
  let p := r.val.2
  let W := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
  let E := @actualEntry k _ factor B a b g δ ready X s layout outSite pa z h r
  let args := supplyArgs B X s layout j l hdb m h ps
    (@outputHalfCode k _ factor B a b g δ ready X s layout outSite z)
  let port := MotifFields.anchorPort supply p
  let e := MotifFields.edge supply p port
  change fixedCode B a b C p args = MotifFields.fixedInput B E
  have hb := bundle_near_of_role (x := x) X layout m (partyRole layout p) (congrArg (fun q => q.1.1) r.property)
  have sWord (q : MotifFields.Port supply p) := supplyWord_spec B ready X s layout j l hdb m p r.property.symm h ps z rfl q
  unfold supplyWordCorrect supplyValueBits at sWord
  have hlength (q : MotifFields.Port supply p) :
      (supplyWord B a b p q args).length = supplyWidths B W (s m).val (MotifFields.edge supply p q) := by
    rw [sWord q]
    cases q <;> exact List.length_ofFn
  have hAnchor : (anchorWord B a b p args).length = supplyWidths B W (s m).val e + 1 := by
    unfold anchorWord
    rw [List.length_cons, hlength]
  have hbounds := hC W (s m).val (s m).property e
  have wTally (d : Bool) : widthTally B a b C p d args = tally (E.demand d) := by
    unfold widthTally
    rw [hAnchor]
    cases d
    · change tally (min (codedAB a ((2 ^ g,BRows,layout),arcCode X m.val)) _) = tally (W false)
      rw [codedAB_spec B X s hdb layout m hb]
      change tally (min (W false) _) = tally (W false)
      rw [min_eq_left (hbounds.1 false)]
    · change tally (min (codedCD a ((2 ^ g,BRows,layout),arcCode X m.val)) _) = tally (W true)
      rw [codedCD_spec B X s hdb layout m hb]
      change tally (min (W true) _) = tally (W true)
      rw [min_eq_left (hbounds.1 true)]
  have pTally (e : Bool × Fin 4) : payloadTally B a b C p e args = tally (E.payload e) := by
    unfold payloadTally
    rw [hAnchor]
    change tally (min (codedPayload a e ((2 ^ g,BRows,layout),arcCode X m.val)) _) = tally ((s m).val e)
    rw [codedPayload_spec B X s hdb layout m hb, min_eq_left (hbounds.2 e)]
  have dWord := demandWord_spec B X s layout pa ps hps hdb m hb p r.property.symm
  unfold fixedCode MotifFields.fixedInput MotifFields.mapInput MotifFields.supplyInput
  dsimp only [E, actualEntry]
  refine Prod.ext (Prod.ext (Prod.ext ?_ rfl) ?_) (Prod.ext ?_ ?_)
  all_goals dsimp only
  · exact bank_congr wTally
  · apply bank_congr
    intro q
    cases q <;> exact dWord _
  · apply bank_congr
    intro q
    refine Prod.ext ?_ (pTally _)
    cases q with
    | inl q => exact sWord (.inl q)
    | inr q => exact sWord (.inr q)
  · exact bank_congr pTally

theorem writeTerm_correct (pa : Placed (oplace (g := g) X layout) X.network.Half outSite)
    (ps : List PosCode) (hps : PositionList X (oplace (g := g) X layout) outSite pa ps)
    (z : (Y).network.Half outSite)
    (C : ℕ) (hC : EntryWidthCap B C) (h : Own) :
    writeTerm B a b C (frame,ps,@outputHalfCode k _ factor B a b g δ ready X s layout outSite z,codeOf h) =
      (List.ofFn fun r =>
        @actualEntry k _ factor B a b g δ ready X s layout outSite pa z h
          (residentOrder B X s layout x j l r)).map
        (MotifFields.fixedInput B) := by
  let zCode := @outputHalfCode k _ factor B a b g δ ready X s layout outSite z
  unfold writeTerm
  have tab := congrArg (List.map (fun r => writeResident B a b C ((frame,ps,zCode,codeOf h),r)))
    (List.ofFn_getElem (xs := residentRows a frame)).symm
  rw [List.map_ofFn] at tab
  rw [tab, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [← residentOrder_encode B X s layout x j l i]
  let r := residentOrder B X s layout x j l i
  unfold writeResident encodeIndex
  dsimp only
  rw [read_ofFn_num _ _ r.val.2]
  exact fixedCode_correct B ready X s layout x j l pa ps hps z C hC h r

end Spec

private theorem sumAlong {A A' R : Type} [AddCommMonoid R] {i : Fintype A} {i' : Fintype A'}
    (e : A ≃ A') {f : A → R} {g : A' → R} (h : ∀ a, f a = g (e a)) :
    @Finset.sum A R _ (@Finset.univ A i) f = @Finset.sum A' R _ (@Finset.univ A' i') g := by
  letI := i
  letI := i'
  exact Fintype.sum_equiv e f g h

private theorem prodAlong {A A' R : Type} [CommMonoid R] {i : Fintype A} {i' : Fintype A'}
    (e : A ≃ A') {f : A → R} {g : A' → R} (h : ∀ a, f a = g (e a)) :
    @Finset.prod A R _ (@Finset.univ A i) f = @Finset.prod A' R _ (@Finset.univ A' i') g := by
  letI := i
  letI := i'
  exact Fintype.prod_equiv e f g h

set_option maxHeartbeats 1000000 in
theorem writePlan_correct {a b : ℕ} {δ : ℝ}
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (C : ℕ) (hC : EntryWidthCap B C) : ShrinkKernelOK B ready (writePlan B a b C) := by
  intro R _ κ hκ g X s x j l pa z ps pad hps hpad
  let layout := layoutBit B X s
  let v : (X.Base × TagW a) × BitWord g := ((x,j),l)
  let chart := codedBall_payload B X s x
  have hplaced : PositionList X (oplace (g := g) X layout) v pa ps := hps
  let hcode : HalfCode := halfCode (X.shrinkNext B ready s) v z
  let e := internalOrder B X s chart layout j l
  let r := residentOrder B X s layout x j l
  let term (h : Placed (X.packingData.shrinkInternalOwner layout)
      (internalLabel (selW B X s) layout) v) : List (EntryInput B) :=
    List.ofFn fun i => @actualEntry k _ factor B a b g δ ready X s layout v pa z h (r i)
  let I := List.ofFn fun i => term (e.symm i)
  have hclock := hpad
  rw [ownerWords_card B X s chart layout j l] at hclock
  refine ⟨I, ?_, ?_⟩
  · unfold writePlan mapPlan planWords planAt
    dsimp only
    rw [residentFrame_true B ready X s x j l ps z pad]
    let f : ResidentFrame := ((2 ^ g,codedBall B X s x,layout),siteCode X (x,j,l))
    change (internalWords ((ownerWidths B a f).sum,pad)).map
      (fun h => writeTerm B a b C (f,ps,hcode,h)) = _
    rw [internalWords_eq _ _ hclock, ownerWidths_spec B X s chart layout j l, List.sum_ofFn]
    change (List.ofFn fun i => Bits.short _ i.val).map _ = _
    simp only [I, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    let w := ∑ q, internalWidth B X s layout (ownerOrder B X s chart layout j l q).val
    have hword : Bits.short w i.val = assignmentCode B X s chart layout j l (e.symm i) := by
      rw [short_of_wordBits]
      change List.ofFn (RAMSerialization.wordBits _ i) =
        List.ofFn (RAMSerialization.wordBits _ (e (e.symm i)))
      rw [Equiv.apply_symm_apply]
    change writeTerm B a b C (f,ps,hcode,Bits.short w i.val) =
      (term (e.symm i)).map (MotifFields.fixedInput B)
    rw [hword]
    exact writeTerm_correct B ready X s layout x j l pa ps hplaced z C hC (e.symm i)
  · refine (Eq.trans ?_ (shrink_kernel_resident' B ready κ hκ X s v pa z).symm)
    unfold entriesValue
    simp only [I, term, List.map_ofFn, List.sum_ofFn, List.prod_ofFn, Function.comp_apply]
    refine sumAlong e.symm (fun i => ?_)
    refine prodAlong r (fun q => ?_)
    dsimp only [actualEntry, actualDemand, actualSupply, P1P7.SolKernloc.atSite]
    have hpull : @packedPull a g X layout v pa = pullPlaced B ready κ hκ X s v pa := by
      unfold packedPull pullPlaced
      rfl
    rw [hpull]
    have hd := P1P7.SolKernloc.placed_cast_eq
      (p := X.packingData.shrinkPlace (layoutBit B X s))
      (F := (X.packingData.oldWireNetwork X.packingWidth).Half)
      (r q).property.symm (pullPlaced B ready κ hκ X s v pa)
    rw [← hd] <;> rfl

end
end P1ProgEng.SolKWS

theorem P1ProgEng.shrinkKernelProgram {a b : ℕ} {δ factor : ℝ} {k : Type} [Field k]
    (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) :
    P1P5.KW.ShrinkKernelProgram B ready := by
  obtain ⟨C, hC⟩ := P1ProgEng.SolKWS.shrink_entry_width_bound B
  exact ⟨P1ProgEng.SolKWS.writePlan B a b C, P1ProgEng.SolKWS.writePlan_poly B a b C,
    P1ProgEng.SolKWS.writePlan_correct B ready C hC⟩

#print axioms P1ProgEng.shrinkKernelProgram
#print axioms P1ProgEng.SolKWS.supplyWord_spec
#print axioms P1ProgEng.SolKWS.demandWord_spec
