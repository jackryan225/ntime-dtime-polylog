import P1ProgEng.KWShrinkInternal
import P1ProgEng.KWShrinkSurviving

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.MultitapeWeakETH
open P1P7 P1P5.KW
open C10
open scoped P1ChkFinal.AstraC10
open P1ProgEng.SolKWR (HalfCode)
open P1P7.SolKernloc (outputState atSite placed_at)

noncomputable section

variable {k : Type} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- A decoded query for one motif, including the shared internal assignment. -/
abbrev EntryArgs := ResidentFrame × List PosCode × (HalfCode × Bits.Word) × ArcRow

def supplyEndWord (a b : ℕ) (incoming : Bool) (e : Bool × Fin 4)
    (p : EntryArgs) : Bits.Word :=
  bif decide (p.1.1.2.2 = e.1) then
    survivingWord a b incoming e.2 (p.1,p.2.2.1.1,p.2.2.2)
  else absorbedWord B a e.2 (p.1,p.2.2.1.2,p.2.2.2)

theorem supplyEndWord_poly (a b : ℕ) (incoming : Bool) (e : Bool × Fin 4) :
    Poly (supplyEndWord B a b incoming e) := by
  apply Code.Poly.choose ((show Poly (fun p : EntryArgs => (p.1.1.2.2,e.1)) from by fun_prop).compose
    (Easy.finite (fun q : Bool × Bool => decide (q.1 = q.2))).poly)
  · exact (show Poly (fun p : EntryArgs => (p.1,p.2.2.1.1,p.2.2.2)) from by fun_prop).compose
      (survivingWord_poly a b incoming e.2)
  · exact (show Poly (fun p : EntryArgs => (p.1,p.2.2.1.2,p.2.2.2)) from by fun_prop).compose
      (absorbedWord_poly B a e.2)

def supplyWord (a b : ℕ) (j : Fin 6) (p : MotifFields.Port supply j) : EntryArgs → Bits.Word :=
  match p with
  | .inl e => supplyEndWord B a b false e.val
  | .inr e => supplyEndWord B a b true e.val

theorem supplyWord_poly (a b : ℕ) (j : Fin 6) (p : MotifFields.Port supply j) :
    Poly (supplyWord B a b j p) := by
  cases p <;> exact supplyEndWord_poly B _ _ _ _

section Spec

set_option maxHeartbeats 500000
set_option maxRecDepth 2500

variable {a b g : ℕ} {δ : ℝ}
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
variable (layout : Bool)
local notation "Y" => (outputState (g := g) B ready X s layout)
local notation "hpos" => ready.count_pos

def actualSupply (m : X.packingData.Motif) (p : Fin 6) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X s) layout) v)
    (z : (Y).network.Half v) :=
  X.packingData.shrinkLocalSupplyArg layout (SD a b) (selW B X s)
    (X.shrinkStateIndex ready layout) hpos m p (hv ▸ h) (hv ▸ z)

private theorem supplyOut_active (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p)
    (hr : v = packedSiteEquiv (X.packingData.survivingRole layout (sourceRole layout t) m))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v)
    (z : (outputState B ready X c layout).network.Half v) (hp : p = supply.src (layout,t)) :
    (actualSupply B ready X c layout m p hv h z).1 (layout,t) hp =
      (RAMSerialization.wordBits _).symm
        (X.packingData.localSurvivingSource layout (SD a b) (fun n i => selW B X c n (layout,i)) (X.shrinkStateIndex ready layout) ready.count_pos m t (atSite (N := (outputState B ready X c layout).network) hr z)) := by
  subst hv
  cases layout <;> rfl

private theorem supplyIn_active (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p)
    (hr : v = packedSiteEquiv (X.packingData.survivingRole layout (targetRole layout t) m))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v)
    (z : (outputState B ready X c layout).network.Half v) (hp : p = supply.dst (layout,t)) :
    (actualSupply B ready X c layout m p hv h z).2 (layout,t) hp =
      (RAMSerialization.wordBits _).symm
        (X.packingData.localSurvivingTarget layout (SD a b) (fun n i => selW B X c n (layout,i)) (X.shrinkStateIndex ready layout) ready.count_pos m t (atSite (N := (outputState B ready X c layout).network) hr z)) := by
  subst hv
  cases layout <;> rfl

private theorem supplyOut_internal (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p) (hi : v = (X.packingData.shrinkInternalOwner layout) (m,t))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v) (z : (outputState B ready X c layout).network.Half v)
    (hp : p = supply.src (!layout,t)) :
    (actualSupply B ready X c layout m p hv h z).1 (!layout,t) hp = h (m,t) hi := by
  cases layout <;> exact placed_at hv h (m,t) _

private theorem supplyIn_internal (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p) (hi : v = (X.packingData.shrinkInternalOwner layout) (m,t))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v) (z : (outputState B ready X c layout).network.Half v)
    (hp : p = supply.dst (!layout,t)) :
    (actualSupply B ready X c layout m p hv h z).2 (!layout,t) hp = h (m,t) hi := by
  cases layout <;> exact placed_at hv h (m,t) _

variable {x : X.Base} {db : BallRows}
variable (j : TagW a) (l : BitWord g)
local notation "outSite" => ((x,j),l)
local notation "f" => ((2 ^ g,db,layout),siteCode X (x,j,l))
local notation "H" => (Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X s) layout) outSite)

def outputHalfCode (v₀ : (Y).network.Site) (z : (Y).network.Half v₀) : HalfCode :=
  @halfCode b g (Y) v₀ z

def supplyValueBits {w : Bool × Fin 4 → ℕ} {p : Fin 6}
    (u : ((e : Bool × Fin 4) → p = supply.src e → Fin (2 ^ w e)) ×
      ((e : Bool × Fin 4) → p = supply.dst e → Fin (2 ^ w e)))
    (q : MotifFields.Port supply p) : Bits.Word :=
  match q with
  | .inl e => List.ofFn (MotifEntry.inputBits (u.1 e.val e.property))
  | .inr e => List.ofFn (MotifEntry.inputBits (u.2 e.val e.property))

def supplyArgs (chart : PayloadRows B X s x db) (m' : X.packingData.Motif)
    (h' : H) (ps' : List PosCode) (zCode : HalfCode) : EntryArgs := by
  refine ⟨?_, ps', ⟨zCode, ?_⟩, ?_⟩
  · exact ((2 ^ g,db,layout),siteCode X (x,j,l))
  · exact @assignmentCode k _ factor B a g X s x db chart layout j l h'
  · exact arcCode X m'.val

set_option maxHeartbeats 900000 in
def supplyWordCorrect (chart : PayloadRows B X s x db) (m' : X.packingData.Motif) (p' : Fin 6)
    (he : outSite = X.packingData.shrinkPartySite layout m' p') (h' : H) (ps' : List PosCode)
    {v₀ : (Y).network.Site} (z : (Y).network.Half v₀) (hz : v₀ = outSite)
    (q : MotifFields.Port supply p') (zCode : HalfCode) : Prop := by
  let args := supplyArgs B X s layout j l chart m' h' ps' zCode
  let z' : (Y).network.Half outSite := @atSite (Y).network v₀ outSite hz z
  let u : ((e : Bool × Fin 4) → p' = supply.src e → Fin (2 ^ selW B X s m' e)) ×
      ((e : Bool × Fin 4) → p' = supply.dst e → Fin (2 ^ selW B X s m' e)) :=
    @actualSupply k _ factor B a b g δ ready X s layout m' p' outSite he h' z'
  exact supplyWord B a b p' q args = supplyValueBits u q

set_option maxHeartbeats 900000 in
theorem supplyWord_spec (hdb : PayloadRows B X s x db) (m : X.packingData.Motif) (p : Fin 6)
    (hv : outSite = X.packingData.shrinkPartySite layout m p) (h : H) (ps : List PosCode)
    {v₀ : (Y).network.Site} (z : (Y).network.Half v₀) (hz : v₀ = outSite)
    (q : MotifFields.Port supply p) :
    supplyWordCorrect B ready X s layout j l hdb m p hv h ps z hz q
      (outputHalfCode B ready X s layout v₀ z) := by
  unfold supplyWordCorrect supplyArgs supplyValueBits
  subst v₀
  let entryArgs := supplyArgs B X s layout j l hdb m h ps (outputHalfCode B ready X s layout outSite z)
  let actual := @actualSupply k _ factor B a b g δ ready X s layout m p outSite hv h z
  have bits (n : ℕ) (i : Fin (2 ^ n)) : MotifEntry.inputBits i = RAMSerialization.wordBits n i :=
    funext fun k => (CursorNetwork.addressWord_bit i k).symm
  rcases q with ⟨⟨bl,t⟩,he⟩ | ⟨⟨bl,t⟩,he⟩
  · change supplyEndWord B a b false (bl,t) entryArgs = List.ofFn (MotifEntry.inputBits ((actual).1 (bl,t) he))
    by_cases hb : bl = layout
    · subst bl
      have hrs : partyRole layout p = sourceRole layout t :=
        (congrArg (partyRole layout) he).trans (role_src_survives layout t)
      have hs := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole layout r m)) hrs)
      simp only [supplyEndWord, entryArgs, supplyArgs, decide_true, Bool.cond_true]
      rw [supplyOut_active B ready X s layout m p t hv hs h z he, bits, Equiv.apply_symm_apply]
      exact survivingSource_spec B ready X s hdb.toLocalRows layout j l m t z rfl hs
    · obtain rfl := Bool.eq_not_of_ne hb
      have hr : partyRole layout p = internalRole layout t :=
        (congrArg (partyRole layout) he).trans (role_src_absorbed layout t)
      have hi := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole layout r m)) hr)
      have heq : ¬ layout = !layout := by cases layout <;> decide
      simp only [supplyEndWord, entryArgs, supplyArgs, heq, decide_false, Bool.cond_false]
      rw [supplyOut_internal B ready X s layout m p t hv hi h z he, bits]
      exact absorbedWord_spec B X s hdb layout j l h m t hi
  · change supplyEndWord B a b true (bl,t) entryArgs = List.ofFn (MotifEntry.inputBits ((actual).2 (bl,t) he))
    by_cases hb : bl = layout
    · subst bl
      have hrs : partyRole layout p = targetRole layout t :=
        (congrArg (partyRole layout) he).trans (role_dst_survives layout t)
      have hs := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole layout r m)) hrs)
      simp only [supplyEndWord, entryArgs, supplyArgs, decide_true, Bool.cond_true]
      rw [supplyIn_active B ready X s layout m p t hv hs h z he, bits, Equiv.apply_symm_apply]
      exact survivingTarget_spec B ready X s hdb.toLocalRows layout j l m t z rfl hs
    · obtain rfl := Bool.eq_not_of_ne hb
      have hr : partyRole layout p = internalRole layout t :=
        (congrArg (partyRole layout) he).trans (role_dst_absorbed layout t)
      have hi := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole layout r m)) hr)
      have heq : ¬ layout = !layout := by cases layout <;> decide
      simp only [supplyEndWord, entryArgs, supplyArgs, heq, decide_false, Bool.cond_false]
      rw [supplyIn_internal B ready X s layout m p t hv hi h z he, bits]
      exact absorbedWord_spec B X s hdb layout j l h m t hi

end Spec

end
end P1ProgEng.SolKWS

#print axioms P1ProgEng.SolKWS.supplyWord_spec
#print axioms P1ProgEng.SolKWS.supplyWordCorrect
#print axioms P1ProgEng.SolKWS.outputHalfCode
#print axioms P1ProgEng.SolKWS.supplyArgs
#print axioms P1ProgEng.SolKWS.actualSupply
