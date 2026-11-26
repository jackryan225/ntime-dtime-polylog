import P1P7.SolKernlocPlaced

namespace P1P7.SolKernloc

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkPayload
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel

attribute [local instance] instDecEqBaseT

theorem concat_heq {n n' q : ℕ} (hw : n' = n) (hq : 0 < q)
    (f : ∀ i : Fin q, Fin (splitWidth n q i) → Bool)
    (f' : ∀ i : Fin q, Fin (splitWidth n' q i) → Bool)
    (h : ∀ i, HEq (f' i) (f i)) :
    HEq ((sliceWords n' q hq).symm f') ((sliceWords n q hq).symm f) := by
  subst n'
  exact heq_of_eq (congrArg (sliceWords n q hq).symm (funext fun i => eq_of_heq (h i)))

theorem encode_val {n n' : ℕ} (hw : n' = n) {f' : Fin n' → Bool} {f : Fin n → Bool} (hf : HEq f' f) :
    ((RAMSerialization.wordBits n').symm f' : ℕ) = ((RAMSerialization.wordBits n).symm f : ℕ) := by
  subst n'
  rw [eq_of_heq hf]

theorem finVal_eq {n n' : ℕ} (h : n' = n) {i' : Fin n'} {i : Fin n} (hi : HEq i' i) :
    (i' : ℕ) = i := by
  subst h
  exact congrArg Fin.val (eq_of_heq hi)

def atSite {N : Network} {v u : N.Site} (e : v = u) (z : N.Half v) : N.Half u :=
  ⟨fun a h => z.1 a (e.trans h), fun a h => z.2 a (e.trans h)⟩

section Supply

variable {a b g : ℕ} {δ factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {X X' : State a (packingLaneBits a g)} {x : X.Base}
variable (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
variable (L : Bool) (j : TagW a) (l : BitWord g)

local notation "Y₀" => outputState B ready X s L
local notation "Y₁" => outputState B ready X' s' L
local notation "v₀" => ((x, j), l)
local notation "v₁" => ((pb X X' x, j), l)
local notation "w₀" => selW B X s
local notation "w₁" => selW B X' s'
local notation "I₀" => X.shrinkStateIndex ready L
local notation "I₁" => X'.shrinkStateIndex ready L
local notation "hpos" => ready.count_pos

variable {B ready s s' L j l}
variable {z : Network.Half ((outputState B ready X s L).network) ((x, j), l)}
variable {z' : Network.Half ((outputState B ready X' s' L).network) ((pb X X' x, j), l)}
variable (hg : Good3 X X' x)
variable (m : X.packingData.Motif) (hE : EndsGood X X' m.val)

local notation "m₁" => tM m hE

include hg in
theorem localSource (hc : (∀ k : Fin (2 ^ b),
      HEq (z'.1 (outEdge Y₁ v₁ k) (outEdge_src Y₁ v₁ k))
        (z.1 (outEdge Y₀ v₀ k) (outEdge_src Y₀ v₀ k)))) (t : Fin 4)
    (h : v₀ = packedSiteEquiv (X.packingData.survivingRole L (sourceRole L t) m))
    (h' : v₁ = packedSiteEquiv (X'.packingData.survivingRole L (sourceRole L t) m₁))
    (hw : w₁ m₁ (L,t) = w₀ m (L,t)) :
    HEq (X'.packingData.localSurvivingSource L (SD a b) (fun n i => w₁ n (L,i)) I₁ hpos m₁ t (atSite (N := (Y₁).network) h' z'))
      (X.packingData.localSurvivingSource L (SD a b) (fun n i => w₀ n (L,i)) I₀ hpos m t (atSite (N := (Y₀).network) h z)) := by
  unfold PackingData.localSurvivingSource
  refine concat_heq hw (ready.count_pos t) _ _ ?_
  intro i
  let e := actualArc (ready := ready) X L m t i
  let e' := actualArc (ready := ready) X' L m₁ t i
  have he : v₀ = (Y₀).network.src e :=
    h.trans (X.packingData.shrinkArc_endpoints L (SD a b) I₀ ⟨t,m,i⟩).1.symm
  have he' : v₁ = (Y₁).network.src e' :=
    h'.trans (X'.packingData.shrinkArc_endpoints L (SD a b) I₁ ⟨t,m₁,i⟩).1.symm
  have hk : e'.2 = e.2 :=
    actualArc_out_slot (ready := ready) hg L j m hE t i (congrArg Prod.fst h).symm
  exact (cast_heq _ _).trans ((halfReadOut (Y := Y₁) (u := v₁) z' e' he' e.2 hk).trans
    ((hc e.2).trans ((halfReadOut (Y := Y₀) (u := v₀) z e he e.2 rfl).symm.trans (cast_heq _ _).symm)))

include hg in
theorem localTarget (hc : (∀ k : Fin (2 ^ b),
      HEq (z'.2 (inEdge Y₁ v₁ k) (inEdge_dst Y₁ v₁ k))
        (z.2 (inEdge Y₀ v₀ k) (inEdge_dst Y₀ v₀ k)))) (t : Fin 4)
    (h : v₀ = packedSiteEquiv (X.packingData.survivingRole L (targetRole L t) m))
    (h' : v₁ = packedSiteEquiv (X'.packingData.survivingRole L (targetRole L t) m₁))
    (hw : w₁ m₁ (L,t) = w₀ m (L,t)) :
    HEq (X'.packingData.localSurvivingTarget L (SD a b) (fun n i => w₁ n (L,i)) I₁ hpos m₁ t (atSite (N := (Y₁).network) h' z'))
      (X.packingData.localSurvivingTarget L (SD a b) (fun n i => w₀ n (L,i)) I₀ hpos m t (atSite (N := (Y₀).network) h z)) := by
  unfold PackingData.localSurvivingTarget
  refine concat_heq hw (ready.count_pos t) _ _ ?_
  intro i
  let e := actualArc (ready := ready) X L m t i
  let e' := actualArc (ready := ready) X' L m₁ t i
  have he : v₀ = (Y₀).network.dst e :=
    h.trans (X.packingData.shrinkArc_endpoints L (SD a b) I₀ ⟨t,m,i⟩).2.symm
  have he' : v₁ = (Y₁).network.dst e' :=
    h'.trans (X'.packingData.shrinkArc_endpoints L (SD a b) I₁ ⟨t,m₁,i⟩).2.symm
  let k := ((I₀).graph.actualGraph.target e).2
  have hk : ((I₁).graph.actualGraph.target e').2 = k :=
    actualArc_in_slot (ready := ready) hg L j m hE t i (congrArg Prod.fst h).symm
  exact (cast_heq _ _).trans ((halfReadIn (Y := Y₁) (u := v₁) z' e' he' k hk).trans
    ((hc k).trans ((halfReadIn (Y := Y₀) (u := v₀) z e he k rfl).symm.trans (cast_heq _ _).symm)))


local notation "owners₀" => X.packingData.shrinkInternalOwner L
local notation "owners₁" => X'.packingData.shrinkInternalOwner L

section Owners

variable (hg' : Good3 X' X (pb X X' x)) (hch : Ch3 B X X' s s' x)
variable {L' : Bool} (hLL : L = L')

include hch in
theorem ownerWidth (e : {e : X.packingData.Motif × Fin 4 // v₀ = owners₀ e}) :
    internalLabel w₀ L e.val = internalLabel w₁ L' (ownEquiv hg hg' L L' hLL j l e).val := by
  obtain ⟨⟨n,t⟩, hn⟩ := e
  have hx : (X.packingData.survivingRole L (internalRole L t) n).1 = x :=
    (congrArg (fun p => p.1.1) hn).symm
  have equalWidth := selW_eq B hg s s' hch L (internalRole L t) n hx (owner_ends hg L j l (n,t) hn) (!L,t)
  subst L'
  exact congrArg (fun d => Fin (2 ^ d)) equalWidth

noncomputable def internalEquiv :
    Placed owners₀ (internalLabel w₀ L) v₀ ≃
      Placed (X'.packingData.shrinkInternalOwner L') (internalLabel w₁ L') v₁ :=
  placedCongr (ownEquiv hg hg' L L' hLL j l) (fun e => Equiv.cast (ownerWidth hg hg' hch hLL e))

theorem internalEquiv_apply (h : Placed owners₀ (internalLabel w₀ L) v₀)
    (t : Fin 4) (hm : v₀ = owners₀ (m,t))
    (hm' : v₁ = X'.packingData.shrinkInternalOwner L' (m₁,t)) :
    HEq (internalEquiv (s := s) (s' := s') (j := j) (l := l) hg hg' hch hLL h (m₁,t) hm') (h (m,t) hm) := by
  have eq : (ownEquiv hg hg' L L' hLL j l ⟨(m,t), hm⟩).val = (m₁,t) := rfl
  exact (placedCongr_heq (ownEquiv hg hg' L L' hLL j l)
    (fun e => Equiv.cast (ownerWidth hg hg' hch hLL e)) h (m,t) hm (m₁,t) hm' eq).trans (cast_heq _ _)

end Owners

private noncomputable abbrev supplyArg (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (L : Bool)
    (m : X.packingData.Motif) (p : Fin 6) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite L m p)
    (h : Placed (X.packingData.shrinkInternalOwner L) (internalLabel (selW B X s) L) v)
    (z : (outputState B ready X s L).network.Half v) :=
  X.packingData.shrinkLocalSupplyArg L (SD a b) (selW B X s)
    (X.shrinkStateIndex ready L) hpos m p (hv ▸ h) (hv ▸ z)

private theorem supplyOut_active (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p)
    (hr : v = packedSiteEquiv (X.packingData.survivingRole layout (sourceRole layout t) m))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v)
    (z : (outputState B ready X c layout).network.Half v) (hp : p = supply.src (layout,t)) :
    (supplyArg (B := B) (ready := ready) X c layout m p hv h z).1 (layout,t) hp =
      (RAMSerialization.wordBits _).symm
        (X.packingData.localSurvivingSource layout (SD a b) (fun n i => selW B X c n (layout,i)) (X.shrinkStateIndex ready layout) hpos m t (atSite (N := (outputState B ready X c layout).network) hr z)) := by
  subst hv
  cases layout <;> rfl

private theorem supplyIn_active (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p)
    (hr : v = packedSiteEquiv (X.packingData.survivingRole layout (targetRole layout t) m))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v)
    (z : (outputState B ready X c layout).network.Half v) (hp : p = supply.dst (layout,t)) :
    (supplyArg (B := B) (ready := ready) X c layout m p hv h z).2 (layout,t) hp =
      (RAMSerialization.wordBits _).symm
        (X.packingData.localSurvivingTarget layout (SD a b) (fun n i => selW B X c n (layout,i)) (X.shrinkStateIndex ready layout) hpos m t (atSite (N := (outputState B ready X c layout).network) hr z)) := by
  subst hv
  cases layout <;> rfl

private theorem supplyOut_internal (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p) (hi : v = (X.packingData.shrinkInternalOwner layout) (m,t))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v) (z : (outputState B ready X c layout).network.Half v)
    (hp : p = supply.src (!layout,t)) :
    (supplyArg (B := B) (ready := ready) X c layout m p hv h z).1 (!layout,t) hp = h (m,t) hi := by
  cases layout <;> exact placed_at hv h (m,t) _

private theorem supplyIn_internal (c : X.ShrinkSelection B) (layout : Bool) (m : X.packingData.Motif)
    (p : Fin 6) (t : Fin 4) {v : (X.Base × TagW a) × BitWord g}
    (hv : v = X.packingData.shrinkPartySite layout m p) (hi : v = (X.packingData.shrinkInternalOwner layout) (m,t))
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X c) layout) v) (z : (outputState B ready X c layout).network.Half v)
    (hp : p = supply.dst (!layout,t)) :
    (supplyArg (B := B) (ready := ready) X c layout m p hv h z).2 (!layout,t) hp = h (m,t) hi := by
  cases layout <;> exact placed_at hv h (m,t) _

private theorem supplyArg_heq_same (hg' : Good3 X' X (pb X X' x)) (hch : Ch3 B X X' s s' x)
    (ho : (∀ k : Fin (2 ^ b),
      HEq (z'.1 (outEdge Y₁ v₁ k) (outEdge_src Y₁ v₁ k))
        (z.1 (outEdge Y₀ v₀ k) (outEdge_src Y₀ v₀ k)))) (hn : (∀ k : Fin (2 ^ b),
      HEq (z'.2 (inEdge Y₁ v₁ k) (inEdge_dst Y₁ v₁ k))
        (z.2 (inEdge Y₀ v₀ k) (inEdge_dst Y₀ v₀ k)))) (p : Fin 6)
    (h : Placed owners₀ (internalLabel w₀ L) v₀)
    (hv : v₀ = X.packingData.shrinkPartySite L m p)
    (hv' : v₁ = X'.packingData.shrinkPartySite L m₁ p) :
    HEq (supplyArg (B := B) (ready := ready) X' s' L m₁ p (v := v₁) hv' (internalEquiv (s := s) (s' := s') (j := j) (l := l) hg hg' hch rfl h) z')
      (supplyArg (B := B) (ready := ready) X s L m p (v := v₀) hv h z) := by
  have hx : (X.packingData.survivingRole L (partyRole L p) m).1 = x :=
    (congrArg (fun v => v.1.1) hv).symm
  have widths : w₁ m₁ = w₀ m :=
    funext fun e => (selW_eq B hg s s' hch L (partyRole L p) m hx hE e).symm
  apply halfBits_heq widths
  · rintro ⟨b,t⟩ hp
    by_cases hb : b = L
    · subst b
      have hrs : partyRole L p = sourceRole L t :=
        (congrArg (partyRole L) hp).trans (role_src_survives L t)
      have hs := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole L r m)) hrs)
      have hs' := hv'.trans (congrArg (fun r => packedSiteEquiv (X'.packingData.survivingRole L r m₁)) hrs)
      rw [supplyOut_active s' L m₁ p t hv' hs' _ z' hp, supplyOut_active s L m p t hv hs h z hp]
      exact encode_val (congrFun widths (L,t))
        (localSource hg m hE ho t hs hs' (congrFun widths (L,t)))
    · obtain rfl := Bool.eq_not_of_ne hb
      have hr : partyRole L p = internalRole L t :=
        (congrArg (partyRole L) hp).trans (role_src_absorbed L t)
      have hi := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole L r m)) hr)
      have hi' := hv'.trans (congrArg (fun r => packedSiteEquiv (X'.packingData.survivingRole L r m₁)) hr)
      rw [supplyOut_internal s' L m₁ p t hv' hi' _ z' hp, supplyOut_internal s L m p t hv hi h z hp]
      exact finVal_eq (congrArg (fun w => 2 ^ w) (congrFun widths (!L,t)))
        (internalEquiv_apply hg m hE hg' hch rfl h t hi hi')
  · rintro ⟨b,t⟩ hp
    by_cases hb : b = L
    · subst b
      have hrs : partyRole L p = targetRole L t :=
        (congrArg (partyRole L) hp).trans (role_dst_survives L t)
      have hs := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole L r m)) hrs)
      have hs' := hv'.trans (congrArg (fun r => packedSiteEquiv (X'.packingData.survivingRole L r m₁)) hrs)
      rw [supplyIn_active s' L m₁ p t hv' hs' _ z' hp, supplyIn_active s L m p t hv hs h z hp]
      exact encode_val (congrFun widths (L,t))
        (localTarget hg m hE hn t hs hs' (congrFun widths (L,t)))
    · obtain rfl := Bool.eq_not_of_ne hb
      have hr : partyRole L p = internalRole L t :=
        (congrArg (partyRole L) hp).trans (role_dst_absorbed L t)
      have hi := hv.trans (congrArg (fun r => packedSiteEquiv (X.packingData.survivingRole L r m)) hr)
      have hi' := hv'.trans (congrArg (fun r => packedSiteEquiv (X'.packingData.survivingRole L r m₁)) hr)
      rw [supplyIn_internal s' L m₁ p t hv' hi' _ z' hp, supplyIn_internal s L m p t hv hi h z hp]
      exact finVal_eq (congrArg (fun w => 2 ^ w) (congrFun widths (!L,t)))
        (internalEquiv_apply hg m hE hg' hch rfl h t hi hi')

theorem supplyArg_heq {L' : Bool} (hLL : L = L')
    (hg' : Good3 X' X (pb X X' x)) (hch : Ch3 B X X' s s' x)
    {z' : (outputState B ready X' s' L').network.Half v₁}
    (ho : (∀ k : Fin (2 ^ b),
      HEq (z'.1 (outEdge (outputState B ready X' s' L') v₁ k) (outEdge_src (outputState B ready X' s' L') v₁ k))
        (z.1 (outEdge Y₀ v₀ k) (outEdge_src Y₀ v₀ k))))
    (hn : (∀ k : Fin (2 ^ b),
      HEq (z'.2 (inEdge (outputState B ready X' s' L') v₁ k) (inEdge_dst (outputState B ready X' s' L') v₁ k))
        (z.2 (inEdge Y₀ v₀ k) (inEdge_dst Y₀ v₀ k)))) (p : Fin 6)
    (h : Placed owners₀ (internalLabel w₀ L) v₀)
    (hv : v₀ = X.packingData.shrinkPartySite L m p)
    (hv' : v₁ = X'.packingData.shrinkPartySite L' m₁ p) :
    HEq (supplyArg (B := B) (ready := ready) X' s' L' m₁ p (v := v₁) hv' (internalEquiv (s := s) (s' := s') (j := j) (l := l) hg hg' hch hLL h) z')
      (supplyArg (B := B) (ready := ready) X s L m p (v := v₀) hv h z) := by
  subst L'
  exact supplyArg_heq_same hg m hE hg' hch ho hn p h hv hv'

end Supply

end P1P7.SolKernloc
