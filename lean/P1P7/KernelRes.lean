import P1P7.KernelPos
import P1P7.KernelForm

/-!
# P7 kernel locality, layer 4: resident maps, internal owners and their data

* `resEquiv`: the resident maps `(m, j)` at `((x, tg), l)` correspond to those at `((pb x, tg), l)` (`m ↦ tM m`).
* `ownEquiv`: the absorbed internal words owned by the two sites correspond in the same way.
* `selW_eq`, `demandWidths_eq`, `choiceVal_eq`: widths and term choices of corresponding motifs agree.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.NetworkKernel


section Sites

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}

theorem partySite_tM (L : Bool) (m : X.packingData.Motif) (h : EndsGood X X' m.val) (j : Fin 6) :
    X'.packingData.shrinkPartySite L (tM m h) j =
      ((pb X X' (X.packingData.shrinkPartySite L m j).1.1, (X.packingData.shrinkPartySite L m j).1.2),
        (X.packingData.shrinkPartySite L m j).2) := by
  unfold PackingData.shrinkPartySite
  rw [survivingRole_tA L _ m (tM m h) rfl h]
  rfl

theorem owner_tM (L : Bool) (m : X.packingData.Motif) (h : EndsGood X X' m.val) (t : Fin 4) :
    X'.packingData.shrinkInternalOwner L (tM m h, t) =
      ((pb X X' (X.packingData.shrinkInternalOwner L (m, t)).1.1,
        (X.packingData.shrinkInternalOwner L (m, t)).1.2), (X.packingData.shrinkInternalOwner L (m, t)).2) := by
  unfold PackingData.shrinkInternalOwner
  rw [survivingRole_tA L _ m (tM m h) rfl h]
  rfl

/-- A motif with a role at base `x` has both wire ends within 2 of `x`. -/
theorem ends_near_of_role (L : Bool) (r : PackedRole) (m : X.packingData.Motif) {x : X.Base}
    (hx : (X.packingData.survivingRole L r m).1 = x) :
    (baseGraph X).edist x m.val.1.1.1 ≤ 2 ∧
      (baseGraph X).edist x (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 ≤ 2 := by
  subst hx
  exact role_ends X L r m

theorem resident_ends {x : X.Base} (hg : Good3 X X' x) (L : Bool) (tg : TagW a) (l : BitWord g)
    (p : X.packingData.Motif × Fin 6) (hp : X.packingData.shrinkPartySite L p.1 p.2 = ((x, tg), l)) :
    EndsGood X X' p.1.val := by
  have hx : (X.packingData.survivingRole L (partyRole L p.2) p.1).1 = x := congrArg (fun q => q.1.1) hp
  obtain ⟨h1, h2⟩ := ends_near_of_role L _ p.1 hx
  exact (motif_conds hg p.1 h1 h2).1

theorem owner_ends {x : X.Base} (hg : Good3 X X' x) (L : Bool) (tg : TagW a) (l : BitWord g)
    (e : X.packingData.Motif × Fin 4) (he : ((x, tg), l) = X.packingData.shrinkInternalOwner L e) :
    EndsGood X X' e.1.val := by
  have hx : (X.packingData.survivingRole L (internalRole L e.2) e.1).1 = x :=
    (congrArg (fun q => q.1.1) he).symm
  obtain ⟨h1, h2⟩ := ends_near_of_role L _ e.1 hx
  exact (motif_conds hg e.1 h1 h2).1

/-- Resident maps at `((x, tg), l)` and at `((pb x, tg), l)` (layouts `L = L'`). -/
noncomputable def resEquiv {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) :
    {p : X.packingData.Motif × Fin 6 // X.packingData.shrinkPartySite L p.1 p.2 = ((x, tg), l)} ≃
      {p : X'.packingData.Motif × Fin 6 //
        X'.packingData.shrinkPartySite L' p.1 p.2 = ((pb X X' x, tg), l)} :=
  subEquiv (fun p hp => (tM p.1 (resident_ends hg L tg l p hp), p.2))
    (fun p hp => by
      dsimp only
      subst hLL
      rw [partySite_tM, hp])
    (fun p' hp' => (tM p'.1 (resident_ends hg' L' tg l p' hp'), p'.2))
    (fun p' hp' => by
      dsimp only
      subst hLL
      have hx : pb X' X (pb X X' x) = x := pb_pb X X' (hg x (by simp)).addr_eq
      rw [partySite_tM, hp', hx])
    (fun p hp => Prod.ext (Subtype.ext (tA_tA X X' p.1.val (resident_ends hg L tg l p hp).1)) rfl)
    (fun p' hp' => Prod.ext (Subtype.ext (tA_tA X' X p'.1.val (resident_ends hg' L' tg l p' hp').1)) rfl)

theorem resEquiv_apply {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) (p : X.packingData.Motif × Fin 6)
    (hp : X.packingData.shrinkPartySite L p.1 p.2 = ((x, tg), l)) :
    (resEquiv hg hg' L L' hLL tg l ⟨p, hp⟩).1 = (tM p.1 (resident_ends hg L tg l p hp), p.2) := rfl

/-- Internal words owned by `((x, tg), l)` and by `((pb x, tg), l)` (layouts `L = L'`). -/
noncomputable def ownEquiv {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) :
    {e : X.packingData.Motif × Fin 4 // ((x, tg), l) = X.packingData.shrinkInternalOwner L e} ≃
      {e : X'.packingData.Motif × Fin 4 //
        ((pb X X' x, tg), l) = X'.packingData.shrinkInternalOwner L' e} :=
  subEquiv (fun e he => (tM e.1 (owner_ends hg L tg l e he), e.2))
    (fun e he => by
      subst hLL
      rw [owner_tM, ← he])
    (fun e' he' => (tM e'.1 (owner_ends hg' L' tg l e' he'), e'.2))
    (fun e' he' => by
      subst hLL
      have hx : pb X' X (pb X X' x) = x := pb_pb X X' (hg x (by simp)).addr_eq
      rw [owner_tM, ← he', hx])
    (fun e he => Prod.ext (Subtype.ext (tA_tA X X' e.1.val (owner_ends hg L tg l e he).1)) rfl)
    (fun e' he' => Prod.ext (Subtype.ext (tA_tA X' X e'.1.val (owner_ends hg' L' tg l e' he').1)) rfl)

theorem ownEquiv_apply {x : X.Base} (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x))
    (L L' : Bool) (hLL : L = L') (tg : TagW a) (l : BitWord g) (e : X.packingData.Motif × Fin 4)
    (he : ((x, tg), l) = X.packingData.shrinkInternalOwner L e) :
    (ownEquiv hg hg' L L' hLL tg l ⟨e, he⟩).1 = (tM e.1 (owner_ends hg L tg l e he), e.2) := rfl

end Sites

section Data

variable {a g : ℕ} {factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- Term data agree on the ball of radius 3. -/
def Ch3 (X X' : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) : Prop :=
  ∀ y, (baseGraph X).edist x y ≤ 3 → choiceAt B X s y = choiceAt B X' s' (pb X X' y)

variable {X X' : State a (packingLaneBits a g)}

/-- The data of a motif with a role at a base near `x`. -/
theorem role_data {x : X.Base} (hg : Good3 X X' x) (L : Bool) (r : PackedRole) (m : X.packingData.Motif)
    (hx : (X.packingData.survivingRole L r m).1 = x) :
    EndsGood X X' m.val ∧
      (∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m → EndsGood X X' m2.val) ∧
      SGood X X' (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1 ∧
      (baseGraph X).edist x m.val.1.1.1 ≤ 3 := by
  obtain ⟨h1, h2⟩ := ends_near_of_role L r m hx
  exact ⟨(motif_conds hg m h1 h2).1, (motif_conds hg m h1 h2).2.1, (motif_conds hg m h1 h2).2.2,
    h1.trans (by norm_num)⟩

theorem demandWidths_eq {x : X.Base} (hg : Good3 X X' x) (L : Bool) (r : PackedRole)
    (m : X.packingData.Motif) (hx : (X.packingData.survivingRole L r m).1 = x) (h : EndsGood X X' m.val) :
    X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m =
      X'.packingData.shrinkDemandWidths X'.shrinkNumber X'.packingWidth (tM m h) := by
  obtain ⟨hE, hball, hBg, -⟩ := role_data hg L r m hx
  unfold PackingData.shrinkDemandWidths
  rw [abWidth_eq m (tM m h) rfl hE hball hBg, tM_val, packingWidth_tA m.val hE.1]

theorem choiceVal_eq {x : X.Base} (hg : Good3 X X' x) (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (hch : Ch3 B X X' s s' x) (L : Bool) (r : PackedRole)
    (m : X.packingData.Motif) (hx : (X.packingData.survivingRole L r m).1 = x) (h : EndsGood X X' m.val) :
    (s m).val = (s' (tM m h)).val :=
  choice_eq B s s' m (tM m h) rfl (hch _ (role_data hg L r m hx).2.2.2)

theorem selW_eq {x : X.Base} (hg : Good3 X X' x) (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (hch : Ch3 B X X' s s' x) (L : Bool) (r : PackedRole)
    (m : X.packingData.Motif) (hx : (X.packingData.survivingRole L r m).1 = x) (h : EndsGood X X' m.val)
    (e : Bool × Fin 4) :
    selW B X s m e = selW B X' s' (tM m h) e := by
  obtain ⟨hE, hball, hBg, hd⟩ := role_data hg L r m hx
  exact termWidths_eq B s s' m (tM m h) rfl hE hball hBg (hch _ hd) e.1 e.2

end Data

end P1P7
