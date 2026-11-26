import P1P7.ShrinkGraph

/-!
# P7, shrink half, layer 5: the widths at `(x, j)`

The width of a genuine new arc is a slice (`splitWidth`) of OpenAI's `termWidths` (PackedShrinkStep.lean:71) of the
actual motif. `termWidths` reads: the selected term (`choiceAt` at the wire's source base), the old CD width
(`packingWidth`), and the AB width (`abWidth`, SlotDemandEnergy.lean:47): a slice of the bundle width (sum over the
thick wires of the bundle) at the rank of the motif in its bundle (`sortedBundleNumbering`). All are transported.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBaseWidth {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

section Width

variable {a g : ℕ}

theorem packingWidth_tA {X X' : State a (packingLaneBits a g)}
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) (h : SGood X X' α.1.1.1) :
    X'.packingWidth (tA X X' α) = X.packingWidth α :=
  (h.width_eq α.1.2 ((packingFields a g).symm (α.2.1, α.2.2, α.1.1.2))).symm

/-- The bundle width as a sum over colour bits and slot labels. -/
theorem bundleWidth_sum (X : State a (packingLaneBits a g))
    (w : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1) → ℕ)
    (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) :
    X.packingData.bundleWidth w b = ∑ uh : BitWord (2 * 2 ^ a + 1) × BitWord a,
      if X.packingData.thick (sourcePosition (b, uh)) ∧
          X.packingData.thick (sourcePosition (X.packingData.actual (b, uh))) then w (b, uh) else 0 := by
  let e : {t : X.packingData.ThickWire // t.1.1 = b} ≃ {uh : BitWord (2 * 2 ^ a + 1) × BitWord a //
      X.packingData.thick (sourcePosition (b, uh)) ∧
        X.packingData.thick (sourcePosition (X.packingData.actual (b, uh)))} :=
    { toFun := fun t => ⟨t.1.1.2, by
        obtain ⟨⟨⟨p, uh⟩, hc⟩, hb⟩ := t
        change X.packingData.thick (sourcePosition (b, uh)) ∧
          X.packingData.thick (sourcePosition (X.packingData.actual (b, uh)))
        rw [← show p = b from hb]
        exact hc⟩
      invFun := fun uh => ⟨⟨(b, uh.1), uh.2⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨p, uh⟩, hc⟩, hb⟩
        apply Subtype.ext
        apply Subtype.ext
        change (b, uh) = (p, uh)
        rw [show p = b from hb]
      right_inv := by rintro ⟨uh, hc⟩; rfl }
  unfold PackingData.bundleWidth
  rw [← Finset.sum_filter]
  refine (Fintype.sum_equiv e (fun t => w t.1.1) (fun uh => w (b, uh.1)) ?_).trans ?_
  · rintro ⟨⟨⟨p, uh⟩, hc⟩, hb⟩
    change w (p, uh) = w (b, uh)
    rw [show p = b from hb]
  · exact (Finset.sum_subtype _ (fun uh => by simp) (fun uh => w (b, uh))).symm

theorem bundleWidth_tS {X X' : State a (packingLaneBits a g)}
    (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1) :
    X'.packingData.bundleWidth X'.packingWidth (tS X X' b.1, b.2) =
      X.packingData.bundleWidth X.packingWidth b := by
  rw [bundleWidth_sum, bundleWidth_sum]
  refine Finset.sum_congr rfl fun uh _ => ?_
  have hE : EndsGood X X' (b, uh) := ⟨h1, h2⟩
  have hc := thickThick_tA X X' (b, uh) hE
  have hw := packingWidth_tA (b, uh) h1
  change (if X'.packingData.thick (sourcePosition (tA X X' (b, uh))) ∧
      X'.packingData.thick (sourcePosition (X'.packingData.actual (tA X X' (b, uh))))
    then X'.packingWidth (tA X X' (b, uh)) else 0) = _
  rw [hw]
  by_cases hcond : X.packingData.thick (sourcePosition (b, uh)) ∧
      X.packingData.thick (sourcePosition (X.packingData.actual (b, uh)))
  · rw [if_pos (hc.mpr hcond), if_pos hcond]
  · rw [if_neg (fun h => hcond (hc.mp h)), if_neg hcond]

/-- The motifs of a bundle. -/
noncomputable def bfib (X : State a (packingLaneBits a g)) (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) :
    Finset X.packingData.Motif :=
  Finset.univ.filter (fun m => X.packingData.bundle m = b)

theorem card_bfib (X : State a (packingLaneBits a g)) (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) :
    (bfib X b).card = 3 * (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) / 4 := by
  unfold bfib
  rw [← Fintype.card_subtype]
  exact X.packingData.card_motifs_bundle (State.two_le_packingColors a) b

theorem arcKey_baseMotif (X : State a (packingLaneBits a g)) (m : X.packingData.Motif) :
    arcKey X (X.packingData.baseMotif m).1.1 = arcKey X m.val := rfl

/-- OpenAI's bundle numbering compares by `arcKey`. Same proof as OpenAI's `sortedBundle_lt`
(CompressorRecordsBundleRank.lean:90; that file is not in our build closure). -/
theorem sortedBundle_lt' (X : State a (packingLaneBits a g)) (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (x y : X.packingData.MotifFiber b) :
    X.shrinkNumber b x < X.shrinkNumber b y ↔ arcKey X x.1.val < arcKey X y.1.val := by
  let z : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a) := ((b.1.1, b.1.2.1, 0), b.2)
  let toZero (u : X.packingData.MotifFiber b) : X.packingData.MotifFiber z :=
    ⟨X.packingData.translateMotif u.1 (-b.1.2.2), by simp [z, u.2, translateSite]⟩
  let key := fun u : X.packingData.MotifFiber z ↦
    X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
      (X.packingData.baseMotif u.1)
  let := LinearOrder.lift' key
    (X.packingData.motifFiberIndex_injective X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) z)
  let e := (Fintype.orderIsoFinOfCardEq (X.packingData.MotifFiber z)
    (X.packingData.card_motifs_bundle (State.two_le_packingColors a) z)).symm
  change e (toZero x) < e (toZero y) ↔ _
  rw [e.lt_iff_lt]
  change ((X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
      (X.packingData.baseMotif (X.packingData.translateMotif x.1 (-b.1.2.2))) : ℕ)) <
      (X.packingData.baseMotifIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
        (X.packingData.baseMotif (X.packingData.translateMotif y.1 (-b.1.2.2))) : ℕ) ↔ _
  rw [PackingData.baseMotif_translate, PackingData.baseMotif_translate, baseMotifIndex_val,
    baseMotifIndex_val]
  exact Iff.rfl

/-- A numbering that is monotone for a key counts the smaller keys (generic, so that nothing is unfolded). -/
theorem rank_of_lt {A : Type*} [Fintype A] {n : ℕ} (num : A ≃ Fin n) (key : A → ℕ)
    (hlt : ∀ y x, num y < num x ↔ key y < key x) (x : A) :
    ((num x : ℕ)) = Fintype.card {y // key y < key x} := by
  rw [← Fintype.card_fin_lt_of_le (num x).isLt.le]
  exact (Fintype.card_congr (num.subtypeEquiv (p := fun y => key y < key x)
    (q := fun i : Fin n => (i : ℕ) < (num x : ℕ)) (fun y => (hlt y x).symm))).symm

/-- The bundle number of a motif is the number of motifs of its bundle with a smaller `arcKey`. -/
theorem bundle_rank (X : State a (packingLaneBits a g)) (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (x : X.packingData.MotifFiber b) :
    ((X.shrinkNumber b x : ℕ)) =
      Fintype.card {y : X.packingData.MotifFiber b // arcKey X y.1.val < arcKey X x.1.val} :=
  rank_of_lt (X.shrinkNumber b) (fun y => arcKey X y.1.val) (fun y x => sortedBundle_lt' X b y x) x

/-- Rank transport for subtypes (cardinalities instead of filters). -/
theorem card_lt_transport {E E' : Type*} [Fintype E] [Fintype E'] (key : E → ℕ) (key' : E' → ℕ)
    (hinj : Function.Injective key) (hinj' : Function.Injective key')
    (hcard : Fintype.card E' ≤ Fintype.card E) (hpart : ∀ e, ∃ e', key' e' = key e) (κ : ℕ) :
    Fintype.card {z // key z < κ} = Fintype.card {z // key' z < κ} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact rank_transport Finset.univ Finset.univ key key' hinj.injOn hinj'.injOn
    (by simpa using hcard) (fun e _ => by obtain ⟨e', he'⟩ := hpart e; exact ⟨e', Finset.mem_univ _, he'⟩) κ

/-- Bundle numbers are transported when all motifs of the bundle have good ends. -/
theorem bundle_rank_eq {X X' : State a (packingLaneBits a g)} (m : X.packingData.Motif)
    (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val) (hE : EndsGood X X' m.val)
    (hball : ∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m →
      EndsGood X X' m2.val) :
    ((X.shrinkNumber (X.packingData.bundle m) ⟨m, rfl⟩ : ℕ)) =
      ((X'.shrinkNumber (X'.packingData.bundle m') ⟨m', rfl⟩ : ℕ)) := by
  have hbm : X'.packingData.bundle m' = (tS X X' (X.packingData.bundle m).1, (X.packingData.bundle m).2) :=
    bundle_tA m m' hm hE
  have hkey : arcKey X m.val = arcKey X' m'.val := by rw [hm]; exact (arcKey_tA m.val hE.1.addr_eq).symm
  rw [bundle_rank X _ ⟨m, rfl⟩, bundle_rank X' _ ⟨m', rfl⟩]
  change Fintype.card {y : X.packingData.MotifFiber (X.packingData.bundle m) // arcKey X y.1.val < arcKey X m.val} =
    Fintype.card {y : X'.packingData.MotifFiber (X'.packingData.bundle m') // arcKey X' y.1.val < arcKey X' m'.val}
  rw [← hkey]
  refine card_lt_transport (fun y : X.packingData.MotifFiber (X.packingData.bundle m) => arcKey X y.1.val)
    (fun y : X'.packingData.MotifFiber (X'.packingData.bundle m') => arcKey X' y.1.val) ?_ ?_ ?_ ?_ _
  · intro y1 y2 heq
    exact X.packingData.motifFiberIndex_injective X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) _
      (Fin.ext (by beta_reduce; rw [baseMotifIndex_val, baseMotifIndex_val]; exact heq))
  · intro y1 y2 heq
    exact X'.packingData.motifFiberIndex_injective X'.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) _
      (Fin.ext (by beta_reduce; rw [baseMotifIndex_val, baseMotifIndex_val]; exact heq))
  · rw [X.packingData.card_motifs_bundle (State.two_le_packingColors a),
      X'.packingData.card_motifs_bundle (State.two_le_packingColors a)]
  · intro y
    have hE2 := hball y.1 y.2
    have hmot := motif_tA X X' y.1.val hE2 y.1.property
    have hb' : X'.packingData.bundle ⟨tA X X' y.1.val, hmot⟩ = X'.packingData.bundle m' := by
      rw [bundle_tA y.1 ⟨tA X X' y.1.val, hmot⟩ rfl hE2, y.2, hbm]
    exact ⟨⟨⟨tA X X' y.1.val, hmot⟩, hb'⟩, arcKey_tA y.1.val hE2.1.addr_eq⟩

end Width

/-! ## The term widths -/

section Terms

variable {a g : ℕ} {factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem abWidth_eq {X X' : State a (packingLaneBits a g)} (m : X.packingData.Motif)
    (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val) (hE : EndsGood X X' m.val)
    (hball : ∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m →
      EndsGood X X' m2.val)
    (hBg : SGood X X' (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1) :
    X.packingData.abWidth X.shrinkNumber X.packingWidth m =
      X'.packingData.abWidth X'.shrinkNumber X'.packingWidth m' := by
  have hbm : X'.packingData.bundle m' = (tS X X' (X.packingData.bundle m).1, (X.packingData.bundle m).2) :=
    bundle_tA m m' hm hE
  have hbw : X'.packingData.bundleWidth X'.packingWidth (X'.packingData.bundle m') =
      X.packingData.bundleWidth X.packingWidth (X.packingData.bundle m) := by
    rw [hbm]; exact bundleWidth_tS _ (C_good m hE) hBg
  have hr : X.shrinkNumber (X.packingData.bundle m) ⟨m, rfl⟩ =
      X'.shrinkNumber (X'.packingData.bundle m') ⟨m', rfl⟩ :=
    Fin.ext (bundle_rank_eq m m' hm hE hball)
  unfold PackingData.abWidth
  rw [hbw, hr]

/-- The selected terms agree when the term data at the wire's source agree. -/
theorem choice_eq {X X' : State a (packingLaneBits a g)} (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (m : X.packingData.Motif) (m' : X'.packingData.Motif) (hm : m'.val = tA X X' m.val)
    (hch : choiceAt B X s m.val.1.1.1 = choiceAt B X' s' (pb X X' m.val.1.1.1)) :
    (s m).val = (s' m').val := by
  obtain ⟨⟨⟨⟨y, t, l⟩, i⟩, u, hh⟩, hmp⟩ := m
  obtain ⟨α', hmp'⟩ := m'
  change α' = tA X X' (((y, t, l), i), u, hh) at hm
  subst hm
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hch i) t) l) u) hh
  have hmp'' : ¬ (X'.packingData.thick (sourcePosition (((pb X X' y, (t, l)), i), (u, hh))) ∧
      X'.packingData.thick (sourcePosition (X'.packingData.actual (((pb X X' y, (t, l)), i), (u, hh))))) := hmp'
  simp only [choiceAt] at h
  rw [dif_pos hmp, dif_pos hmp''] at h
  exact Option.some.inj h

theorem termWidths_eq {X X' : State a (packingLaneBits a g)} (s : X.ShrinkSelection B)
    (s' : X'.ShrinkSelection B) (m : X.packingData.Motif) (m' : X'.packingData.Motif)
    (hm : m'.val = tA X X' m.val) (hE : EndsGood X X' m.val)
    (hball : ∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m →
      EndsGood X X' m2.val)
    (hBg : SGood X X' (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1)
    (hch : choiceAt B X s m.val.1.1.1 = choiceAt B X' s' (pb X X' m.val.1.1.1)) (layout : Bool) (e : Fin 4) :
    X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout e =
      X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m' layout e := by
  have hold : X.packingWidth m.val = X'.packingWidth m'.val := by
    rw [hm, packingWidth_tA m.val hE.1]
  unfold PackingData.termWidths
  rw [choice_eq B s s' m m' hm hch, abWidth_eq m m' hm hE hball hBg, hold]

end Terms

end P1P7
