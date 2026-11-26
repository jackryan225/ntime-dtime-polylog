import P1C10.Bridge
import P1ChkGreedy.Local

/-!
# P1, check C10 on CODES: the decision that the C10 program makes (lane P1-lean-c10)

The D10 check `C10sRc rc ..` compares a PANEL with the stored numbers. A program computes codes, so this file states
the same check with codes only and proves that it is the same Prop.

* `storedPanel D u ℓ Y A G`: the stored numbers of the panel of address `Y` at level `ℓ` (2^A slots, 2^G lanes) as a
  `PanelCode` (the raw numbers, no decoding). `DispOK`: every stored displacement is below `2^G` (else no panel has
  these numbers: a malformed panel).
* `panelMatch_iff_code`: `PanelMatch D u ℓ Y p ↔ codePanel p = storedPanel D u ℓ Y A G`.
* `C10sCode rcS a b g D u ℓ Y`, `C10rCode rcR a a₀ g dH D u ℓ Y`: the recomputation on codes, applied to the ball list of
  the decoded level-`ℓ` data, returns exactly the stored level-`ℓ+1` code at `Y`, and `DispOK` holds there.
* `C10sCode_iff`, `C10rCode_iff`: these are `C10sRc (shrinkRcOf b g rcS)` and `C10rRc (refreshRcOf a₀ g rcR)`.
* `C10sCode_stage`, `C10rCode_stage`: the stage lemmas under `ShrinkCodeOK` / `RefreshCodeOK` (the program targets).
* D5 family form (number 9): `C10Fix` (the fixed data), `C10Idx`, `C10at`, `C10w`, `cnt10`, `C10w_out`, `C10w_level`.
  Index `i = ℓ + 2^L * Y` (`P1ChkGreedy.encIdx`, `L = levBits`), `ℓ` = substep (`ℓ < top`), `Y` = level-`ℓ+1` address.
  The kind of substep `ℓ` is the format bit `(D.lv ℓ).shrink`; the slot bits are `slotBits D ℓ = log2 (D.lv ℓ).slots`
  (old) and `slotBits D (ℓ+1)` (new); the lane bits `g` are `(D.lv (ℓ+1)).laneW` (lanes of the NEW level).
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-! ## The stored panel as a code -/

/-- The stored numbers of the panel of address `Y` at level `ℓ` (`2^A` slots, `2^G` lanes), as a `PanelCode`. -/
def storedPanel (D : Dims) (u : List Bool) (ℓ Y A G : ℕ) : PanelCode :=
  List.ofFn fun k : Fin (2 ^ A) =>
    ((rdOutAddr D u ℓ Y k, rdOutDisp D u ℓ Y k, rdOutFar D u ℓ Y k),
     (rdInAddr D u ℓ Y k, rdInDisp D u ℓ Y k, rdInFar D u ℓ Y k),
     List.ofFn fun l : Fin (2 ^ G) => rdWidth D u ℓ Y l k)

/-- Every stored displacement of the panel is below `2^G`. -/
def DispOK (D : Dims) (u : List Bool) (ℓ Y A G : ℕ) : Prop :=
  ∀ k : Fin (2 ^ A), rdOutDisp D u ℓ Y k < 2 ^ G ∧ rdInDisp D u ℓ Y k < 2 ^ G

instance (D : Dims) (u : List Bool) (ℓ Y A G : ℕ) : Decidable (DispOK D u ℓ Y A G) := by
  unfold DispOK
  infer_instance

theorem bwNum_lt {G : ℕ} (w : BitWord G) : bwNum w < 2 ^ G := (bitWordFinEquiv G w).isLt

theorem bwNum_bwOf {G n : ℕ} (h : n < 2 ^ G) : bwNum (bwOf G n) = n := by
  unfold bwNum bwOf
  rw [dif_pos h, Equiv.apply_symm_apply]

theorem panelMatch_iff_code (D : Dims) (u : List Bool) (ℓ Y : ℕ) {A G : ℕ} (p : PanelT A G) :
    PanelMatch D u ℓ Y p ↔ codePanel p = storedPanel D u ℓ Y A G := by
  unfold codePanel storedPanel
  rw [List.ofFn_inj]
  constructor
  · intro h
    funext k
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h k
    simp only [codeSlot]
    rw [h1, h2, h3, h4, h5, h6]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show laneList (p.2.2.2.2 k) = List.ofFn fun l : Fin (2 ^ G) => rdWidth D u ℓ Y l k
    unfold laneList
    congr 1
    funext i
    rw [← h7 ((bitWordFinEquiv G).symm i)]
    simp only [bwNum, Equiv.apply_symm_apply]
  · intro h k
    have hk := congrFun h k
    simp only [codeSlot, Prod.mk.injEq] at hk
    obtain ⟨⟨e1, e2, e3⟩, ⟨e4, e5, e6⟩, e7⟩ := hk
    refine ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm, fun l => ?_⟩
    have e := congrArg (fun xs => readAt 0 xs (bwNum l)) e7
    simp only [readAt_laneList] at e
    rw [e]
    unfold bwNum
    rw [readAt_ofFn]

/-- Some panel has the stored numbers iff the stored displacements are in range. -/
theorem exists_match_iff (D : Dims) (u : List Bool) (ℓ Y A G : ℕ) :
    (∃ p : PanelT A G, PanelMatch D u ℓ Y p) ↔ DispOK D u ℓ Y A G := by
  constructor
  · rintro ⟨p, hp⟩ k
    obtain ⟨-, h2, -, -, h5, -⟩ := hp k
    rw [h2, h5]
    exact ⟨bwNum_lt _, bwNum_lt _⟩
  · intro hd
    refine ⟨decPanel D u ℓ Y A G, fun k => ⟨rfl, ?_, rfl, rfl, ?_, rfl, fun l => rfl⟩⟩
    · exact (bwNum_bwOf (hd k).1).symm
    · exact (bwNum_bwOf (hd k).2).symm

/-- The decision on one returned value: `r` is the stored code and the panel is well formed, iff the decoded value
of `r` is a panel that matches the stored numbers. -/
theorem code_iff_aux (D : Dims) (u : List Bool) (ℓ Y A G : ℕ) (r : Option PanelCode) :
    (r = some (storedPanel D u ℓ Y A G) ∧ DispOK D u ℓ Y A G) ↔
      ∃ p : PanelT A G, r.bind (uncodePanel A G) = some p ∧ PanelMatch D u ℓ Y p := by
  cases r with
  | none => simp
  | some c =>
    show (some c = some (storedPanel D u ℓ Y A G) ∧ DispOK D u ℓ Y A G) ↔
      ∃ p : PanelT A G, uncodePanel A G c = some p ∧ PanelMatch D u ℓ Y p
    constructor
    · rintro ⟨hc, hd⟩
      obtain ⟨p, hp⟩ := (exists_match_iff D u ℓ Y A G).mpr hd
      refine ⟨p, uncodePanel_eq_some.mpr ?_, hp⟩
      rw [(panelMatch_iff_code D u ℓ Y p).mp hp]
      exact (Option.some.inj hc).symm
    · rintro ⟨p, hp, hm⟩
      have e1 := uncodePanel_eq_some.mp hp
      have e2 := (panelMatch_iff_code D u ℓ Y p).mp hm
      exact ⟨congrArg some (e1.symm.trans e2), (exists_match_iff D u ℓ Y A G).mp ⟨p, hm⟩⟩

/-! ## Check C10 on codes -/

/-- **C10 on codes, shrinking substep**: `rcS` on the ball list (radius 6) of the decoded level-`ℓ` data, the
layout bit and the child index returns the stored level-`ℓ+1` code at `Y`, and that panel is well formed. -/
def C10sCode (rcS : ShrinkIn → Option PanelCode) (a b g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  rcS (((Y / shrinkJ a, ballList (nbOf shrinkNbrs (decS a g D u ℓ))
      (fun y => (decS a g D u ℓ y).map codeShrinkDatum) (Y / shrinkJ a) 6), layoutOf D u ℓ), Y % shrinkJ a) =
    some (storedPanel D u (ℓ + 1) Y b g) ∧ DispOK D u (ℓ + 1) Y b g

/-- **C10 on codes, refresh substep** (radius 1, no layout bit). -/
def C10rCode (rcR : RefreshIn → Option PanelCode) (a a₀ g dH : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    Prop :=
  rcR ((Y / 2 ^ a, ballList (nbOf refreshNbrs (decR a g dH D u ℓ))
      (fun y => (decR a g dH D u ℓ y).map codeRefreshDatum) (Y / 2 ^ a) 1), Y % 2 ^ a) =
    some (storedPanel D u (ℓ + 1) Y a₀ g) ∧ DispOK D u (ℓ + 1) Y a₀ g

theorem C10sCode_iff (rcS : ShrinkIn → Option PanelCode) (a b g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    C10sCode rcS a b g D u ℓ Y ↔ C10sRc (shrinkRcOf (a := a) b g rcS) D u ℓ Y := by
  have hb := ballList_ballMap shrinkNbrs (decS a g D u ℓ) codeShrinkDatum (Y / shrinkJ a) 6
  unfold C10sCode C10sRc
  show _ ↔ ∃ p, (rcS (((Y / shrinkJ a, ballList (nbOf shrinkNbrs
      (ballMap (nbOf shrinkNbrs (decS a g D u ℓ)) (decS a g D u ℓ) (Y / shrinkJ a) 6))
      (fun y => (ballMap (nbOf shrinkNbrs (decS a g D u ℓ)) (decS a g D u ℓ) (Y / shrinkJ a) 6 y).map
        codeShrinkDatum) (Y / shrinkJ a) 6), layoutOf D u ℓ), Y % shrinkJ a)).bind (uncodePanel b g) = some p ∧
      PanelMatch D u (ℓ + 1) Y p
  rw [hb]
  exact code_iff_aux D u (ℓ + 1) Y b g _

theorem C10rCode_iff (rcR : RefreshIn → Option PanelCode) (a a₀ g dH : ℕ) (D : Dims) (u : List Bool)
    (ℓ Y : ℕ) :
    C10rCode rcR a a₀ g dH D u ℓ Y ↔ C10rRc (refreshRcOf (a := a) (dH := dH) a₀ g rcR) D u ℓ Y := by
  have hb := ballList_ballMap refreshNbrs (decR a g dH D u ℓ) codeRefreshDatum (Y / 2 ^ a) 1
  unfold C10rCode C10rRc
  show _ ↔ ∃ p, (rcR ((Y / 2 ^ a, ballList (nbOf refreshNbrs
      (ballMap (nbOf refreshNbrs (decR a g dH D u ℓ)) (decR a g dH D u ℓ) (Y / 2 ^ a) 1))
      (fun y => (ballMap (nbOf refreshNbrs (decR a g dH D u ℓ)) (decR a g dH D u ℓ) (Y / 2 ^ a) 1 y).map
        codeRefreshDatum) (Y / 2 ^ a) 1), Y % 2 ^ a)).bind (uncodePanel a₀ g) = some p ∧
      PanelMatch D u (ℓ + 1) Y p
  rw [hb]
  exact code_iff_aux D u (ℓ + 1) Y a₀ g _

noncomputable instance (rcS : ShrinkIn → Option PanelCode) (a b g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    Decidable (C10sCode rcS a b g D u ℓ Y) := by
  unfold C10sCode
  infer_instance

noncomputable instance (rcR : RefreshIn → Option PanelCode) (a a₀ g dH : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    Decidable (C10rCode rcR a a₀ g dH D u ℓ Y) := by
  unfold C10rCode
  infer_instance

/-! ## Stage lemmas on codes -/

section Shrink

variable {a b : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- **C10 on codes, stage form (shrink)**, under the program target `ShrinkCodeOK`. -/
theorem C10sCode_stage {rcS : ShrinkIn → Option PanelCode} (hok : ShrinkCodeOK B ready rcS) (g : ℕ)
    (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout D u ℓ = if layoutBit B X s then 1 else 0) :
    (∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sCode rcS a b g D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) := by
  simp only [C10sCode_iff]
  exact C10sRc_stage B ready _ D u ℓ X s (shrinkRcOf_true B ready hok g X s) hN hP hcol hoff hterm hlay

end Shrink

section Refresh

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- **C10 on codes, stage form (refresh)**, under the program target `RefreshCodeOK`. -/
theorem C10rCode_stage {rcR : RefreshIn → Option PanelCode} (hok : RefreshCodeOK P hdH hconn F hD hd rcR)
    (g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    (∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base, C10rCode rcR a a₀ g dH D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
  simp only [C10rCode_iff]
  exact C10rRc_stage P hdH hconn F hD hd _ D u ℓ X c (refreshRcOf_true P hdH hconn F hD hd hok g X c) hN hP hterm

end Refresh

/-! ## D5 family form (family number 9) -/

/-- The fixed data of check C10. The slot bits of a substep are READ FROM THE FORMAT (`slotBits`), because OpenAI's
schedule changes the degree exponent at every shrinking substep of a block (`BlockSchedule.degreeExponent`, one fixed
block `Templates.shrink` with a `Ready` per substep). So the shrink recomputation is a family `rcS a b` indexed by the
slot bits (old `a`, new `b`); the refresh template is one (`Templates.refresh`), with expander degree `dH`. -/
structure C10Fix where
  dH : ℕ
  rcS : ℕ → ℕ → ShrinkIn → Option PanelCode
  rcR : RefreshIn → Option PanelCode

open P1ChkGreedy

/-- The slot bits of level `ℓ` (`slots = 2 ^ slotBits` on a genuine format). -/
def slotBits (D : Dims) (ℓ : ℕ) : ℕ := Nat.log 2 (D.lv ℓ).slots

theorem slotBits_eq {D : Dims} {ℓ a : ℕ} (h : (D.lv ℓ).slots = 2 ^ a) : slotBits D ℓ = a := by
  unfold slotBits
  rw [h, Nat.log_pow (by norm_num)]

/-- Index `i` names a level-`ℓ+1` address `Y` of a substep `ℓ < top` (`ℓ = i % 2^L`, `Y = i / 2^L`). -/
def C10Idx (D : Dims) (i : ℕ) : Prop :=
  i % 2 ^ levBits D < D.top ∧ i / 2 ^ levBits D < (D.lv (i % 2 ^ levBits D + 1)).bases

instance (D : Dims) (i : ℕ) : Decidable (C10Idx D i) := by
  unfold C10Idx
  infer_instance

/-- C10 at substep `ℓ` and level-`ℓ+1` address `Y`: the kind is the stored format bit `(D.lv ℓ).shrink`; slot bits
and lane bits come from the format. -/
def C10at (fx : C10Fix) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  if (D.lv ℓ).shrink = true then
    C10sCode (fx.rcS (slotBits D ℓ) (slotBits D (ℓ + 1))) (slotBits D ℓ) (slotBits D (ℓ + 1))
      (D.lv (ℓ + 1)).laneW D u ℓ Y
  else C10rCode fx.rcR (slotBits D ℓ) (slotBits D (ℓ + 1)) (D.lv (ℓ + 1)).laneW fx.dH D u ℓ Y

noncomputable instance (fx : C10Fix) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Decidable (C10at fx D u ℓ Y) := by
  unfold C10at
  infer_instance

/-- **Family 9 (C10)** in the D5 form: an index that names no level-`ℓ+1` base accepts. -/
def C10w (fx : C10Fix) (dims : ℕ → Dims) (x u : List Bool) (i : ℕ) : Prop :=
  C10Idx (dims x.length) i →
    C10at fx (dims x.length) u (i % 2 ^ levBits (dims x.length)) (i / 2 ^ levBits (dims x.length))

noncomputable instance (fx : C10Fix) (dims : ℕ → Dims) (x u : List Bool) (i : ℕ) :
    Decidable (C10w fx dims x u i) := by
  unfold C10w
  infer_instance

/-- Number of indices of family 9 (the same count as C5, C6, C8: `2^L * maxBases`). -/
def cnt10 (dims : ℕ → Dims) (n : ℕ) : ℕ := cntBase (dims n)

theorem not_C10Idx_of_ge (D : Dims) {i : ℕ} (hi : cntBase D ≤ i) : ¬ C10Idx D i := by
  rintro ⟨hℓ, hy⟩
  have h1 := bases_le_maxBases D (show i % 2 ^ levBits D + 1 ≤ D.top by omega)
  have hp : 0 < 2 ^ levBits D := Nat.two_pow_pos _
  have h2 : maxBases D ≤ i / 2 ^ levBits D := by
    rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm]
    exact hi
  omega

theorem C10w_out (fx : C10Fix) (dims : ℕ → Dims) (x u : List Bool) {i : ℕ} (hi : cnt10 dims x.length ≤ i) :
    C10w fx dims x u i := fun h => absurd h (not_C10Idx_of_ge _ hi)

/-- **Family 9 at one substep** `ℓ < top` = C10 on codes at every address of level `ℓ + 1`. -/
theorem C10w_level (fx : C10Fix) (dims : ℕ → Dims) (x u : List Bool) {ℓ : ℕ} (hℓ : ℓ < (dims x.length).top) :
    (∀ Y < ((dims x.length).lv (ℓ + 1)).bases, C10w fx dims x u (encIdx (dims x.length) ℓ Y)) ↔
      ∀ Y < ((dims x.length).lv (ℓ + 1)).bases, C10at fx (dims x.length) u ℓ Y := by
  apply forall_congr'
  intro Y
  apply forall_congr'
  intro hY
  unfold C10w C10Idx
  rw [encIdx_mod _ (Nat.le_of_lt hℓ), encIdx_div _ (Nat.le_of_lt hℓ)]
  exact ⟨fun h => h ⟨hℓ, hY⟩, fun h _ => h⟩

/-- Family 9 at a SHRINKING substep, stage form (the step of `P1Count.stages_iff`). -/
theorem C10w_shrink_stage {a b : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
    (B : FixedBlock k demandSource demandTarget supply
      (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (fx : C10Fix)
    (hok : ShrinkCodeOK B ready (fx.rcS a b))
    (dims : ℕ → Dims) (x u : List Bool) {ℓ : ℕ} (hℓ : ℓ < (dims x.length).top)
    (hk : ((dims x.length).lv ℓ).shrink = true)
    (hsa : ((dims x.length).lv ℓ).slots = 2 ^ a) (hsb : ((dims x.length).lv (ℓ + 1)).slots = 2 ^ b)
    (g : ℕ) (hg : ((dims x.length).lv (ℓ + 1)).laneW = g)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hN' : ((dims x.length).lv (ℓ + 1)).bases = Fintype.card (X.shrinkNext B ready s).Base)
    (hN : ((dims x.length).lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch (dims x.length) u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour (dims x.length) u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset (dims x.length) u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec (dims x.length) u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout (dims x.length) u ℓ = if layoutBit B X s then 1 else 0) :
    (∀ Y < ((dims x.length).lv (ℓ + 1)).bases, C10w fx dims x u (encIdx (dims x.length) ℓ Y)) ↔
      ∀ y, PanelMatch (dims x.length) u (ℓ + 1) (addr (X.shrinkNext B ready s) y)
        (panel (X.shrinkNext B ready s) y) := by
  rw [C10w_level _ dims x u hℓ]
  unfold C10at
  simp only [hk, hg, slotBits_eq hsa, slotBits_eq hsb, eq_self_iff_true, ↓reduceIte]
  rw [hN']
  exact C10sCode_stage B ready hok g _ u ℓ X s hN hP hcol hoff hterm hlay

/-- Family 9 at a REFRESH substep, stage form. -/
theorem C10w_refresh_stage {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
    (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
    (hconn : (arcSupportGraph P.multiplicity).Connected)
    (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
    (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀) (fx : C10Fix) (hdx : fx.dH = dH)
    (hok : RefreshCodeOK P hdH hconn F hD hd fx.rcR)
    (dims : ℕ → Dims) (x u : List Bool) {ℓ : ℕ} (hℓ : ℓ < (dims x.length).top)
    (hk : ((dims x.length).lv ℓ).shrink = false)
    (hsa : ((dims x.length).lv ℓ).slots = 2 ^ a) (hsa₀ : ((dims x.length).lv (ℓ + 1)).slots = 2 ^ a₀)
    (g : ℕ) (hg : ((dims x.length).lv (ℓ + 1)).laneW = g)
    (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (hN' : ((dims x.length).lv (ℓ + 1)).bases = Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base)
    (hN : ((dims x.length).lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch (dims x.length) u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms (dims x.length) u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    (∀ Y < ((dims x.length).lv (ℓ + 1)).bases, C10w fx dims x u (encIdx (dims x.length) ℓ Y)) ↔
      ∀ y, PanelMatch (dims x.length) u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
  rw [C10w_level _ dims x u hℓ]
  unfold C10at
  simp only [hk, hg, hdx, slotBits_eq hsa, slotBits_eq hsa₀, Bool.false_eq_true, ↓reduceIte]
  rw [hN']
  exact C10rCode_stage P hdH hconn F hD hd hok g _ u ℓ X c hN hP hterm

end P1C10
