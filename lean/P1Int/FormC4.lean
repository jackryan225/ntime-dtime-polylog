import P1Int.FormC4Defs

noncomputable section

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1ChkDir P1Net

namespace P1Int.P11.SolFormC4

private theorem initialPanelFits {R : Type*} [CommSemiring R] {b n e h : ℕ}
    {X : State e h} (D : Dims) (E : StateExecution R b n X)
    (P : ExecutionPanels D E 0) (c : E.Choices) : PanelFits D (D.lv 0) X := by
  cases E with
  | done => exact P.val.fits
  | more => exact (P.1.val c.1).fits

private theorem skeletonOfAgreement {K : Type} (D : Dims) (ρ : K ≃ Fin D.r) (U : List Bool)
    (W : Fields) (σ : Fin (D.I * D.N) → K → Fin 3)
    (hAgree : ∀ i < D.count secTrit, (dec D U).val D secTrit i = W.val D secTrit i)
    (hTrit : ∀ (i : Fin (D.I * D.N)) (j : K), W.trit i (ρ j) = (σ i j : ℕ)) :
    (dirP6 D ρ).sigmaS U = σ := by
  funext i j
  have hr := (ρ j).isLt
  have hi : (i : ℕ) * D.r + ρ j < D.count secTrit := by
    simpa only [Dims.count, D.kind_trit] using idx_lt i.isLt hr
  have h := hAgree _ hi
  simp only [Fields.val, D.kind_trit, idx_div hr, idx_mod hr, dec] at h
  rw [dirP6_sigmaS, h, hTrit i j, tritOfN_val, Option.getD_some]

private theorem panelAgreement {e h : ℕ} (D : Dims) (X : State e h)
    (fit : PanelFits D (D.lv 0) X) (U : List Bool) (W : Fields)
    (hFields : ∀ y : X.Base, PanelFields W 0 (X.baseIndex y) (P1P7.panel X y)) :
    (∀ y : X.Base, PanelStored D U (X.baseIndex y) (P1P7.panel X y)) ↔
    (∀ m : Mem, panelKind m = true → ∀ i < D.count (secLev 0 m),
      (dec D U).val D (secLev 0 m) i = W.val D (secLev 0 m) i) := by
  have h0 : 0 ≤ D.top := Nat.zero_le _
  constructor
  · intro hStored m hm i hi
    have hSlot (q : Fin ((D.lv 0).bases * (D.lv 0).slots)) :
        ∃ (y : X.Base) (s : Fin (2 ^ e)), (X.baseIndex y : ℕ) * (D.lv 0).slots + s = q.val := by
      let p := fit.baseSlot q
      exact ⟨p.1, p.2, congrArg Fin.val (fit.baseSlot.symm_apply_apply q)⟩
    have hWidth : ∀ j < D.count (secLev 0 .width),
        (dec D U).val D (secLev 0 .width) j = W.val D (secLev 0 .width) j := by
      intro j hj
      have hj' : j < (D.lv 0).bases * (D.lv 0).lanes * (D.lv 0).slots := by
        simpa only [D.count_secLev .width h0, LevelDims.count] using hj
      let q : Fin ((D.lv 0).bases * (D.lv 0).lanes * (D.lv 0).slots) := ⟨j, hj'⟩
      rcases he : fit.arc q with ⟨⟨y, lane⟩, s⟩
      have hidx : ((X.baseIndex y : ℕ) * (D.lv 0).lanes + bwNum lane) * (D.lv 0).slots + s = j := by
        rw [bwNum, ← fit.arc_symm_val y lane s, ← he, Equiv.symm_apply_apply]
      have hs : (s : ℕ) < (D.lv 0).slots := fit.slots.symm ▸ s.isLt
      have hl : bwNum lane < (D.lv 0).lanes := fit.lanes.symm ▸ bwNum_lt lane
      rw [← hidx]
      simp only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs,
        idx_div hl, idx_mod hl, dec]
      exact ((hStored y s).2.2.2.2.2.2 lane).trans ((hFields y s).2.2.2.2.2.2 lane).symm
    cases m <;> try contradiction
    case width => exact hWidth i hi
    all_goals
      have hi' : i < (D.lv 0).bases * (D.lv 0).slots := by
        simpa only [D.count_secLev _ h0, LevelDims.count] using hi
      obtain ⟨y, s, hidx⟩ := hSlot ⟨i, hi'⟩
      have hs : (s : ℕ) < (D.lv 0).slots := fit.slots.symm ▸ s.isLt
      change _ = i at hidx
      rw [← hidx]
      simp only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec]
      rcases hStored y s with ⟨os₁, os₂, os₃, is₁, is₂, is₃, _⟩
      rcases hFields y s with ⟨ot₁, ot₂, ot₃, it₁, it₂, it₃, _⟩
      first | exact os₁.trans ot₁.symm | exact os₂.trans ot₂.symm | exact os₃.trans ot₃.symm |
        exact is₁.trans it₁.symm | exact is₂.trans it₂.symm | exact is₃.trans it₃.symm
  · intro hAgree y s
    have hs : (s : ℕ) < (D.lv 0).slots := fit.slots.symm ▸ s.isLt
    have hy : (X.baseIndex y : ℕ) < (D.lv 0).bases := fit.bases.symm ▸ (X.baseIndex y).isLt
    have hSlot (m : Mem) (hm : panelKind m = true)
        (hc : (D.lv 0).count m = (D.lv 0).bases * (D.lv 0).slots) :
        (dec D U).val D (secLev 0 m) ((X.baseIndex y : ℕ) * (D.lv 0).slots + s) =
          W.val D (secLev 0 m) ((X.baseIndex y : ℕ) * (D.lv 0).slots + s) := by
      have hi : (X.baseIndex y : ℕ) * (D.lv 0).slots + s < D.count (secLev 0 m) := by
        rw [D.count_secLev m h0, hc]
        exact idx_lt hy hs
      exact hAgree m hm _ hi
    rcases hFields y s with ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun lane => ?_⟩
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₁]
        using hSlot .outAddr rfl rfl
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₂]
        using hSlot .outDisp rfl rfl
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₃]
        using hSlot .outFar rfl rfl
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₄]
        using hSlot .inAddr rfl rfl
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₅]
        using hSlot .inDisp rfl rfl
    · simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs, dec, e₆]
        using hSlot .inFar rfl rfl
    · have hl : bwNum lane < (D.lv 0).lanes := fit.lanes.symm ▸ bwNum_lt lane
      have hi : ((X.baseIndex y : ℕ) * (D.lv 0).lanes + bwNum lane) * (D.lv 0).slots + s <
          D.count (secLev 0 .width) := by
        rw [D.count_secLev _ h0]
        exact idx_lt (idx_lt hy hl) hs
      simpa only [Fields.val, D.kind_secLev _ h0, Fields.levVal, idx_div hs, idx_mod hs,
        idx_div hl, idx_mod hl, dec, e₇ lane] using hAgree .width rfl _ hi

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) [NeZero (fixedDims Bt V a b x d bigBias termBias).I]
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)

private theorem bridgeForTuple (τ : (toOAI V).K → ℕ) (hτ : ∀ j, (H.tape_order j : ℕ) = τ j)
    (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d)
    (hTrit : SecEq Bt κ hκ V a b x d bigBias termBias H u t secTrit) :
    c4Rhs Bt V a b x d bigBias termBias τ u ↔
      (∀ m : Mem, panelKind m = true →
        SecEq Bt κ hκ V a b x d bigBias termBias H u t (secLev 0 m)) := by
  let D := fixedDims Bt V a b x d bigBias termBias
  let U := List.ofFn u
  let W := ofTuple (fixedTR Bt κ hκ V a b x d bigBias termBias H) t
  let B := P1Wrap.Params.B (lpTime a b x.length)
  let I := P1Wrap.Params.I 1 (lpTime a b x.length)
  let h := P1Wrap.Params.h (lpTime a b x.length)
  let X := rnState (toOAI V) B I t.1 (four_le_baseDegree S)
  have hσ : (dirP6 D H.tape_order).sigmaS U = t.1 :=
    skeletonOfAgreement D H.tape_order U W t.1 hTrit (dirLink Bt κ hκ V a x _ _ _ _ H t).1
  have hn : (dirAt D τ I (2 ^ h)).sigmaS U = t.1 := by
    have ht : τ = fun j => (H.tape_order j : ℕ) := funext fun j => (hτ j).symm
    rw [ht]
    exact hσ
  have hAddr (y : X.Base) : (X.baseIndex y : ℕ) = addrL y := by
    rcases y with ⟨⟨j, l⟩, twin⟩
    exact stateNet_baseIndex_val I t.1 (four_le_baseDegree S) (strWidth (toOAI V) B)
      (strWidth (toOAI V) B) (tupWidth (toOAI V) B) j l twin
  have hFields (y : X.Base) : PanelFields W 0 (X.baseIndex y) (P1P7.panel X y) := by
    rw [hAddr]
    exact (panelLink Bt κ hκ V a x _ _ _ _ H t).2.2.2 y
  have hFits : PanelFits D (D.lv 0) X :=
    initialPanelFits D _ (H.panels t.1) t.2.1
  change (∀ y, PanelStored D U (addrL y)
    (P1P7.panel (stateNet I ((dirAt D τ I (2 ^ h)).sigmaS U) (four_le_baseDegree S)
      (strWidth (toOAI V) B) (strWidth (toOAI V) B) (tupWidth (toOAI V) B)) y)) ↔ _
  rw [hn]
  change (∀ y : X.Base, PanelStored D U (addrL y) (P1P7.panel X y)) ↔
    (∀ m : Mem, panelKind m = true → ∀ i < D.count (secLev 0 m),
      (dec D U).val D (secLev 0 m) i = W.val D (secLev 0 m) i)
  simpa only [hAddr] using panelAgreement D X hFits U W hFields

end P1Int.P11.SolFormC4

open P1Int.P11 P1Int.P11.SolFormC4
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.c4_bridge {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) [NeZero (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).I]
    (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.C4BridgeTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hd τ hτ u hDir
  constructor
  · intro hStored
    exact Exists.elim (dir_exists Bt κ hκ V a b x d bigBias termBias H hd u hDir) fun t hTrit =>
      ⟨t, hTrit, (bridgeForTuple Bt κ hκ V a b x d bigBias termBias H τ hτ u t hTrit).mp hStored⟩
  · intro h
    exact Exists.elim h fun t ht =>
      (bridgeForTuple Bt κ hκ V a b x d bigBias termBias H τ hτ u t ht.1).mpr ht.2

#print axioms P1Int.P11.c4_bridge
