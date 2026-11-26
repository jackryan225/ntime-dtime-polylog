import P1SolC10K.Sections

namespace P1SolC10K.Sol

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1P7 P1ChkFinal P1Int.P11

private theorem forallIndexEquiv {n : ℕ} {α : Type*} (e : Fin n ≃ α) (P : ℕ → Prop) :
    (∀ i < n, P i) ↔ ∀ x, P (e.symm x).val := by
  constructor
  · exact fun h x => h _ (e.symm x).isLt
  · intro h i hi
    simpa only [e.symm_apply_apply] using h (e ⟨i, hi⟩)

/-- A panel at each base covers all six slot arrays and the entire outgoing-wire width array. -/
theorem panelSections {D : Dims} {w : List Bool} {ℓ a g : ℕ} (X : State a g)
    (fit : PanelFits D (D.lv ℓ) X) (extra : StepRecords D (D.lv ℓ)) :
    (∀ y, PanelMatch D w ℓ (addr X y) (panel X y)) ↔
      ∀ m : Mem, panelKind m = true → ReadsSection D w ℓ (levelRecordsOfState X fit extra) m := by
  let A (m : Mem) (i : ℕ) : Prop :=
    readField D w (secLev ℓ m) i = (levelRecordsOfState X fit extra).code m i
  let slot (y : X.Base) (j : Fin (2 ^ a)) := (fit.baseSlot.symm (y, j)).val
  let wire (y : X.Base) (l : BitWord g) (j : Fin (2 ^ a)) := (fit.arc.symm ((y, l), j)).val
  have point (y : X.Base) : PanelMatch D w ℓ (addr X y) (panel X y) ↔
      ∀ j : Fin (2 ^ a), A .outAddr (slot y j) ∧ A .outDisp (slot y j) ∧ A .outFar (slot y j) ∧
        A .inAddr (slot y j) ∧ A .inDisp (slot y j) ∧ A .inFar (slot y j) ∧
        ∀ l : BitWord g, A .width (wire y l j) := by
    unfold PanelMatch
    apply forall_congr'
    intro j
    have widthAt (l : BitWord g) :
        (levelRecordsOfState X fit extra).code .width (wire y l j) = X.width ((y, j), l) := by
      let e : X.network.Edge := ((y, l), j)
      change finValue fit.wireWidth (fit.arc.symm e).val = _
      rw [finValue_fin]
      change X.width (((fit.arc (fit.arc.symm e)).1.1, (fit.arc (fit.arc.symm e)).2),
        (fit.arc (fit.arc.symm e)).1.2) = _
      rw [fit.arc.apply_symm_apply e]
    simp only [A, widthAt]
    simp only [slot, wire, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, panel, outNbr, inNbr, outFar, inFar,
      outWidths, addr, bwNum] <;> rfl
  constructor
  · intro hm m hk
    have hp (y : X.Base) := (point y).1 (hm y)
    cases m with
    | layout | colour | offset | energy | terms => cases hk
    | outAddr => exact (forallIndexEquiv fit.baseSlot (A .outAddr)).2 (fun q => (hp q.1 q.2).1)
    | outDisp => exact (forallIndexEquiv fit.baseSlot (A .outDisp)).2 (fun q => (hp q.1 q.2).2.1)
    | outFar => exact (forallIndexEquiv fit.baseSlot (A .outFar)).2 (fun q => (hp q.1 q.2).2.2.1)
    | inAddr => exact (forallIndexEquiv fit.baseSlot (A .inAddr)).2 (fun q => (hp q.1 q.2).2.2.2.1)
    | inDisp => exact (forallIndexEquiv fit.baseSlot (A .inDisp)).2 (fun q => (hp q.1 q.2).2.2.2.2.1)
    | inFar => exact (forallIndexEquiv fit.baseSlot (A .inFar)).2 (fun q => (hp q.1 q.2).2.2.2.2.2.1)
    | width =>
      exact (forallIndexEquiv fit.arc (A .width)).2 (fun e => (hp e.1.1 e.2).2.2.2.2.2.2 e.1.2)
  · intro h y
    apply (point y).2
    intro j
    have hs (m : Mem) (hk : panelKind m = true)
        (hc : (D.lv ℓ).count m = (D.lv ℓ).bases * (D.lv ℓ).slots) :
        A m (slot y j) := h m hk _ (hc.symm ▸ (fit.baseSlot.symm (y, j)).isLt)
    exact ⟨hs .outAddr rfl rfl, hs .outDisp rfl rfl, hs .outFar rfl rfl, hs .inAddr rfl rfl,
      hs .inDisp rfl rfl, hs .inFar rfl rfl, fun l => h .width rfl _ (fit.arc.symm ((y, l), j)).isLt⟩

end P1SolC10K.Sol
