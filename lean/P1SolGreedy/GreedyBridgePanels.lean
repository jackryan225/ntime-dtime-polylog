import P1SolGreedy.GreedyBridgeSections

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1Int.P11 P1Int.SolTrueRecords
open P1P7 P1ChkFinal

theorem panel_of_reads {D : Dims} {u : List Bool} {ℓ a g : ℕ} (X : State a g)
    (fit : PanelFits D (D.lv ℓ) X) (extra : StepRecords D (D.lv ℓ))
    (hread : ∀ m : Mem, panelKind m = true →
      ReadsKind D u ℓ (levelRecordsOfState X fit extra) m) :
    ∀ y : X.Base, PanelMatch D u ℓ (addr X y) (panel X y) := by
  intro y k
  let j := fit.baseSlot.symm (y, k)
  have hslot (m : Mem) (hm : panelKind m = true)
      (hc : (D.lv ℓ).count m = (D.lv ℓ).bases * (D.lv ℓ).slots) :
      readField D u (secLev ℓ m) (addr X y * (D.lv ℓ).slots + k.val) =
        (levelRecordsOfState X fit extra).code m j.val :=
    hread m hm j.val (hc.symm ▸ j.isLt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun lane => ?_⟩
  · simpa only [j, rdOutAddr, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.outNbr, addr] using hslot .outAddr rfl rfl
  · simpa only [j, rdOutDisp, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.outNbr, bwNum] using hslot .outDisp rfl rfl
  · simpa only [j, rdOutFar, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.outFar] using hslot .outFar rfl rfl
  · simpa only [j, rdInAddr, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.inNbr, addr] using hslot .inAddr rfl rfl
  · simpa only [j, rdInDisp, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.inNbr, bwNum] using hslot .inDisp rfl rfl
  · simpa only [j, rdInFar, LevelRecords.code, finValue_fin, levelRecordsOfState,
      Equiv.apply_symm_apply, P1P7.panel, P1P7.inFar] using hslot .inFar rfl rfl
  · let e : X.network.Edge := ((y, lane), k)
    have hw := hread .width rfl (fit.arc.symm e).val (fit.arc.symm e).isLt
    change readField D u (secLev ℓ .width)
      (((X.baseIndex y).val * (D.lv ℓ).lanes + (bitWordFinEquiv g lane).val) *
        (D.lv ℓ).slots + k.val) = X.width ((y, k), lane)
    rw [← fit.arc_symm_val y lane k]
    apply hw.trans
    have harc := fit.arc.apply_symm_apply e
    simp only [LevelRecords.code, finValue_fin, levelRecordsOfState, PanelFits.wireWidth]
    rw [harc]

theorem panel_reads_transfer {D : Dims} {u : List Bool} {ℓ a g : ℕ} (X : State a g)
    (fit : PanelFits D (D.lv ℓ) X) (p q : StepRecords D (D.lv ℓ))
    (h : ∀ m : Mem, panelKind m = true → ReadsKind D u ℓ (levelRecordsOfState X fit p) m) :
    ∀ m : Mem, panelKind m = true → ReadsKind D u ℓ (levelRecordsOfState X fit q) m := by
  intro m hm
  cases m <;> first | exact h _ rfl | contradiction

theorem fieldValue_exact {w v : ℕ} : (fieldValue w v).val = v ↔ v < 2 ^ w :=
  ⟨fun h => h ▸ (fieldValue w v).isLt, fieldValue_val⟩

private theorem base_at_number {a g : ℕ} (X : State a g) (f : X.Base → ℕ) (y : X.Base) :
    baseValue X f (addr X y) = f y := by
  unfold baseValue addr
  rw [dite_eq_left (X.baseIndex y).isLt]
  exact congrArg f (X.baseIndex.symm_apply_apply y)

theorem shrink_energy_exact_iff {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (D : Dims) (ℓ : ℕ) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (s : X.ShrinkSelection Bt.shrink) (y : X.Base) (l : Bool) (hy : addr X y < (D.lv ℓ).bases) :
    let j : Fin ((D.lv ℓ).bases * 2) :=
      ⟨addr X y * 2 + P1ChkGreedy.eCode l, idx_lt hy (by cases l <;> decide)⟩
    ((panelAt Bt κ hκ D ℓ (.shrink i rfl X) s).energy j).val =
        P1ChkGreedy.truePrefix X (P1ChkGreedy.termW Bt.shrink X s) y l ↔
      P1ChkGreedy.truePrefix X (P1ChkGreedy.termW Bt.shrink X s) y l < 2 ^ D.bigW := by
  have hc : P1ChkGreedy.eCode l < 2 := by cases l <;> decide
  have hbool : (P1ChkGreedy.eCode l == 0) = l := by cases l <;> rfl
  dsimp only [panelAt]
  rw [idx_mod hc, idx_div hc, hbool, base_at_number]
  exact fieldValue_exact

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.panel_of_reads
#print axioms P1SolGreedy.SolBridge.shrink_energy_exact_iff
