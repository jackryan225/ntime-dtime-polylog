import P1Int.WLinkProof
import P1SolC10K.InitialNode

namespace P1SolC10K.Sol

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Int.P11 P1Int.SolTrueRecords
open private levelFrom levelFrom_head levelFrom_tail from P1Int.WLinkProof

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

def headRecord (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) (c : p.step.Choice) (fit : PanelFits D (D.lv ℓ) X) :
    LevelRecords D (D.lv ℓ) :=
  let v := panelAt Bt κ hκ D ℓ o c
  levelRecordsOfState X fit ⟨v.layout, v.colour, v.offset, v.energy, tableAt Bt κ hκ D ℓ o c⟩

def branchRecord (D : Dims) {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X)
    (o : PassOrigins Bt κ hκ E) (c : E.Choices) (start : ℕ) (f : ExecFits D E start)
    (inj : TablesInjective D E start (tableTree Bt κ hκ D E o start))
    (j : Fin (D.top + 1)) (hj : start ≤ j.val) : LevelRecords D (D.lv j.val) :=
  levelFrom E (mkPanels D E start f (panelTree Bt κ hκ D E o start))
    (mkTerms D E start f (tableTree Bt κ hκ D E o start) inj) c j hj

section More

variable {D : Dims} {a g a' g' b n : ℕ} {X : State a g}
  {p : StatePass F X a' g'} {tail : ∀ s, StateExecution F b n (p.next s)}
  (o : PassOrigins Bt κ hκ (.more p tail)) (c : (StateExecution.more p tail).Choices) (start : ℕ)
  (f : ExecFits D (.more p tail) start)
  (inj : TablesInjective D (.more p tail) start (tableTree Bt κ hκ D (.more p tail) o start))

theorem branchRecordHead :
    branchRecord Bt κ hκ D (.more p tail) o c start f inj ⟨start, Nat.lt_succ_of_lt f.1⟩ le_rfl =
      headRecord Bt κ hκ D start o.1 c.1 f.2.1 := by
  let P := mkPanels D (.more p tail) start f (panelTree Bt κ hκ D (.more p tail) o start)
  let T := mkTerms D (.more p tail) start f (tableTree Bt κ hκ D (.more p tail) o start) inj
  exact levelFrom_head (p := p) (tail := tail) P T c

theorem branchRecordTail (j : Fin (D.top + 1)) (hj : start + 1 ≤ j.val) :
    branchRecord Bt κ hκ D (.more p tail) o c start f inj j (Nat.le_of_succ_le hj) =
      branchRecord Bt κ hκ D (tail c.1) (o.2 c.1) c.2 (start + 1) (f.2.2 c.1) (inj.2 c.1) j hj := by
  let P := mkPanels D (.more p tail) start f (panelTree Bt κ hκ D (.more p tail) o start)
  let T := mkTerms D (.more p tail) start f (tableTree Bt κ hκ D (.more p tail) o start) inj
  exact levelFrom_tail (p := p) (tail := tail) P T c j hj

end More

theorem branchRecordStart {D : Dims} {a g b n start : ℕ} {X : State a g} (E : StateExecution F b n X)
    (o : PassOrigins Bt κ hκ E) (c : E.Choices) (f : ExecFits D E start)
    (inj : TablesInjective D E start (tableTree Bt κ hκ D E o start)) (hs : start ≤ D.top) :
    ∃ (fit : PanelFits D (D.lv start) X) (extra : StepRecords D (D.lv start)),
      branchRecord Bt κ hκ D E o c start f inj ⟨start, Nat.lt_succ_of_le hs⟩ le_rfl =
        levelRecordsOfState X fit extra := by
  let P := mkPanels D E start f (panelTree Bt κ hκ D E o start)
  let T := mkTerms D E start f (tableTree Bt κ hκ D E o start) inj
  let j : Fin (D.top + 1) := ⟨start, Nat.lt_succ_of_le hs⟩
  let terms := T.table E c j
  obtain ⟨v, hv⟩ := panelAtStart E P c hs
  refine ⟨v.fits, v.step terms, ?_⟩
  exact congrArg (fun q : IndexedPanel D start =>
    levelRecordsOfState q.state q.data.fits (q.data.step terms)) hv

end
end P1SolC10K.Sol
