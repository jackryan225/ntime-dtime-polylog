import P1Wit.WitTuple
import P1Wit.WitSiteOrder

namespace P1Wit.SolWitfill

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression

variable {D : Dims} {L : LevelDims} {a g : ℕ}

/-- The layout dimensions and width bounds needed to store a genuine state panel. -/
structure PanelFits (D : Dims) (L : LevelDims) (X : State a g) : Prop where
  bases : L.bases = Fintype.card X.Base
  lanes : L.lanes = 2 ^ g
  slots : L.slots = 2 ^ a
  addr : L.bases ≤ 2 ^ D.bigW
  disp : L.lanes ≤ 2 ^ L.laneW
  far : L.slots ≤ 2 ^ L.slotW
  width : ∀ e, X.width e < 2 ^ D.wW

/-- A branch's records in addition to its lifted state panel. -/
structure StepRecords (D : Dims) (L : LevelDims) where
  layout : Bool
  colour : Fin L.bases → Fin (2 ^ L.colW)
  offset : Fin L.bases → Fin (2 ^ L.tagW)
  energy : Fin (L.bases * 2) → Fin (2 ^ D.bigW)
  terms : Fin (L.bases * L.termKeys) → TermSlot D L

def PanelFits.baseSlot {X : State a g} (h : PanelFits D L X) :
    Fin (L.bases * L.slots) ≃ X.Base × Fin (2 ^ a) :=
  (ord L.bases L.slots).symm.trans
    (((finCongr h.bases).trans X.baseIndex.symm).prodCongr (finCongr h.slots))

/-- Decode an arc address in base, lane, outgoing-slot order. -/
noncomputable def PanelFits.arc {X : State a g} (h : PanelFits D L X) :
    Fin (L.bases * L.lanes * L.slots) ≃ X.network.Edge :=
  (ord (L.bases * L.lanes) L.slots).symm.trans
    (((ord L.bases L.lanes).symm.trans
      (((finCongr h.bases).trans X.baseIndex.symm).prodCongr
        ((finCongr h.lanes).trans (bitWordFinEquiv g).symm))).prodCongr (finCongr h.slots))

theorem PanelFits.arc_symm_val {X : State a g} (h : PanelFits D L X)
    (y : X.Base) (l : BitWord g) (k : Fin (2 ^ a)) :
    ((h.arc).symm ((y, l), k)).val =
      ((X.baseIndex y).val * L.lanes + (bitWordFinEquiv g l).val) * L.slots + k.val :=
  rfl

/-- Wire widths are stored at the source of each actual outgoing slot. -/
noncomputable def PanelFits.wireWidth {X : State a g} (h : PanelFits D L X)
    (i : Fin (L.bases * L.lanes * L.slots)) : Fin (2 ^ D.wW) :=
  let e := h.arc i
  ⟨X.width ((e.1.1, e.2), e.1.2), h.width _⟩

/-- Build the true panel from the underlying slot graph and its widths.
For an incoming slot the stored displacement is the displacement of the
outgoing arc at its source. -/
noncomputable def levelRecordsOfState (X : State a g) (h : PanelFits D L X) (S : StepRecords D L) :
    LevelRecords D L :=
  let out := fun i => X.slots.base.target (h.baseSlot i)
  let inc := fun i => X.slots.base.target.symm (h.baseSlot i)
  { layout := S.layout
    outAddr := fun i => ⟨(X.baseIndex (out i).1).val, (X.baseIndex (out i).1).isLt.trans_le
      (h.bases ▸ h.addr)⟩
    outDisp := fun i => ⟨(bitWordFinEquiv g (X.slots.displacement (h.baseSlot i))).val,
      (bitWordFinEquiv g (X.slots.displacement (h.baseSlot i))).isLt.trans_le (h.lanes ▸ h.disp)⟩
    outFar := fun i => ⟨(out i).2.val, (out i).2.isLt.trans_le (h.slots ▸ h.far)⟩
    inAddr := fun i => ⟨(X.baseIndex (inc i).1).val, (X.baseIndex (inc i).1).isLt.trans_le
      (h.bases ▸ h.addr)⟩
    inDisp := fun i => ⟨(bitWordFinEquiv g (X.slots.displacement (inc i))).val,
      (bitWordFinEquiv g (X.slots.displacement (inc i))).isLt.trans_le (h.lanes ▸ h.disp)⟩
    inFar := fun i => ⟨(inc i).2.val, (inc i).2.isLt.trans_le (h.slots ▸ h.far)⟩
    width := h.wireWidth
    colour := S.colour
    offset := S.offset
    energy := S.energy
    terms := S.terms }

/-- Payload words on an actual compressor network, reindexed in the same
base, lane, outgoing-slot order as its width fields. -/
noncomputable def payloadOfState (X : State a g) (h : PanelFits D L X) (S : StepRecords D L) :
    ((e : X.network.Edge) → X.network.Payload e) ≃
      ((i : Fin (L.bases * L.lanes * L.slots)) → Fin ((levelRecordsOfState X h S).width i).val → Bool) :=
  Equiv.piCongrLeft' (fun e => X.network.Payload e) h.arc.symm

/-- The S3 length is the compressor's total final width. -/
theorem payloadOfState_length (X : State a g) (h : PanelFits D L X) (S : StepRecords D L)
    (z : (e : X.network.Edge) → X.network.Payload e) :
    (flatten (payloadOfState X h S z)).length = X.totalWidth := by
  rw [flatten_length, widthPrefix, ← Fin.sum_univ_eq_sum_range]
  simp only [atIndex_fin]
  let arcCoords : X.network.Edge ≃ (X.Base × Fin (2 ^ a)) × BitWord g :=
    { toFun := fun e => ((e.1.1, e.2), e.1.2)
      invFun := fun e => ((e.1.1, e.2), e.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.sum_comp h.arc (fun e => X.width (arcCoords e))).trans
    (Equiv.sum_comp arcCoords X.width)

end P1Wit.SolWitfill
