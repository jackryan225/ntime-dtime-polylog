import P1Int.WitfillLink
import P1ChkFinal.C10Bits
import P1P7.KernelPos
import OAI.Computability.VPVNP.BitSlotXor

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1ChkFinal P1P7

/-- All the outgoing, incoming and width fields of a true panel survive P6 encoding. -/
theorem panelMatch_encTuple {F : Type*} {D : Dims} {C : P1Count.CountData F} {d a g : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R t).length ≤ m)
    (ℓ : Fin (D.top + 1)) (X : State a g) (fit : PanelFits D (D.lv ℓ.val) X)
    (step : StepRecords D (D.lv ℓ.val)) (hLevel : R.level t.1 t.2.1 ℓ = levelRecordsOfState X fit step)
    (y : X.Base) :
    PanelMatch D (List.ofFn (encTuple R m t)) ℓ.val (addr X y) (panel X y) := by
  intro k
  let y' := finCongr fit.bases.symm (X.baseIndex y)
  let k' := finCongr fit.slots.symm k
  let i := ord (D.lv ℓ.val).bases (D.lv ℓ.val).slots (y', k')
  have hi : fit.baseSlot i = (y, k) := by
    simp only [PanelFits.baseSlot, i, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply]
    change (X.baseIndex.symm (finCongr fit.bases y'), finCongr fit.slots k') = (y, k)
    rw [show finCongr fit.bases y' = X.baseIndex y from Fin.ext rfl,
      show finCongr fit.slots k' = k from Fin.ext rfl, Equiv.symm_apply_apply]
  let u := enc D m (ofTuple R t) (tuplePayload R t)
  have hb : List.ofFn (encTuple R m t) = u := ofFn_encFn _ _ _ _ hm
  have hf := ofTuple_inRange R t
  have hℓ : ℓ.val ≤ D.top := by have := ℓ.isLt; omega
  rw [hb, show addr X y = y'.val from rfl, show k.val = k'.val from rfl]
  dsimp only [u]
  rw [rdOutAddr_enc D m _ _ hf hℓ y'.isLt k'.isLt,
    rdOutDisp_enc D m _ _ hf hℓ y'.isLt k'.isLt,
    rdOutFar_enc D m _ _ hf hℓ y'.isLt k'.isLt,
    rdInAddr_enc D m _ _ hf hℓ y'.isLt k'.isLt,
    rdInDisp_enc D m _ _ hf hℓ y'.isLt k'.isLt,
    rdInFar_enc D m _ _ hf hℓ y'.isLt k'.isLt]
  have hr : levelAt (R.level t.1 t.2.1) ℓ.val = (R.level t.1 t.2.1 ℓ).code := by
    funext kind idx
    unfold levelAt
    exact dite_eq_left ℓ.isLt
  have hwidth (l : BitWord g) :
      rdWidth D u ℓ.val (addr X y) (bwNum l) k.val = (panel X y).2.2.2.2 k l := by
    let l' := finCongr fit.lanes.symm (bitWordFinEquiv g l)
    let e : X.network.Edge := ((y, l), k)
    let j := (fit.arc).symm e
    change rdWidth D (enc D m (ofTuple R t) (tuplePayload R t)) ℓ.val y'.val l'.val k'.val = _
    rw [rdWidth_enc D m _ _ hf hℓ y'.isLt l'.isLt k'.isLt]
    show levelAt (R.level t.1 t.2.1) ℓ.val .width
      ((y'.val * (D.lv ℓ.val).lanes + l'.val) * (D.lv ℓ.val).slots + k'.val) = _
    rw [hr, hLevel]
    have hj : ((y'.val * (D.lv ℓ.val).lanes + l'.val) * (D.lv ℓ.val).slots + k'.val) = j.val :=
      (fit.arc_symm_val y l k).symm
    rw [hj]
    change finValue (fit.wireWidth) j.val = _
    rw [finValue_fin]
    change X.width (((fit.arc j).1.1, (fit.arc j).2), (fit.arc j).1.2) = _
    exact congrArg (fun e : X.network.Edge => X.width ((e.1.1, e.2), e.1.2))
      (fit.arc.apply_symm_apply e)
  simp only [ofTuple, hr, hLevel, LevelRecords.code]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hwidth⟩
  all_goals rw [show y'.val * (D.lv ℓ.val).slots + k'.val = i.val from rfl, finValue_fin]
  all_goals simp only [levelRecordsOfState, hi] <;> rfl

/-- Read the two slot-ordered lists of half-wire widths at any level. An incoming width
uses the width at the source lane specified by the incoming displacement. -/
def readHalfWidths (D : Dims) (u : List Bool) (ℓ : ℕ) (site : ℕ × ℕ) : List ℕ × List ℕ :=
  let slots := List.range (D.lv ℓ).slots
  let width := rdWidth D u ℓ
  let y := site.1
  let l := site.2
  (slots.map (width y l), slots.map fun k =>
    width (rdInAddr D u ℓ y k) (l ^^^ rdInDisp D u ℓ y k) (rdInFar D u ℓ y k))

private theorem map_range_eq_ofFn {A : Type*} {n : ℕ} (f : ℕ → A) (g : Fin n → A)
    (h : ∀ i : Fin n, f i.val = g i) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact h ⟨i, by simpa only [List.length_ofFn] using hj⟩

theorem readHalfWidths_eq {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a g)
    (slots : (D.lv ℓ).slots = 2 ^ a) (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (s : X.network.Site) :
    readHalfWidths D u ℓ (addr X s.1, bwNum s.2) =
      (List.ofFn fun k : Fin (2 ^ a) => X.width ((s.1, k), s.2),
        List.ofFn fun k : Fin (2 ^ a) =>
          let e := inEdge X s k
          X.width ((e.1.1, e.2), e.1.2)) := by
  unfold readHalfWidths
  rw [slots]
  apply Prod.ext
  · apply map_range_eq_ofFn
    intro k
    exact (hPanel s.1 k).2.2.2.2.2.2 s.2
  · apply map_range_eq_ofFn
    intro k
    let src := X.slots.base.target.symm (s.1, k)
    let d := X.slots.displacement src
    have h := hPanel s.1 k
    have xorEq : bwNum (s.2 - d) = bwNum s.2 ^^^ bwNum d := by
      have hneg : -d = d := funext fun i => ZMod.neg_eq_self_mod_two (d i)
      rw [sub_eq_add_neg, hneg]
      exact bitWordFinEquiv_add_val s.2 d
    change rdWidth D u ℓ (rdInAddr D u ℓ (addr X s.1) k.val)
      (bwNum s.2 ^^^ rdInDisp D u ℓ (addr X s.1) k.val)
      (rdInFar D u ℓ (addr X s.1) k.val) = X.width (src, s.2 - d)
    rw [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1]
    change rdWidth D u ℓ (addr X src.1) (bwNum s.2 ^^^ bwNum d) src.2.val = _
    rw [← xorEq]
    exact (hPanel src.1 src.2).2.2.2.2.2.2 (s.2 - d)

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.panelMatch_encTuple
#print axioms P1SolCone.SolCone.readHalfWidths_eq
