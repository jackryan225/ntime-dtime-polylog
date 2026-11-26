import P1SolFactor.FactorSpec
import P1P5.Cover

namespace P1SolFactor.SolHalf

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression NetworkKernel
open P1Net
open scoped BigOperators Classical

noncomputable section

private theorem getD_concat {A : Type} (before row after : List A) (k : ℕ) (fallback : A)
    (hk : k < row.length) : (before ++ row ++ after).getD (before.length + k) fallback = row.getD k fallback := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, List.getElem?_append_left hk]

private theorem getD_flatten_at {A : Type} (blocks : List (List A)) (before after : List A)
    (j : Fin blocks.length) (k : ℕ) (fallback : A) (hk : k < blocks[j.val].length) :
    (before ++ blocks.flatten ++ after).getD (before.length + (blocks.take j.val).flatten.length + k) fallback =
      blocks[j.val].getD k fallback := by
  have hs : blocks = blocks.take j.val ++ blocks[j.val] :: blocks.drop (j.val + 1) := by
    simpa only [List.drop_eq_getElem_cons j.isLt] using (List.take_append_drop j.val blocks).symm
  have hflat : blocks.flatten = (blocks.take j.val).flatten ++ blocks[j.val] ++
      (blocks.drop (j.val + 1)).flatten := (congrArg List.flatten hs).trans (by
    simp only [List.flatten_append, List.flatten_cons, List.append_assoc])
  conv_lhs => rw [hflat]
  simpa only [List.length_append, List.append_assoc] using
    getD_concat (before ++ (blocks.take j.val).flatten) blocks[j.val] ((blocks.drop (j.val + 1)).flatten ++ after)
      k fallback hk

section Half

variable {a h : ℕ} (X : State a h) (u : X.network.Site)

theorem inEdge_eq_target_symm (j : Fin (2 ^ a)) :
    inEdge X u j = X.slots.actualGraph.target.symm (u, j) := by
  cases u
  rfl

theorem target_inEdge (j : Fin (2 ^ a)) : X.slots.actualGraph.target (inEdge X u j) = (u, j) := by
  exact (congrArg X.slots.actualGraph.target (inEdge_eq_target_symm X u j)).trans
    (X.slots.actualGraph.target.apply_symm_apply (u, j))

theorem slotWidth_eq_halfWidth (dir : Bool) (j : Fin (2 ^ a)) :
    slotWidth X u dir j = X.halfWidth u dir j := by
  cases dir <;> rfl

theorem card_half_exact : Fintype.card (X.network.Half u) = 2 ^ halfWidthSum X u := by
  rw [P1P5.card_half, halfWidthSum]
  simp only [slotWidth_eq_halfWidth]

/-- The full physical word at a numbered incoming or outgoing slot. -/
def slotBits (z : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) : Fin (slotWidth X u dir j) → Bool :=
  match dir with
  | false => z.1 (u, j) rfl
  | true => z.2 (inEdge X u j) (inEdge_dst X u j)

/-- The physical slot words, in slot order on the chosen side. -/
def fieldLists (z : X.network.Half u) (dir : Bool) : List (List Bool) :=
  List.ofFn fun j => List.ofFn (slotBits X u z dir j)

theorem fieldLists_lengths (z : X.network.Half u) (dir : Bool) :
    (fieldLists X u z dir).map List.length = List.ofFn (slotWidth X u dir) := by
  simp only [fieldLists, List.map_ofFn, Function.comp_def, List.length_ofFn]

theorem fieldLists_flatten_length (z : X.network.Half u) (dir : Bool) :
    (fieldLists X u z dir).flatten.length = ∑ j, slotWidth X u dir j := by
  rw [List.length_flatten, fieldLists_lengths, List.sum_ofFn]

theorem packHalf_fields (z : X.network.Half u) :
    packHalf X u z = (fieldLists X u z false).flatten ++ (fieldLists X u z true).flatten := rfl

theorem packHalf_length (z : X.network.Half u) : (packHalf X u z).length = halfWidthSum X u := by
  rw [packHalf_fields, List.length_append, fieldLists_flatten_length, fieldLists_flatten_length,
    halfWidthSum, Fintype.sum_bool]
  omega

/-- Bit position of the start of this slot in the packed word. -/
def slotStart (dir : Bool) (j : Fin (2 ^ a)) : ℕ :=
  (if dir then ∑ i, slotWidth X u false i else 0) + ((List.ofFn (slotWidth X u dir)).take j.val).sum

theorem packHalf_getD_slot (z : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a))
    (k : Fin (slotWidth X u dir j)) :
    (packHalf X u z).getD (slotStart X u dir j + k.val) false = slotBits X u z dir j k := by
  let blocks := fieldLists X u z dir
  let q : Fin blocks.length := ⟨j.val, by simpa only [blocks, fieldLists, List.length_ofFn] using j.isLt⟩
  have hq : blocks[q.val] = List.ofFn (slotBits X u z dir j) := by
    simp only [blocks, fieldLists, q, List.getElem_ofFn, Fin.eta]
  have hk : k.val < blocks[q.val].length := by rw [hq, List.length_ofFn]; exact k.isLt
  have hpos : (blocks.take q.val).flatten.length = ((List.ofFn (slotWidth X u dir)).take j.val).sum := by
    rw [List.length_flatten, List.map_take]
    change (((fieldLists X u z dir).map List.length).take j.val).sum = _
    rw [fieldLists_lengths]
  have hfield : blocks[q.val].getD k.val false = slotBits X u z dir j k := by
    rw [hq, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt), List.getElem_ofFn, Fin.eta]
  cases dir
  · have hp := getD_flatten_at blocks [] (fieldLists X u z true).flatten q k.val false hk
    rw [hpos, hfield] at hp
    simpa only [packHalf_fields, slotStart, List.nil_append, List.length_nil, Nat.zero_add, Bool.false_eq_true,
      ite_false] using hp
  · have hp := getD_flatten_at blocks (fieldLists X u z false).flatten [] q k.val false hk
    rw [hpos, hfield, fieldLists_flatten_length] at hp
    simpa only [packHalf_fields, slotStart, List.append_nil, ite_true] using hp

theorem slotBits_unpack (bits : List Bool) (dir : Bool) (j : Fin (2 ^ a)) (k : Fin (slotWidth X u dir j)) :
    slotBits X u (unpackHalf X u bits) dir j k = bits.getD (slotStart X u dir j + k.val) false := by
  cases dir
  · rfl
  · change bits.getD (slotStart X u true (X.slots.actualGraph.target (inEdge X u j)).2 + k.val) false = _
    rw [target_inEdge]

theorem slotBits_injective {y z : X.network.Half u}
    (hbits : ∀ dir j, slotBits X u y dir j = slotBits X u z dir j) : y = z := by
  apply Prod.ext
  · funext e he
    obtain ⟨v, j⟩ := e
    change u = v at he
    subst v
    exact hbits false j
  · funext e he
    let w : {e : X.network.Edge // u = X.network.dst e} := ⟨e, he⟩
    let q := P1P5.inEquiv X u w
    let readEq (f : {e : X.network.Edge // u = X.network.dst e}) : Prop :=
      y.2 f.val f.property = z.2 f.val f.property
    let w₀ : {e : X.network.Edge // u = X.network.dst e} := ⟨inEdge X u q, inEdge_dst X u q⟩
    have heq : w₀ = w := by
      calc
        w₀ = (P1P5.inEquiv X u).symm q := Subtype.ext (inEdge_eq_target_symm X u q)
        _ = w := (P1P5.inEquiv X u).symm_apply_apply w
    have hr : readEq w₀ := hbits true q
    change readEq w
    rw [← heq]
    exact hr

theorem unpackHalf_packHalf (z : X.network.Half u) : unpackHalf X u (packHalf X u z) = z := by
  apply slotBits_injective X u
  intro dir j
  funext k
  rw [slotBits_unpack, packHalf_getD_slot]

end Half

end

end P1SolFactor.SolHalf
