import P1P7.KernelPos
import Mathlib.Data.List.OfFn

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- Encode the half-wires of one actual state site in outgoing and incoming slot order. -/
noncomputable def halfWords {a g : ℕ} (X : State a g) (s : X.network.Site) (z : X.network.Half s) :
    List (List Bool) × List (List Bool) :=
  (List.ofFn fun k : Fin (2 ^ a) => List.ofFn (z.1 (P1P7.outEdge X s k) (P1P7.outEdge_src X s k)),
    List.ofFn fun k : Fin (2 ^ a) => List.ofFn (z.2 (P1P7.inEdge X s k) (P1P7.inEdge_dst X s k)))

private theorem slotWords_injective {E : Type*} {n : ℕ} (slot : E ≃ Fin n) (w : E → ℕ) :
    Function.Injective (fun z : (e : E) → Fin (w e) → Bool =>
      List.ofFn fun k => List.ofFn (z (slot.symm k))) := by
  intro z z' h
  funext e
  have he := congrFun (List.ofFn_injective h) (slot e)
  rw [Equiv.symm_apply_apply] at he
  exact List.ofFn_injective he

theorem halfWords_injective {a g : ℕ} (X : State a g) (s : X.network.Site) :
    Function.Injective (halfWords X s) := by
  intro z z' h
  apply Prod.ext
  · funext e he
    let w : {e : X.network.Edge // s = X.network.src e} → ℕ :=
      fun e => X.width ((e.val.1.1, e.val.2), e.val.1.2)
    have hz : (fun e : {e : X.network.Edge // s = X.network.src e} => z.1 e.val e.property) =
        (fun e : {e : X.network.Edge // s = X.network.src e} => z'.1 e.val e.property) :=
      slotWords_injective (P1P7.outFib X s) w (congrArg Prod.fst h)
    exact congrFun hz ⟨e, he⟩
  · funext e he
    let w : {e : X.network.Edge // s = X.network.dst e} → ℕ :=
      fun e => X.width ((e.val.1.1, e.val.2), e.val.1.2)
    have hz : (fun e : {e : X.network.Edge // s = X.network.dst e} => z.2 e.val e.property) =
        (fun e : {e : X.network.Edge // s = X.network.dst e} => z'.2 e.val e.property) :=
      slotWords_injective (P1P7.inFib X s) w (congrArg Prod.snd h)
    exact congrFun hz ⟨e, he⟩

private theorem words_of_widths {n : ℕ} (w : Fin n → ℕ) (ls : List (List Bool))
    (h : ls.map List.length = List.ofFn w) :
    ∃ words : (k : Fin n) → Fin (w k) → Bool, (List.ofFn fun k => List.ofFn (words k)) = ls := by
  have hl : ls.length = n := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length h
  let row (k : Fin n) := ls[k.val]'(hl.symm ▸ k.isLt)
  have hr (k : Fin n) : (row k).length = w k := by
    have hh := List.getElem_of_eq h (i := k.val)
    have hi : k.val < (ls.map List.length).length := by simp only [List.length_map, hl]; exact k.isLt
    simpa only [List.getElem_map, List.getElem_ofFn] using hh hi
  let words (k : Fin n) (i : Fin (w k)) := (row k)[i.val]'((hr k).symm ▸ i.isLt)
  refine ⟨words, List.ext_getElem (by rw [List.length_ofFn, hl]) ?_⟩
  intro k hk hk'
  simp only [List.getElem_ofFn]
  let j : Fin n := ⟨k, hl ▸ hk'⟩
  change List.ofFn (words j) = row j
  apply List.ext_getElem
  · exact List.length_ofFn.trans (hr j).symm
  · intro i hi hi'
    simp only [List.getElem_ofFn, words]

private theorem slotWords_of_widths {E : Type*} {n : ℕ} (slot : E ≃ Fin n) (w : E → ℕ)
    (ls : List (List Bool)) (h : ls.map List.length = List.ofFn (fun k => w (slot.symm k))) :
    ∃ z : (e : E) → Fin (w e) → Bool, (List.ofFn fun k => List.ofFn (z (slot.symm k))) = ls := by
  obtain ⟨words, hw⟩ := words_of_widths _ ls h
  let reorder := Equiv.piCongrLeft' (fun e => Fin (w e) → Bool) slot
  refine ⟨reorder.symm words, ?_⟩
  have he : reorder (reorder.symm words) = words := reorder.apply_symm_apply words
  change (List.ofFn fun k => List.ofFn (reorder (reorder.symm words) k)) = ls
  exact he.symm ▸ hw

/-- A pair of words of the exact slot widths represents a half-assignment at the site. -/
theorem halfWords_of_widths {a g : ℕ} (X : State a g) (s : X.network.Site)
    (zs : List (List Bool) × List (List Bool))
    (ho : zs.1.map List.length = List.ofFn (fun k : Fin (2 ^ a) => X.width ((s.1, k), s.2)))
    (hi : zs.2.map List.length = List.ofFn (fun k : Fin (2 ^ a) =>
      let e := P1P7.inEdge X s k; X.width ((e.1.1, e.2), e.1.2))) :
    ∃ z : X.network.Half s, halfWords X s z = zs := by
  let outW (e : {e : X.network.Edge // s = X.network.src e}) := X.width ((e.val.1.1, e.val.2), e.val.1.2)
  let inW (e : {e : X.network.Edge // s = X.network.dst e}) := X.width ((e.val.1.1, e.val.2), e.val.1.2)
  obtain ⟨outs, hout⟩ := slotWords_of_widths (P1P7.outFib X s) outW zs.1 ho
  obtain ⟨ins, hin⟩ := slotWords_of_widths (P1P7.inFib X s) inW zs.2 hi
  exact ⟨(fun e he => outs ⟨e, he⟩, fun e he => ins ⟨e, he⟩), Prod.ext hout hin⟩

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.halfWords_injective
#print axioms P1SolCone.SolCone.halfWords_of_widths
