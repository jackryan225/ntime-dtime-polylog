import P1Net.ContractProofTables

/-! Reading and reconstructing physical payloads, including twins and padding. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

theorem word_eq_of_width_zero {n : ℕ} (hn : n = 0) (x y : Fin n → Bool) : x = y := by
  subst n
  exact Subsingleton.elim _ _

theorem padded_injective {n W : ℕ} (hn : n ≤ W) : Function.Injective (@asWord W n) := by
  intro x y he
  funext i
  have h := congrFun he ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩
  simpa only [asWord, dif_pos i.isLt] using h

theorem read_after_pad {n W : ℕ} (hn : n ≤ W) (x : Fin n → Bool) :
    asWord n (asWord W x) = x := by
  funext i
  rw [asWord_apply_lt _ _ _ (lt_of_lt_of_le i.isLt hn), asWord_mk _ _ _ _ i.isLt]

variable {h a : ℕ}

theorem inEdge_unmated (G : PreGraph h) (ha : 4 ≤ 2 ^ a) (w : (G.V × Fin 4) × BitWord h → ℕ)
    {v : G.V} {s : Fin 4} (hm : G.mate (v, s) = none) (l : BitWord h) :
    inEdge (G.regularize ha w) ((v, false), l) (s.castLE ha) = (((v, true), l), s.castLE ha) := by
  have ht : (G.regularize ha w).slots.base.target.symm ((v, false), s.castLE ha) =
      ((v, true), s.castLE ha) := by
    rw [Equiv.symm_apply_eq]
    change ((v, false), s.castLE ha) = G.slotMap ha ((v, true), s.castLE ha)
    simp only [PreGraph.slotMap, PreGraph.slot4_castLE, hm, Bool.not_true]
  unfold inEdge
  simp only [ht]
  change (((v, true), l - G.displacement ((v, true), s.castLE ha)), s.castLE ha) = _
  simp only [PreGraph.displacement, PreGraph.slot4_castLE, hm, sub_zero]

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)

theorem slotIn_unmated (z : Labels V B I σ ha) {v : Fin I × Loc V.K h} {s : Fin 4}
    (hm : netMate I σ (v, s) = none) (l : BitWord h) (W : ℕ) :
    slotIn V B I σ ha z v l s W = fun _ => false := by
  change asWord W (z (inEdge (rnState V B I σ ha) ((v, false), l) (s.castLE ha))) = _
  rw [inEdge_unmated (preGraph I σ) ha _ hm l]
  funext i
  apply asWord_apply_ge
  change ¬ (i : ℕ) < (rnState V B I σ ha).width (((v, true), s.castLE ha), l)
  rw [PreGraph.regularize_width_twin]
  exact Nat.not_lt_zero _

theorem slotOut_unmated (z : Labels V B I σ ha) {v : Fin I × Loc V.K h} {s : Fin 4}
    (hm : netMate I σ (v, s) = none) (l : BitWord h) (W : ℕ) :
    slotOut V B I σ ha z v l s W = fun _ => false := by
  funext i
  change asWord W (z (((v, false), l), s.castLE ha)) i = false
  apply asWord_apply_ge
  change ¬ (i : ℕ) < (rnState V B I σ ha).width (((v, false), s.castLE ha), l)
  rw [PreGraph.regularize_width]
  simp only [netWidth, hm, ↓reduceIte, Nat.not_lt_zero, not_false_eq_true]

abbrev widthAt (v : Fin I × Loc V.K h) (s : Fin 4) :=
  baseWidth (strWidth V B) (strWidth V B) (tupWidth V B) v.2 s

/-- Equality on the outgoing words at their nominal widths determines the complete labelling. -/
theorem labels_ext {z z' : Labels V B I σ ha}
    (he : ∀ v l s, slotOut V B I σ ha z v l s (widthAt V B I v s) =
      slotOut V B I σ ha z' v l s (widthAt V B I v s)) : z = z' := by
  funext e
  obtain ⟨⟨⟨v, twin⟩, l⟩, r⟩ := e
  cases twin with
  | true =>
    apply word_eq_of_width_zero
    exact (preGraph I σ).regularize_width_twin ha _ v r l
  | false =>
    cases hs : PreGraph.slot4 r with
    | none =>
      apply word_eq_of_width_zero
      change (preGraph I σ).padWidth _ (((v, false), r), l) = 0
      simp only [PreGraph.padWidth, hs]
    | some s =>
      have hr : s.castLE ha = r := PreGraph.slot4_eq_some ha hs
      subst r
      have hw : (rnState V B I σ ha).width (((v, false), s.castLE ha), l) ≤ widthAt V B I v s := by
        rw [PreGraph.regularize_width]
        unfold netWidth
        split <;> first | exact Nat.zero_le _ | exact le_rfl
      exact padded_injective hw (he v l s)

/-- Pack prescribed outgoing words into the actual directed edges. -/
noncomputable def packSlots
    (out : (v : Fin I × Loc V.K h) → BitWord h → (s : Fin 4) → Fin (widthAt V B I v s) → Bool) :
    Labels V B I σ ha :=
  fun e => if e.1.1.2 then fun _ => false else
    match PreGraph.slot4 e.2 with
    | none => fun _ => false
    | some s => asWord _ (out e.1.1.1 e.1.2 s)

theorem slotOut_pack_mated
    (out : (v : Fin I × Loc V.K h) → BitWord h → (s : Fin 4) → Fin (widthAt V B I v s) → Bool)
    {v : Fin I × Loc V.K h} {s : Fin 4} (hm : netMate I σ (v, s) ≠ none) (l : BitWord h) :
    slotOut V B I σ ha (packSlots V B I σ ha out) v l s (widthAt V B I v s) = out v l s := by
  simp only [slotOut, outWord_edgeAssignment, packSlots, Bool.false_eq_true, if_false, PreGraph.slot4_castLE]
  apply read_after_pad
  change widthAt V B I v s ≤ (rnState V B I σ ha).width (((v, false), s.castLE ha), l)
  rw [PreGraph.regularize_width]
  simp only [netWidth, if_neg hm, widthAt, le_refl]

end P1Net.AstraContract
