import P1Net.Factors

/-!
# P4 glue, first lemmas (lane P1-lean-net, copy A)

Structural facts used to read an edge labelling `z` of the routed network `N_{x,σ}`:
* `outWord_edgeAssignment`, `inWord_edgeAssignment`: the words a site sees are the edge values.
* `inEdge_regularize_mate`: in a padded pre-network, the arc arriving at the in-slot of a mated half-edge `(v, s)`
  is the out-slot `s'` of its mate `v'`, at the lane shifted by the edge displacement.
* `inWord_mate`: hence the in-word of a mated half-edge is the out-word of its mate (both ends read one edge).
* `segment_tupleWord`, `asWord_asWord`, `encC_injective`, `encS_injective`: decoding of tuples and codes.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {a h : ℕ}

theorem outWord_edgeAssignment (X : State a h) (z : (e : X.network.Edge) → X.network.Payload e)
    (u : X.Base × BitWord h) (i : Fin (2 ^ a)) (W : ℕ) :
    outWord X u (edgeAssignment X.network.src X.network.dst z u) i W = asWord W (z (u, i)) := rfl

theorem inWord_edgeAssignment (X : State a h) (z : (e : X.network.Edge) → X.network.Payload e)
    (u : X.Base × BitWord h) (j : Fin (2 ^ a)) (W : ℕ) :
    inWord X u (edgeAssignment X.network.src X.network.dst z u) j W = asWord W (z (inEdge X u j)) := rfl

theorem bitWord_sub_eq_add {n : ℕ} (x y : BitWord n) : x - y = x + y := by
  funext j
  simp only [Pi.sub_apply, Pi.add_apply]
  exact CharTwo.sub_eq_add _ _

theorem PreGraph.displacement_mate (G : PreGraph h) (ha : 4 ≤ 2 ^ a) {v u : G.V} {i j : Fin 4}
    (hm : G.mate (v, i) = some (u, j)) (t : Bool) :
    G.displacement ((v, t), i.castLE ha) = G.disp (v, i) := by
  simp [PreGraph.displacement, PreGraph.slot4_castLE, hm]

/-- The arc arriving at the in-slot of a mated half-edge is the mate's out-slot. -/
theorem inEdge_regularize_mate (G : PreGraph h) (ha : 4 ≤ 2 ^ a) (w : (G.V × Fin 4) × BitWord h → ℕ)
    {v v' : G.V} {s s' : Fin 4} (hm : G.mate (v, s) = some (v', s')) (t : Bool) (l : BitWord h) :
    inEdge (G.regularize ha w) ((v, t), l) (s.castLE ha) =
      (((v', t), l + G.disp (v, s)), s'.castLE ha) := by
  have hm' := G.mate_symm _ _ hm
  have ht := G.regularize_target_mate ha w hm' t
  have hsymm : (G.regularize ha w).slots.base.target.symm ((v, t), s.castLE ha) = ((v', t), s'.castLE ha) := by
    rw [Equiv.symm_apply_eq]
    exact ht.symm
  unfold inEdge
  simp only [hsymm]
  rw [G.displacement_mate ha hm' t, G.disp_mate _ _ hm, bitWord_sub_eq_add]

/-- **Both ends read one edge.** The in-word of a mated half-edge is the out-word of its mate. -/
theorem inWord_regularize_mate (G : PreGraph h) (ha : 4 ≤ 2 ^ a) (w : (G.V × Fin 4) × BitWord h → ℕ)
    (z : (e : (G.regularize ha w).network.Edge) → (G.regularize ha w).network.Payload e)
    {v v' : G.V} {s s' : Fin 4} (hm : G.mate (v, s) = some (v', s')) (t : Bool) (l : BitWord h) (W : ℕ) :
    inWord (G.regularize ha w) ((v, t), l)
        (edgeAssignment (G.regularize ha w).network.src (G.regularize ha w).network.dst z ((v, t), l))
        (s.castLE ha) W =
      outWord (G.regularize ha w) ((v', t), l + G.disp (v, s))
        (edgeAssignment (G.regularize ha w).network.src (G.regularize ha w).network.dst z
          ((v', t), l + G.disp (v, s)))
        (s'.castLE ha) W := by
  rw [inWord_edgeAssignment, outWord_edgeAssignment, inEdge_regularize_mate G ha w hm t l]

/-! ## Decoding -/

theorem asWord_apply_lt (W : ℕ) {w : ℕ} (x : Fin w → Bool) (j : Fin W) (hj : (j : ℕ) < w) :
    asWord W x j = x ⟨j, hj⟩ := by
  simp [asWord, hj]

theorem asWord_mk (W : ℕ) {w : ℕ} (x : Fin w → Bool) (n : ℕ) (hn : n < W) (hj : n < w) :
    asWord W x ⟨n, hn⟩ = x ⟨n, hj⟩ := by
  simp [asWord, hj]

theorem asWord_apply_ge (W : ℕ) {w : ℕ} (x : Fin w → Bool) (j : Fin W) (hj : ¬ (j : ℕ) < w) :
    asWord W x j = false := by
  simp [asWord, hj]

theorem asWord_self {w : ℕ} (x : Fin w → Bool) : asWord w x = x := by
  funext j
  simp [asWord, j.isLt]

section Codes

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]

theorem segment_tupleWord (f : Ext V.K → Fin (strWidth V B) → Bool) (c : Ext V.K) :
    segment V B c (tupleWord V B f) = f c := by
  funext o
  simp [segment, tupleWord]

theorem tupleWord_injective : Function.Injective (tupleWord V B) := by
  intro f f' hf
  funext c
  rw [← segment_tupleWord V B f c, ← segment_tupleWord V B f' c, hf]

theorem strWidth_ge_content : B * Fintype.card V.Γ ≤ strWidth V B := by
  unfold strWidth; omega

theorem strWidth_ge_state : Fintype.card V.Q + Fintype.card V.K * B ≤ strWidth V B := by
  unfold strWidth; omega

/-- The code of block contents is injective. -/
theorem encC_injective : Function.Injective (encC V B) := by
  intro b b' hbb
  funext o
  let j : Fin (B * Fintype.card V.Γ) := finProdFinEquiv (o, Fintype.equivFin V.Γ (b o))
  have hW := strWidth_ge_content V B
  have key := congrFun hbb ⟨j, lt_of_lt_of_le j.isLt hW⟩
  unfold encC at key
  rw [asWord_mk _ _ _ _ j.isLt, asWord_mk _ _ _ _ j.isLt] at key
  simp only [Fin.eta, j, Equiv.symm_apply_apply, oneHot] at key
  simpa using key

/-- The code of states with offsets is injective. -/
theorem encS_injective {q q' : V.Q} {off off' : V.K → Fin B}
    (hqq : encS V B q off = encS V B q' off') : q = q' ∧ off = off' := by
  have hW := strWidth_ge_state V B
  constructor
  · let j : Fin (Fintype.card V.Q + Fintype.card V.K * B) := Fin.castAdd _ (Fintype.equivFin V.Q q)
    have key := congrFun hqq ⟨j, lt_of_lt_of_le j.isLt hW⟩
    unfold encS at key
    rw [asWord_mk _ _ _ _ j.isLt, asWord_mk _ _ _ _ j.isLt] at key
    simp only [Fin.eta, j, Fin.append_left, oneHot] at key
    simpa using key
  · funext k
    let j : Fin (Fintype.card V.Q + Fintype.card V.K * B) :=
      Fin.natAdd _ (finProdFinEquiv (Fintype.equivFin V.K k, off k))
    have key := congrFun hqq ⟨j, lt_of_lt_of_le j.isLt hW⟩
    unfold encS at key
    rw [asWord_mk _ _ _ _ j.isLt, asWord_mk _ _ _ _ j.isLt] at key
    simp only [Fin.eta, j, Fin.append_right, Equiv.symm_apply_apply] at key
    simpa using key

end Codes

end P1Net
