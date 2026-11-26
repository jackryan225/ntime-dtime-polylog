import OAI.Computability.VPVNP.CompressionSchedule

/-!
# P1Int.Expander: every compression schedule has expander degree at least 2 (owner: copy B)

Request of G3-chief (board 09:29Z, for P11 and lane net's `stateNet`, which needs `4 ≤ 2^(S.degreeExponent 0)`).
OpenAI's `BlockSchedule` gives only `degreeExponent 0 = expanderExponent + 1`. We prove
`1 ≤ S.expanderExponent` for EVERY schedule `S` (so also for the existential schedule of
`Compression.exists_iterated_compression`):
* the last shrinking substep satisfies `ShrinkMotif.Ready`, whose degree budget
  `d · pieceCount · Σ_{4 types} subdivisions ≤ d'` gives `4 ≤ 2^(last degree exponent)` (`four_le_portOrder`);
* the port graph is connected (OpenAI's `SpectralPortBound.connected_and_pos`);
* a connected graph of degree `2^0 = 1` has at most two vertices (`not_connected_of_degree_one`).
-/

namespace P1Int

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry

/-- A graph with one port per vertex on at least three vertices is not connected: the component of a
vertex `u` is `{u, w u}`, where `w u` is the end of its single arc. -/
theorem not_connected_of_degree_one {D b : ℕ} (hD : 3 ≤ D) (hb : b = 1) (G : RegularArcGraph (Fin D) b) :
    ¬ (arcSupportGraph G.multiplicity).Connected := by
  subst hb
  intro hconn
  classical
  let w : Fin D → Fin D := fun u => (G.reverse (u, 0)).1
  have hw : ∀ u, w (w u) = u := by
    intro u
    have h1 : G.reverse (u, 0) = (w u, 0) := Prod.ext rfl (Subsingleton.elim _ _)
    have h2 := G.involutive (u, 0)
    rw [h1] at h2
    show (G.reverse (w u, 0)).1 = u
    rw [h2]
  have hadj : ∀ u v, (arcSupportGraph G.multiplicity).Adj u v → v = w u := by
    intro u v huv
    rw [arcSupportGraph_adj _ G.multiplicity_symmetric] at huv
    obtain ⟨k, hk⟩ := (G.multiplicity_pos_iff u v).mp huv.2
    rw [← hk, Subsingleton.elim k 0]
  let u0 : Fin D := ⟨0, by omega⟩
  have hclosed : ∀ x, (arcSupportGraph G.multiplicity).Reachable u0 x → x = u0 ∨ x = w u0 := by
    intro x hx
    rw [SimpleGraph.reachable_iff_reflTransGen] at hx
    induction hx with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
      rcases ih with h | h
      · subst h
        exact Or.inr (hadj _ _ hstep)
      · subst h
        exact Or.inl ((hadj _ _ hstep).trans (hw u0))
  obtain ⟨x, hx1, hx2⟩ : ∃ x : Fin D, x ≠ u0 ∧ x ≠ w u0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin D)) ⊆ {u0, w u0} := fun x _ => by
      by_cases h : x = u0
      · simp [h]
      · simp [hcon x h]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have h2 : ({u0, w u0} : Finset (Fin D)).card ≤ 2 := Finset.card_le_two
    omega
  rcases hclosed x (hconn.preconnected u0 x) with h | h
  · exact hx1 h
  · exact hx2 h

/-- The port graph of every schedule has at least four vertices (degree budget of the last shrinking
substep). -/
theorem four_le_portOrder {k : Type*} [Field k] (S : BlockSchedule k) :
    4 ≤ 2 ^ S.degreeExponent (Fin.last S.steps) := by
  obtain ⟨n, hn⟩ : ∃ n, S.steps = n + 1 := ⟨S.steps - 1, by have := S.steps_pos; omega⟩
  let i : Fin S.steps := ⟨n, by omega⟩
  have hr := S.shrink i
  have hsucc : i.succ = Fin.last S.steps := Fin.ext (by simp [i, hn])
  rw [hsucc] at hr
  have hbudget := hr.degree_budget
  have hsum : 4 ≤ ∑ e : Fin 4, ShrinkMotif.subdivisions (2 ^ S.degreeExponent i.castSucc)
      (2 * 2 ^ S.degreeExponent i.castSucc + 1) (2 ^ S.degreeExponent (Fin.last S.steps)) e := by
    calc 4 = ∑ _e : Fin 4, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun e _ => Nat.succ_le_of_lt (hr.count_pos e))
  have hd : 1 ≤ 2 ^ S.degreeExponent i.castSucc := Nat.one_le_two_pow
  have hpiece : 1 ≤ PackingData.pieceCount (2 ^ S.degreeExponent i.castSucc)
      (2 * 2 ^ S.degreeExponent i.castSucc + 1) := by
    unfold PackingData.pieceCount
    have h8 : 8 ≤ 2 ^ (2 * 2 ^ S.degreeExponent i.castSucc + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * 2 ^ S.degreeExponent i.castSucc + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 8 ≤ 2 ^ (2 * 2 ^ S.degreeExponent i.castSucc + 1) * 2 ^ S.degreeExponent i.castSucc :=
      le_trans h8 (Nat.le_mul_of_pos_right _ (by omega))
    omega
  calc 4 = 1 * 1 * 4 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hd hpiece) hsum
    _ ≤ _ := hbudget

/-- **For P11 and lane net.** Every compression schedule has expander exponent at least one. -/
theorem expanderExponent_pos {k : Type*} [Field k] (S : BlockSchedule k) : 1 ≤ S.expanderExponent := by
  by_contra h0
  have he : S.expanderExponent = 0 := by omega
  have hD := four_le_portOrder S
  have hconn := (Refresh.SpectralPortBound.connected_and_pos S.port_bound S.port_order).1
  exact not_connected_of_degree_one (by omega) (by rw [he]; rfl) S.graph hconn

/-- The form lane net uses: the initial (= restored) degree is at least four. -/
theorem four_le_baseDegree {k : Type*} [Field k] (S : BlockSchedule k) :
    4 ≤ 2 ^ S.degreeExponent 0 := by
  rw [S.initial, pow_succ]
  have h := Nat.one_le_two_pow (n := S.expanderExponent)
  have h1 := expanderExponent_pos S
  have h2 : 2 ≤ 2 ^ S.expanderExponent := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ S.expanderExponent := Nat.pow_le_pow_right (by norm_num) h1
  omega

end P1Int
