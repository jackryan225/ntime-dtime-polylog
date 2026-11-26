import P1ChkFinal.C10RcRefreshRead

/-! Correctness of the radius-one polynomial refresh program on genuine panels. -/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.SpectralGeometry
open P1P7

namespace AstraC10

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
  (x : X.Base) (j : Fin (2 ^ a))

local notation "Z" => trueFrame P hdH hconn F X c x
local notation "Y" => dyadicRefreshNext X P hdH hconn F hD hd c
local notation "child" => nb P hdH hconn F hD hd X c (x, j)

theorem refreshEnds_true (r : RefreshSlot dH (2 ^ a₀)) :
    refreshEnds P hd j r Z =
      ((codeSlot (panel Y child) (refreshSlots hd r)).1,
       (codeSlot (panel Y child) (refreshSlots hd r)).2.1) := by
  have base : Z.1 = addr X x := rfl
  rcases r with i | h | h
  · simp only [refreshEnds, externalEnd, rowAt_root, laneCount_true, codeSlot, panel,
      outNbr, inNbr, outFar, inFar, rslots_ext P hdH hconn F hD hd,
      rslotsInv_ext P hdH hconn F hD hd, rdisp_ext P hdH hconn F hD hd,
      raddr P hdH hconn F hD hd, number_residue]
  · simp only [refreshEnds, localEnd, base, codeSlot, panel, outNbr, inNbr, outFar, inFar,
      rslots_int P hdH hconn F hD hd, rslotsInv_int P hdH hconn F hD hd,
      rdisp_int P hdH hconn F hD hd, raddr P hdH hconn F hD hd, number_zero]
  · simp only [refreshEnds, localEnd, base, codeSlot, panel, outNbr, inNbr, outFar, inFar,
      rslots_pad P hdH hconn F hD hd, rslotsInv_pad P hdH hconn F hD hd,
      rdisp_pad P hdH hconn F hD hd, raddr P hdH hconn F hD hd, number_zero]

theorem refreshWidth_true (r : RefreshSlot dH (2 ^ a₀)) (l : BitWord g) :
    refreshWidth P hdH hconn F j r (Z, bwNum l) =
      (Y).width ((child, refreshSlots hd r), l) := by
  rcases r with i | h | h
  · rw [rwidth_ext P hdH hconn F hD hd X c x j i l]
    apply Finset.sum_congr rfl
    intro p _
    rw [fullLane_true, root_width] <;> rfl
  · rw [rwidth_int P hdH hconn F hD hd X c x j h l]
    have dw := funext (tieCell_true P hdH hconn F X c x l)
    have terms : (fun e : Fin (2 ^ a) × Fin dH => termAt Z (bwNum l) e.1.val e.2.val) =
        (c (x, l)).val := by
      funext e
      exact termAt_true P hdH hconn F X c x l e.1 e.2
    simp only [refreshWidth, dw, terms]
  · exact (rwidth_pad P hdH hconn F hD hd X c x j h l).symm

theorem refreshRow_true (s : Fin (2 ^ a₀)) :
    refreshRow P hd hdH hconn F j s Z = codeSlot (panel Y child) s := by
  obtain ⟨r, rfl⟩ := (refreshSlots hd).surjective s
  simp only [refreshRow, Equiv.symm_apply_apply]
  have e := refreshEnds_true P hdH hconn F hD hd X c x j r
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (refreshEnds P hd j r Z).1 = _
    exact congrArg Prod.fst e
  · change (refreshEnds P hd j r Z).2 = _
    exact congrArg Prod.snd e
  change (List.ofFn fun i : Fin (datumAt Z 0).2.length =>
      refreshWidth P hdH hconn F j r (Z, i.val)) =
    (List.ofFn fun i : Fin (2 ^ g) =>
      (Y).width ((child, refreshSlots hd r), (bitWordFinEquiv g).symm i))
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact laneCount_true P hdH hconn F X c x
  · intro i _ hi
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    simpa only [bwNum, Equiv.apply_symm_apply] using
      refreshWidth_true P hdH hconn F hD hd X c x j r ((bitWordFinEquiv g).symm ⟨i, hi⟩)

theorem panelFor_true : panelFor P hd hdH hconn F j Z = codePanel (panel Y (x, j)) := by
  apply congrArg List.ofFn
  exact funext (refreshRow_true P hdH hconn F hD hd X c x j)

end AstraC10

open AstraC10
open scoped AstraC10

/-- One binary tape program computes the child panel for every residual lane dimension. -/
theorem c10_refresh_program {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
    (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
    (hconn : (arcSupportGraph P.multiplicity).Connected)
    (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
    (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀) :
    ∃ rc : (ℕ × List (ℕ × Option RefreshDatumCode)) × ℕ → Option PanelCode, Poly rc ∧
      ∀ (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
        (x : X.Base) (j : Fin (2 ^ a)),
        rc ((addr X x, ballList (nbrAt X)
          (fun y => (refreshOld P hdH hconn F X c y).map codeRefreshDatum) (addr X x) 1), j.val) =
          some (codePanel (panel (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j))) := by
  refine ⟨refreshRc P hd hdH hconn F, poly_refreshRc P hd hdH hconn F, ?_⟩
  intro g X c x j
  change some (readAt [] (List.ofFn fun j' => panelFor P hd hdH hconn F j'
    (trueFrame P hdH hconn F X c x)) j.val) = _
  rw [readAt_ofFn, panelFor_true P hdH hconn F hD hd X c x j]

#print axioms c10_refresh_program

end P1ChkFinal
