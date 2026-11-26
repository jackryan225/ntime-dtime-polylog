import P1SolFactor.WordViews
import P1SolFactor.RoutedWidths

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open scoped Classical

section Rectangular

variable {A : Type} {rows width : ℕ}

/-- Reading one row of a rectangular word is the corresponding contiguous slice. -/
theorem ofFn_slice_row (word : Fin (rows * width) → A) (row : Fin rows) :
    ((List.ofFn word).drop (row.val * width)).take width =
      List.ofFn (fun i : Fin width => word (finProdFinEquiv (row, i))) := by
  have hfit : width ≤ rows * width - row.val * width := by
    have h : (row.val + 1) * width ≤ rows * width := Nat.mul_le_mul_right width row.isLt
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_ofFn, Nat.min_eq_left hfit]
  · intro i hi hj
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
    apply congrArg word
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring

end Rectangular

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B I : ℕ) [NeZero I] {h a : ℕ}
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)

theorem segment_ofFn_slice (c : Ext V.K) (word : Fin (tupWidth V B) → Bool) :
    ((List.ofFn word).drop ((extIdx V.K c).val * strWidth V B)).take (strWidth V B) =
      List.ofFn (segment V B c word) :=
  ofFn_slice_row word (extIdx V.K c)

local notation "X" => rnState V B I σ ha
local notation "Wt" => tupWidth V B

theorem path_tuple_word (ι : Fin I) (c : Ext V.K) (lane : BitWord h)
    (z : (X).network.Half (((ι, .tabP c), false), lane)) :
    let u : (X).network.Site := (((ι, Loc.tabP c), false), lane)
    let j := (0 : Fin 4).castLE ha
    fieldBits X u z true j = List.ofFn (inWord X u z j Wt) := by
  intro u j
  have hw := path_tuple_slot_width V B I σ ha ι c lane
  change slotWidth X u true j = Wt at hw
  rw [← wordAtWidth_in]
  unfold fieldBits
  rw [← hw, wordAtWidth_ofFn, asWord_self]

theorem path_tuple_segment (ι : Fin I) (c : Ext V.K) (lane : BitWord h)
    (z : (X).network.Half (((ι, .tabP c), false), lane)) :
    let u : (X).network.Site := (((ι, Loc.tabP c), false), lane)
    let j := (0 : Fin 4).castLE ha
    ((fieldBits X u z true j).drop ((extIdx V.K c).val * strWidth V B)).take (strWidth V B) =
      List.ofFn (segment V B c (inWord X u z j Wt)) := by
  intro u j
  rw [show fieldBits X u z true j = _ from path_tuple_word V B I σ ha ι c lane z]
  exact segment_ofFn_slice V B c _

end RoutedSite

end P1SolFactor.SolHalf
