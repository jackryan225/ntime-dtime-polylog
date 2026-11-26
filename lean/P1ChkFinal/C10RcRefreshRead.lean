import P1ChkFinal.C10RcRefresh
import OAI.Computability.VPVNP.CompressorRecordRefreshOldWidths
import OAI.Computability.VPVNP.BitSlotXor

/-! Interpretation of the radius-one list and the incoming demand addresses. -/

namespace P1ChkFinal.AstraC10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.SpectralGeometry
open P1P7

noncomputable section

theorem readAt_secondBlock {T : Type} (d root : T) {n : ℕ} (o i : Fin n → T) (s : Fin n) :
    readAt d (root :: (List.ofFn o ++ List.ofFn i)) (1 + (n + s.val)) = i s := by
  rw [Nat.add_comm 1]
  change readAt d (List.ofFn o ++ List.ofFn i) (n + s.val) = i s
  rw [readAt, List.getElem?_append_right (by simp)]
  simp [List.getElem?_ofFn, s.isLt]

@[simp] theorem number_zero {n : ℕ} : bwNum (0 : BitWord n) = 0 := by
  simpa only [zero_add, Nat.xor_self, bwNum] using bitWordFinEquiv_add_val (0 : BitWord n) 0

theorem number_sub {n : ℕ} (v d : BitWord n) :
    bwNum (v - d) = bwNum v ^^^ bwNum d := by
  have hd : -d = d := funext fun i => CharTwo.neg_eq (d i)
  rw [sub_eq_add_neg, hd]
  exact bitWordFinEquiv_add_val _ _

def oldLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) : BitWord (a + g) :=
  (splitBitWord a g).symm ((bitWordFinEquiv a).symm p, l)

theorem number_oldLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) :
    bwNum (oldLane p l) = p.val * 2 ^ g + bwNum l := by
  unfold bwNum oldLane
  rw [splitBitWord_number, AddEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem number_residue {a g : ℕ} (w : BitWord (a + g)) :
    bwNum w % 2 ^ g = bwNum (splitBitWord a g w).2 := by
  unfold bwNum
  rw [splitBitWord_number a g w, Nat.mul_add_mod_of_lt (bitWordFinEquiv g _).isLt]

/-- Undoing the two component translations is subtraction of the full old displacement. -/
theorem incomingLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) (d : BitWord (a + g)) :
    (splitBitWord a g).symm ((bitWordFinEquiv a).symm
      (((bitWordFinEquiv a).symm.trans ((Equiv.addRight (splitBitWord a g d).1).trans
        (bitWordFinEquiv a))).symm p), l - (splitBitWord a g d).2) =
      oldLane p l - d := by
  apply (splitBitWord a g).injective
  simp only [oldLane, map_sub, AddEquiv.apply_symm_apply]
  apply Prod.ext
  · change (bitWordFinEquiv a).symm ((bitWordFinEquiv a)
          (((bitWordFinEquiv a).symm p) + -(splitBitWord a g d).1)) =
        (bitWordFinEquiv a).symm p - (splitBitWord a g d).1
    rw [Equiv.symm_apply_apply, sub_eq_add_neg]
  · rfl

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
variable (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base)

/-- The arguments of the fixed program on genuine data. -/
def trueFrame : RefreshFrame :=
  (addr X x, ballList (nbrAt X)
    (fun y => (refreshOld P hdH hconn F X c y).map codeRefreshDatum) (addr X x) 1)

def trueDatum (y : X.Base) : RefreshDatumCode :=
  codeRefreshDatum (a := a) (g := g) (dH := dH) (panel X y, fun l => (c (y, l)).val)

local notation "Z" => trueFrame P hdH hconn F X c x
local notation "dataOf" => trueDatum P hdH hconn F X c

theorem trueFrame_rows :
    Z.2 = (addr X x, some (dataOf x)) ::
      ((List.ofFn fun s : Fin (2 ^ a) =>
        let y := (X.slots.base.target (x, s)).1
        (addr X y, some (dataOf y))) ++
       (List.ofFn fun s : Fin (2 ^ a) =>
        let y := (X.slots.base.target.symm (x, s)).1
        (addr X y, some (dataOf y)))) := by
  simp [trueFrame, ballList, bfs, nbrAt_addr, nbrAddrs, List.map_ofFn, Function.comp_def,
    outNbr, inNbr, refreshOld_addr, trueDatum]

theorem datumAt_root : datumAt Z 0 = dataOf x := by
  rw [datumAt, trueFrame_rows] <;> rfl

theorem datumAt_in (s : Fin (2 ^ a)) :
    datumAt Z (inPos a s) = dataOf (X.slots.base.target.symm (x, s)).1 := by
  rw [datumAt, trueFrame_rows, inPos, readAt_secondBlock] <;> rfl

theorem rowAt_root (s : Fin (2 ^ a)) : rowAt Z 0 s.val = codeSlot (panel X x) s := by
  simp only [rowAt, datumAt_root, trueDatum, codeRefreshDatum, readAt_panel]

theorem laneCount_true : laneCount Z = 2 ^ g := by
  simp only [laneCount, datumAt_root, trueDatum, codeRefreshDatum, length_laneList]

theorem fullLane_true (p : Fin (2 ^ a)) (l : BitWord g) :
    fullLane Z p.val (bwNum l) = bwNum (oldLane p l) := by
  rw [fullLane, laneCount_true, number_oldLane]

theorem termAt_true (l : BitWord g) (p : Fin (2 ^ a)) (s : Fin dH) :
    termAt Z (bwNum l) p.val s.val = (c (x, l)).val (p, s) := by
  simp only [termAt, datumAt_root, trueDatum, codeRefreshDatum, readAt_laneList, readAt_ofFn]

theorem root_width (s : Fin (2 ^ a)) (w : BitWord (a + g)) :
    widthAt Z 0 s.val (bwNum w) = X.width ((x, s), w) := by
  simp only [widthAt, rowAt_root, codeSlot, panel, readAt_laneList, outWidths]

theorem in_width (s i : Fin (2 ^ a)) (w : BitWord (a + g)) :
    widthAt Z (inPos a s) i.val (bwNum w) =
      X.width (((X.slots.base.target.symm (x, s)).1, i), w) := by
  simp only [widthAt, rowAt, datumAt_in, trueDatum, codeRefreshDatum, readAt_panel,
    codeSlot, panel, readAt_laneList, outWidths]

theorem tieCell_true (l : BitWord g) (t : Tie (2 ^ a)) :
    tieCell a t Z (bwNum l) =
      blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) (x, l) t := by
  rw [demand_eq]
  cases ht : t.1
  · simp only [tieCell, demandOf, ht, Bool.false_eq_true, if_false, fullLane_true,
      rowAt_root, codeSlot, panel, inNbr, inFar, inData, incomingLane, ← number_sub,
      in_width, outWidths]
  · simp only [tieCell, demandOf, ht, if_true, fullLane_true, root_width, oldLane, outWidths]

end
end P1ChkFinal.AstraC10
