import P1SolCone.FullSchedule
import P1SolCone.ReachableSize
import P1SolCone.TraceInitial

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open private slotCap from P1Wit.SpaceFacts

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

local notation "Wn" q => bin (List.length (Prod.fst q))
local notation "Dq" q => coneDims B V a b d bigBias termBias (P1Batch.bval (Wn q))
local notation "Cq" q => coneReadClock B V a b bigBias termBias (Wn q)
local notation "Mq" q => Mbar B V a b (P1Batch.bval (Wn q))

variable {F : Type} [CommRing F] [Fintype F]

def queryInitial (q : Qry) : CheckedTableState F :=
  initialConeState (Dq q) q.2.1 (Mq q) (P1Batch.bval q.2.2)

def queryTrace (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (q : Qry) (ls : List ℕ) : CheckedTableState F :=
  ls.foldl (checkedPhaseStep B V a b d bigBias termBias shr ref q.2.1 (Wn q))
    (queryInitial B V a b d bigBias termBias q)

def queryTraceBits (q : Qry) : ℕ :=
  (Dq q).bigW + q.2.2.length + ((Dq q).top+1)*(Cq q).length + 1

theorem queryInitial_fit (q : Qry) (s : List KeyCode × List (P1P5.Level F))
    (hi : queryInitial (F := F) B V a b d bigBias termBias q = some s) :
    ∃ key, s = ([key],[]) ∧
      keyFits ((Dq q).bigW + q.2.2.length) (Cq q).length (slotCap S) (Mq q) key := by
  let D := Dq q
  let clock := Cq q
  have geom := coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval (Wn q)) D.top le_rfl
  have hslots : 0 < (D.lv D.top).slots := by rw [geom.slots_eq]; exact Nat.two_pow_pos _
  have hlanes : 0 < (D.lv D.top).lanes := by rw [geom.lanes_eq]; exact Nat.two_pow_pos _
  have axis := coneAxisClock_fits B V a b d bigBias termBias (Wn q) D.top le_rfl
  have hclock := coneReadClock_axes B V a b bigBias termBias (Wn q)
  apply initialConeState_shape D q.2.1 _ _ _ clock.length _ _ _ hlanes geom.slots_le s hi
  · rw [bval_eq_value]
    exact (Bits.value_lt q.2.2).trans_le (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left q.2.2.length D.bigW))
  · exact (Nat.le_mul_of_pos_right _ hslots).trans (axis.trans hclock)

set_option maxHeartbeats 1600000 in
theorem queryTrace_size (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (q : Qry) (ls : List ℕ) (hls : ∀ l ∈ ls, l < (Dq q).top) (hn : ls.length ≤ (Dq q).top) :
    size (encodeConeState (queryTrace B V a b d bigBias termBias shr ref q ls)) ≤
      keyCountBound (slotCap S) (Mq q) *
        (4 * queryTraceBits B V a b d bigBias termBias q + 2 * slotCap S * (2 * (Mq q) + 2) + 8)
        + (Dq q).top * (levelCodeBound (slotCap S) (Mq q) B.recordLimit (Fintype.card F) + 1) + 5 := by
  let w := Wn q
  let D := Dq q
  let clock := Cq q
  let width := (Mq q)
  let bits := queryTraceBits B V a b d bigBias termBias q
  let addr := D.bigW + q.2.2.length
  let eval := checkedPhaseStep B V a b d bigBias termBias shr ref q.2.1 w
  let N := keyCountBound (slotCap S) width
  let L := levelCodeBound (slotCap S) width B.recordLimit (Fintype.card F)
  let K := 4 * bits + 2 * slotCap S * (2 * width + 2) + 7
  change size (encodeConeState (ls.foldl eval (queryInitial B V a b d bigBias termBias q))) ≤
    N * (K+1) + D.top * (L+1) + 5
  cases hi : queryInitial (F := F) B V a b d bigBias termBias q with
  | none =>
    have he (is : List ℕ) : is.foldl eval none = none := by
      induction is with
      | nil => rfl
      | cons l is ih => exact ih
    rw [he]
    have hz : size (encodeConeState (none : CheckedTableState F)) = 5 := rfl
    rw [hz]
    exact Nat.le_add_left _ _
  | some s =>
    obtain ⟨key, rfl, hfit⟩ := queryInitial_fit B V a b d bigBias termBias q s hi
    have he := assembleChecked_eq_fold (phaseAllowed D q.2.1 B.recordLimit width)
      (phasePreimages D q.2.1) (phaseHalves D q.2.1)
      (phaseKernel (numericKernelValues shr ref) (conePad B.growthConstant width)
        (2 ^ S.expanderExponent) D q.2.1) ls.reverse [key]
    rw [List.reverse_reverse] at he
    change _ = ls.foldl eval (some ([key],[])) at he
    rw [← he]
    cases hr : assembleCheckedChain (phaseAllowed D q.2.1 B.recordLimit width)
        (phasePreimages D q.2.1) (phaseHalves D q.2.1)
        (phaseKernel (numericKernelValues shr ref) (conePad B.growthConstant width)
          (2 ^ S.expanderExponent) D q.2.1) ls.reverse [key] with
    | none =>
      have hz : size (encodeConeState (none : CheckedTableState F)) = 5 := rfl
      rw [hz]
      exact Nat.le_add_left _ _
    | some run =>
      obtain ⟨keys, levels⟩ := run
      have hh (l : ℕ) (hl : l ∈ ls.reverse) := hls l (List.mem_reverse.mp hl)
      have hLen : ls.reverse.length ≤ D.top := by simpa only [List.length_reverse] using hn
      obtain ⟨hkeys,hfit',hlev,hsize⟩ := checkedTrace_bounds B V a b d bigBias termBias w q.2.1
        addr (Nat.le_add_right _ _) key hfit _ ls.reverse hh hLen keys levels hr
      have hl : (ls.reverse.length+1)*clock.length ≤ 2 ^ bits := by
        calc
          _ ≤ (D.top+1)*clock.length := Nat.mul_le_mul_right _ (Nat.succ_le_succ hLen)
          _ ≤ bits := by
            change (D.top+1)*clock.length ≤ addr + (D.top+1)*clock.length + 1
            omega
          _ ≤ 2 ^ bits := Nat.lt_two_pow_self.le
      have hk (z : KeyCode) (hz : z ∈ keys) : size z ≤ K := by
        apply keyFits_size addr ((ls.reverse.length+1)*clock.length) _ _ _ z _ hl (hfit' z hz)
        unfold bits queryTraceBits
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have h₁ := (sizeList_bound keys K hk).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hkeys) 1)
      change size keys ≤ N * (K+1) + 1 at h₁
      have hl' : levels.length ≤ D.top := hlev.symm ▸ hLen
      have h₂ := (sizeList_bound (levels.map P1P5.encLevel) L (fun r hr' => by
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr'
        exact hsize j hj)).trans
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by simpa only [List.length_map] using hl')) 1)
      change 1 + (size keys + size (levels.map P1P5.encLevel) + 1) + 1 ≤ _
      omega

end

end P1SolCone.SolCone
