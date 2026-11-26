import P1SolGreedy.FieldCache
import P1SolGreedy.C5Words

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev SlotQuery := BaseRow × NumberWord × NumberWord

/-- Field at a base and a numbered slot. -/
def slotAt (c : Mem) (q : SlotQuery) : P1Batch.Req :=
  slotRequest ((rowSection c q.1, Carry.times0 (q.2.1, q.1.2.2.1)), q.2.2)

@[fun_prop] theorem slotAt_poly (c : Mem) : Poly (slotAt c) := by
  unfold slotAt
  fun_prop

def slotsAt (c : Mem) (q : BaseRow × NumberWord × List NumberWord) : List P1Batch.Req :=
  slotRequests ((rowSection c q.1, Carry.times0 (q.2.1, q.1.2.2.1)), q.2.2)

@[fun_prop] theorem slotsAt_poly (c : Mem) : Poly (slotsAt c) := by
  unfold slotsAt
  fun_prop

theorem slotsAt_eq (c : Mem) (r : BaseRow) (y : NumberWord) (ks : List NumberWord) :
    slotsAt c (r, y, ks) = ks.map (fun k => slotAt c (r, y, k)) := rfl

theorem requestNumbers_slotAt (D : Dims) (ℓ : ℕ) (c : Mem) (y k : NumberWord) :
    requestNumbers (slotAt c (levelRow D ℓ, y, k)) =
      requestNumbers (fieldReq D (secLev ℓ c) (P1Batch.bval y * (D.lv ℓ).slots + P1Batch.bval k)) := by
  have hs : (levelRow D ℓ).2.2.1 = bin (D.lv ℓ).slots := rfl
  simp only [slotAt, slotRequest, requestNumbers_rowField, bval_add, bval_mul, hs, bval_bin]

theorem slotAt_width (D : Dims) (ℓ : ℕ) (c : Mem) (y k : NumberWord) :
    P1Batch.bval (slotAt c (levelRow D ℓ, y, k)).2 = D.width (secLev ℓ c) :=
  (congrArg Prod.snd (requestNumbers_slotAt D ℓ c y k)).trans (bval_bin _)

theorem wordRange_length (n : ℕ) : (wordRange (tally n)).length = n := by
  rw [wordRange_tally, List.length_map, List.length_range]

theorem born_mem_wordRange {n k : ℕ} (hk : k < n) : Carry.born k ∈ wordRange (tally n) := by
  rw [wordRange_tally]
  exact List.mem_map_of_mem (List.mem_range.mpr hk)

theorem cacheRead_slot (D : Dims) (u : List Bool) (ℓ : ℕ) (c : Mem)
    (qs : List P1Batch.Req) (y k : NumberWord) {n : ℕ}
    (hk : P1Batch.bval k < n)
    (hs : ∀ r ∈ slotsAt c (levelRow D ℓ, y, wordRange (tally n)), r ∈ qs) :
    P1Batch.bval (cacheRead (qs.map (fun r => (r, P1Batch.fetch u r)), slotAt c (levelRow D ℓ, y, k))) =
      readField D u (secLev ℓ c) (P1Batch.bval y * (D.lv ℓ).slots + P1Batch.bval k) := by
  let k' := Carry.born (P1Batch.bval k)
  let r := slotAt c (levelRow D ℓ, y, k')
  have hr : r ∈ qs := by
    apply hs
    rw [slotsAt_eq]
    exact List.mem_map_of_mem (born_mem_wordRange hk)
  have he : requestNumbers (slotAt c (levelRow D ℓ, y, k)) = requestNumbers r := by
    unfold r
    rw [requestNumbers_slotAt, requestNumbers_slotAt, bval_born]
  rw [cacheRead_fetch _ _ _ ⟨r, hr, he⟩, fetch_of_requestNumbers _ (requestNumbers_slotAt D ℓ c y k),
    bval_bitsVal, ← readField_eq]

end P1SolGreedy.SolDemand
