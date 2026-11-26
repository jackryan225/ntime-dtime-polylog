import P1SolGreedy.GreedyDecisions

open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

/-- First C5 batch: root colour, then the addresses of outgoing and incoming neighbours. -/
def c5RootRequests (D : Dims) (ℓ Y : ℕ) : List P1Batch.Req :=
  fieldReq D (secLev ℓ .colour) Y ::
    (((List.range (D.lv ℓ).slots).map fun k =>
      fieldReq D (secLev ℓ .outAddr) (Y * (D.lv ℓ).slots + k)) ++
    ((List.range (D.lv ℓ).slots).map fun k =>
      fieldReq D (secLev ℓ .inAddr) (Y * (D.lv ℓ).slots + k)))

/-- Decode the two parts of the root response using the default empty field. -/
def c5RootDecode (fs : List (List Bool)) : ℕ × List ℕ :=
  (bitsVal (fs.headD []), fs.tail.map bitsVal)

/-- C5 masks larger addresses. Cap their second-batch reads at the root, which is in range. -/
def c5ColourRequests (D : Dims) (ℓ Y : ℕ) (neighbours : List ℕ) : List P1Batch.Req :=
  neighbours.map fun Z => fieldReq D (secLev ℓ .colour) (min Z Y)

def c5ColourDecode (cap Y : ℕ) (neighbours : List ℕ) (fs : List (List Bool)) : List ℕ :=
  List.zipWith (fun Z f =>
    if Z < Y then (if bitsVal f < cap then bitsVal f else 0) else 0) neighbours fs

theorem c5_root_reads (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    c5RootDecode ((c5RootRequests D ℓ Y).map (P1Batch.fetch u)) =
      (rdColour D u ℓ Y,
        ((List.range (D.lv ℓ).slots).map fun k => rdOutAddr D u ℓ Y k) ++
        ((List.range (D.lv ℓ).slots).map fun k => rdInAddr D u ℓ Y k)) := by
  simp only [c5RootDecode, c5RootRequests, List.map_cons, List.headD_cons, List.tail_cons,
    List.map_append, List.map_map, Function.comp_def, ← readField_eq,
    rdColour, rdOutAddr, rdInAddr]

theorem c5_colour_reads (D : Dims) (u : List Bool) (ℓ Y : ℕ) (neighbours : List ℕ) :
    c5ColourDecode (2 * (D.lv ℓ).slots + 1) Y neighbours
      ((c5ColourRequests D ℓ Y neighbours).map (P1Batch.fetch u)) =
      neighbours.map (mcol D u ℓ (D.lv ℓ).slots Y) := by
  induction neighbours with
  | nil => rfl
  | cons z zs ih =>
    simp only [c5ColourRequests, List.map_cons, c5ColourDecode, List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    congr 1
    rw [← readField_eq]
    unfold mcol
    by_cases hz : z < Y
    · rw [ite_eq_left hz, ite_eq_left hz, min_eq_left hz.le]
      rfl
    · rw [ite_eq_right hz, ite_eq_right hz]

/-- The two batches and a format-capped least-missing test implement C5 on every bit list. -/
theorem c5_two_batches (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    let roots := c5RootDecode ((c5RootRequests D ℓ Y).map (P1Batch.fetch u))
    let colours := (c5ColourRequests D ℓ Y roots.2).map (P1Batch.fetch u)
    leastMissing (2 * (D.lv ℓ).slots + 1) roots.1
        (c5ColourDecode (2 * (D.lv ℓ).slots + 1) Y roots.2 colours) = true ↔
      C5chk D u ℓ Y := by
  dsimp only
  rw [c5_root_reads, c5_colour_reads]
  simp only [List.map_append, List.map_map, Function.comp_def]
  exact C5chk_decision D u ℓ Y

theorem c5RootRequests_valid (D : Dims) {ℓ Y : ℕ} (hℓ : ℓ ≤ D.top)
    (hS : (D.lv ℓ).shrink = true) (hY : Y < (D.lv ℓ).bases)
    {r : P1Batch.Req} (hr : r ∈ c5RootRequests D ℓ Y) :
    P1Batch.bval r.1 ≤ D.fixedLen := by
  have hSlot (k : ℕ) (hk : k < (D.lv ℓ).slots) :
      Y * (D.lv ℓ).slots + k ≤ (D.lv ℓ).bases * (D.lv ℓ).slots := by
    calc
      _ ≤ Y * (D.lv ℓ).slots + (D.lv ℓ).slots := Nat.add_le_add_left hk.le _
      _ = (Y + 1) * (D.lv ℓ).slots := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hY)
  unfold c5RootRequests at hr
  rcases List.mem_cons.mp hr with he | he
  · subst r
    simp only [fieldReq, bval_bin]
    apply field_le_fixedLen D (D.secLev_lt_nSec .colour hℓ)
    simpa only [D.count_secLev .colour hℓ, LevelDims.count, hS, ite_true] using hY.le
  · rcases List.mem_append.mp he with ho | hi
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ho
      simp only [fieldReq, bval_bin]
      apply field_le_fixedLen D (D.secLev_lt_nSec .outAddr hℓ)
      exact (D.count_secLev .outAddr hℓ).symm ▸ hSlot k (List.mem_range.mp hk)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      simp only [fieldReq, bval_bin]
      apply field_le_fixedLen D (D.secLev_lt_nSec .inAddr hℓ)
      exact (D.count_secLev .inAddr hℓ).symm ▸ hSlot k (List.mem_range.mp hk)

theorem c5ColourRequests_valid (D : Dims) {ℓ Y : ℕ} (hℓ : ℓ ≤ D.top)
    (hS : (D.lv ℓ).shrink = true) (hY : Y < (D.lv ℓ).bases) (zs : List ℕ)
    {r : P1Batch.Req} (hr : r ∈ c5ColourRequests D ℓ Y zs) :
    P1Batch.bval r.1 ≤ D.fixedLen := by
  obtain ⟨Z, _, rfl⟩ := List.mem_map.mp hr
  simp only [fieldReq, bval_bin]
  apply field_le_fixedLen D (D.secLev_lt_nSec .colour hℓ)
  rw [D.count_secLev .colour hℓ]
  simp only [LevelDims.count, hS, ite_true]
  exact (Nat.min_le_right Z Y).trans hY.le

end P1SolGreedy.SolDemand
