import P1SolCone.GuardedLevel

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

theorem sizeList_bound {A : Type*} [Codec A] (xs : List A) (b : ℕ)
    (h : ∀ x ∈ xs, size x ≤ b) : size xs ≤ xs.length * (b+1) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := h x List.mem_cons_self
    have h₂ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [size_cons, List.length_cons,Nat.succ_mul]
    omega

theorem halfCode_size (z : HalfCode) (slots width : ℕ)
    (hos : z.1.length ≤ slots) (his : z.2.length ≤ slots)
    (hw : ∀ w ∈ z.1 ++ z.2, w.length ≤ width) :
    size z ≤ 2 * (slots * (2 * width + 2) + 1) + 1 := by
  have out := sizeList_bound z.1 (2*width+1) (fun w hm => by
    rw [P1ChkFinal.size_listBool]
    have := hw w (List.mem_append_left _ hm)
    omega)
  have inn := sizeList_bound z.2 (2*width+1) (fun w hm => by
    rw [P1ChkFinal.size_listBool]
    have := hw w (List.mem_append_right _ hm)
    omega)
  change size z.1 ≤ z.1.length * (2*width+2) + 1 at out
  change size z.2 ≤ z.2.length * (2*width+2) + 1 at inn
  have bo := Nat.mul_le_mul_right (2*width+2) hos
  have bi := Nat.mul_le_mul_right (2*width+2) his
  rw [size_prod]
  omega

theorem natSize_le_of_lt_pow (n bits : ℕ) (h : n < 2 ^ bits) : size n ≤ 2 * bits + 1 := by
  change size (binary n) ≤ _
  rw [binary_eq_coneBin, P1ChkFinal.size_listBool]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (length_bin_le bits n h)) 1

theorem keyCode_size (k : KeyCode) (slots width bits : ℕ)
    (haddr : k.1.1 < 2 ^ bits) (hlane : k.1.2 < 2 ^ bits)
    (hos : k.2.1.length ≤ slots) (his : k.2.2.length ≤ slots)
    (hw : ∀ w ∈ k.2.1 ++ k.2.2, w.length ≤ width) :
    size k ≤ 4 * bits + 2 * slots * (2*width+2) + 7 := by
  have h₁ := natSize_le_of_lt_pow k.1.1 bits haddr
  have h₂ := natSize_le_of_lt_pow k.1.2 bits hlane
  have h₃ := halfCode_size k.2 slots width hos his hw
  change size k.1.1 + size k.1.2 + 1 + size k.2 + 1 ≤ _
  rw [Nat.mul_assoc 2 slots]
  omega

theorem labelSize_bound {F : Type} [Fintype F] (v : Label F) : size v ≤ 2 * Fintype.card F + 1 := by
  change size (tally (Fintype.equivFin F v.val).val) ≤ _
  rw [size_tally,tally_length]
  have h := (Fintype.equivFin F v.val).isLt
  omega

theorem placedCodes_length_le {ks : List PositionCode} {halves : PositionCode → List HalfCode}
    {entry : List KeyCode} (he : entry ∈ placedCodes halves ks) : entry.length ≤ ks.length := by
  unfold placedCodes at he
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp he
  rw [List.length_zip]
  exact min_le_left _ _

/-- The encoded pointer tallies cost at most a linear factor in the number of old keys. -/
theorem assembledLevel_size {F : Type} [CommRing F] [Fintype F]
    (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F) (keys : List KeyCode) (parents entries : ℕ)
    (hp : ∀ k ∈ keys, (pre k.1).length ≤ parents)
    (he : ∀ k ∈ keys, (placedCodes halves (pre k.1)).length ≤ entries) :
    let old := needKeys pre halves keys
    let pointerSize := parents * (2 * old.length + 2) + 1
    let entrySize := 2 * Fintype.card F + 2 + pointerSize
    size (P1P5.encLevel (assembleLevel pre halves kernel keys).2) ≤
      keys.length * (entries * (entrySize+1) + 2) + 1 := by
  intro old ps es
  unfold P1P5.encLevel assembleLevel
  simp only [List.map_map, Function.comp_def]
  have r (k : KeyCode) (hk : k ∈ keys) :
      size ((placedCodes halves (pre k.1)).map fun p =>
        (Label.mk (kernel k p), (p.map old.idxOf).map tally)) ≤ entries * (es+1) + 1 := by
    apply (sizeList_bound _ es (fun q hq => ?_)).trans
    · rw [List.length_map]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (he k hk)) 1
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
      have bound (pointer : Tally) (hm : pointer ∈ (x.map old.idxOf).map tally) : size pointer ≤ 2 * old.length + 1 := by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hi
        rw [size_tally, tally_length]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (List.idxOf_le_length)) 1
      have pp := sizeList_bound _ _ bound
      simp only [List.length_map] at pp
      have hnum := (placedCodes_length_le hx).trans (hp k hk)
      have ht : size ((x.map old.idxOf).map tally) ≤ ps :=
        pp.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (2*old.length+2) hnum) 1)
      have hlabel := labelSize_bound (F := F) (Label.mk (kernel k x))
      simp only [size_prod, es, ps]
      dsimp only [ps] at ht
      omega
  apply (sizeList_bound _ (entries * (es+1) + 1) _).trans
  · rw [List.length_map]
  · intro x hx
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
    simpa only [List.map_map, Function.comp_def] using r k hk

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

theorem coneHistory_frontier {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b n j : ℕ)
    (hj : j ≤ (S.steps + 1) * P1Wrap.Params.T (P1Int.P11.portConsts Bt) (P1Int.lpTime a b n)) :
    Bt.recordLimit ^ j ≤ Mbar Bt V a b n := by
  let t := P1Int.lpTime a b n
  let T := P1Wrap.Params.T (P1Int.P11.portConsts Bt) t
  have hp : 1 ≤ Bt.recordLimit := le_max_left _ _
  calc
    Bt.recordLimit ^ j ≤ Bt.recordLimit ^ ((S.steps + 1) * T) := Nat.pow_le_pow_right hp hj
    _ = (Bt.recordLimit ^ (S.steps+1)) ^ T := pow_mul ..
    _ ≤ Bt.growthConstant ^ T := Nat.pow_le_pow_left (le_max_right _ _) _
    _ ≤ Mbar Bt V a b n := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

end P1SolCone.SolCone
