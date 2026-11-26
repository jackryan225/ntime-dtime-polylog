import P1SolF0R.HeaderStages
import P1SolF0R.HeaderCorrect

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

noncomputable section

private theorem readAt_at {A : Type} (d : A) (xs : List A) (i : ℕ) (hi : i < xs.length) :
    readAt d xs i = xs[i] := by
  simp only [readAt, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem chunkAt_group {A : Type} (xs : List A) (f : A → List (List Bool))
    (hw : ∀ a ∈ xs, (f a).length = 4) (i : ℕ) (hi : i < xs.length) :
    chunkAt (xs.flatMap f, i) = chunkAt (f xs[i], 0) := by
  unfold chunkAt
  dsimp only
  rw [show 4 * i = 4 * i + 0 by omega,
    readAt_flatMap_groups [] f 4 xs hw i 0 hi (by decide),
    readAt_flatMap_groups [] f 4 xs hw i 1 hi (by decide),
    readAt_flatMap_groups [] f 4 xs hw i 2 hi (by decide),
    readAt_flatMap_groups [] f 4 xs hw i 3 hi (by decide)]

def planOne (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (a : PublicClocks) (u : List Bool) (q : Request) : Planned :=
  let chunk := chunkAt ((reqInterval V.K (a, q)).map (P1Batch.fetch u), 0)
  (headerPlan V tape cross ((a, reqSite V.K (a, q)), (q.1.2, chunk)), q.2)

theorem planHeaders_eq {F : Type} (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (cross : CrossIn → Bool) (a : PublicClocks) (u : List Bool) (c : Label F) (qs : List Request) :
    batchAdvance (witnessRequests V.K) (planHeaders V tape cross) u (c, qs) a =
      (c, qs.map (planOne V tape cross a u)) := by
  unfold batchAdvance planHeaders
  dsimp only
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hj
    have hq : i < qs.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map, List.getElem_range, planAt, readAt_at _ qs i hq, planOne, witnessRequests,
      List.map_flatMap]
    rw [chunkAt_group qs (fun q => (reqInterval V.K (a, q)).map (P1Batch.fetch u))
      (fun q _ => by rw [List.length_map, reqInterval_length]) i hq]

theorem resolveEntries_eq {F : Type} (V : FiniteMultiTapeMachine) (a : PublicClocks)
    (x : List Bool) (c : Label F) (ps : List Planned)
    (hLen : ∀ p ∈ ps, p.1.2.length ≤ a.2.2.1.length)
    (hBound : ∀ p ∈ ps, ∀ q ∈ p.1.2, resolvePin V q (P1Batch.fetch x (pinReq q)) ≤ Fintype.card V.Γ) :
    batchAdvance pinRequests (resolveEntries V) x (c, ps) a =
      (c, ps.map fun p => (resolveHeader V x p.1, p.2)) := by
  unfold batchAdvance resolveEntries
  dsimp only
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hj
    have hp : i < ps.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map, List.getElem_range, entryAt, readAt_at _ ps i hp, resolveHeader,
      pinRequests, List.map_flatMap]
    congr 2
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]
    · intro j hj hj'
      have hpin : j < ps[i].1.2.length := by simpa only [List.length_map] using hj'
      have him : ps[i] ∈ ps := List.getElem_mem (h := hp)
      have hj' : j < a.2.2.1.length := hpin.trans_le (hLen ps[i] him)
      let group (p : Planned) := (reqPins (a.2.2.1, p)).map (P1Batch.fetch x)
      have hw (p : Planned) (_ : p ∈ ps) : (group p).length = a.2.2.1.length := by
        simp only [group, List.length_map, reqPins_length]
      have hread := readAt_flatMap_groups [] group a.2.2.1.length ps hw i j hp hj'
      have hbit : readAt [] (group ps[i]) j =
          P1Batch.fetch x (pinReq ps[i].1.2[j]) := by
        have hg : j < (group ps[i]).length := by rw [hw _ him]; exact hj'
        rw [readAt_at [] _ _ hg]
        simp only [group, reqPins, List.getElem_map, List.getElem_range, readAt_at _ ps[i].1.2 j hpin]
      simp only [List.getElem_map, List.getElem_range, pinReply, readAt_at (.inl 0) ps[i].1.2 j hpin]
      rw [hread, hbit, min_eq_left (hBound _ him ps[i].1.2[j] (List.getElem_mem (h := hpin)))]

private theorem pinQuery_code_bound (V : FiniteMultiTapeMachine) (p : Bool × ℕ × ℕ × ℕ)
    (bits : List Bool) : resolvePin V (pinQuery V p) bits ≤ Fintype.card V.Γ := by
  have hc (s : V.Γ) : symbolCode V s ≤ Fintype.card V.Γ := (Fintype.equivFin V.Γ s).isLt
  simp only [pinQuery, Bool.cond_eq_ite]
  split_ifs <;> simp only [resolvePin, Nat.zero_le] <;> apply hc

set_option maxHeartbeats 700000 in
theorem headerPlan_code_bound (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (cross : CrossIn → Bool) (p : LocalInput) (q : PinQuery) (bits : List Bool)
    (hq : q ∈ (headerPlan V tape cross p).2) : resolvePin V q bits ≤ Fintype.card V.Γ := by
  simp only [headerPlan, Bool.cond_eq_ite, noPins_eq] at hq
  split_ifs at hq <;> simp only [List.not_mem_nil] at hq
  unfold portPlan at hq
  obtain ⟨v, rfl⟩ := pinColumn_queries V _ q hq
  exact pinQuery_code_bound V v bits

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.planHeaders_eq
#print axioms P1SolF0R.SolReader.resolveEntries_eq
