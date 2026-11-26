import P1SolGreedy.C6Semantics
import P1ChkFinal.BatchLink
import P1Dispatch.TaskBridge

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

theorem slotsAt_length (c : Mem) (r : BaseRow) (y : NumberWord) (ks : List NumberWord) :
    (slotsAt c (r, y, ks)).length = ks.length := by rw [slotsAt_eq, List.length_map]

theorem length_flatMap_constant {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy)), List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem tagRootRaw_length (D : Dims) (ℓ a g : ℕ) (len Y : NumberWord) :
    (tagRootRaw (activeTag D ℓ a g len Y)).length = 1 + 4 * 2 ^ a := by
  simp only [tagRootRaw, activeTag, tagRow, Bool.cond_true, List.length_cons, List.length_append,
    slotsAt_length, wordRange_length]
  omega

theorem tagSecondRaw_length (D : Dims) (ℓ a g : ℕ) (len Y : NumberWord) (c : FieldCache) :
    (tagSecondRaw (activeTag D ℓ a g len Y, c)).length = (2 * 2 ^ a) * (1 + 2 ^ a) := by
  rw [tagSecondRaw_active, length_flatMap_constant _ _ (1 + 2 ^ a)]
  · unfold tagNeighbors Code.polyPush tagPorts
    simp only [activeTag, tagRow, List.length_map]
    have h : ([false, true].product (wordRange (tally (2 ^ a)))).length =
        [false, true].length * (wordRange (tally (2 ^ a))).length := List.length_product _ _
    rw [h, wordRange_length]
    rfl
  · intro z _
    rw [List.length_cons, slotsAt_length, wordRange_length, Nat.add_comm]

theorem offsetAt_width (D : Dims) (ℓ : ℕ) (y : NumberWord) :
    P1Batch.bval (offsetAt (levelRow D ℓ, y)).2 = D.width (secLev ℓ .offset) := by
  change P1Batch.bval (rowSection .offset (levelRow D ℓ)).2 = _
  rw [rowSection_levelRow, bval_bin]

theorem tagRootRaw_width (D : Dims) (ℓ a g : ℕ) (len Y : NumberWord) (r : P1Batch.Req)
    (hr : r ∈ tagRootRaw (activeTag D ℓ a g len Y)) :
    P1Batch.bval r.2 ≤ size (levelRow D ℓ) := by
  rw [tagRootRaw_active] at hr
  rcases List.mem_cons.mp hr with rfl | h
  · rw [offsetAt_width]
    exact width_le_size_levelRow D ℓ .offset
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
    rw [slotsAt_eq] at hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    rw [slotAt_width]
    exact width_le_size_levelRow D ℓ c

theorem tagSecondRaw_width (D : Dims) (ℓ a g : ℕ) (len Y : NumberWord) (cache : FieldCache)
    (r : P1Batch.Req) (hr : r ∈ tagSecondRaw (activeTag D ℓ a g len Y, cache)) :
    P1Batch.bval r.2 ≤ size (levelRow D ℓ) := by
  rw [tagSecondRaw_active] at hr
  obtain ⟨z, _, hz⟩ := List.mem_flatMap.mp hr
  rcases List.mem_cons.mp hz with rfl | hm
  · rw [offsetAt_width]
    exact width_le_size_levelRow D ℓ .offset
  · rw [slotsAt_eq] at hm
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hm
    rw [slotAt_width]
    exact width_le_size_levelRow D ℓ .outDisp

def tagBudget (q : TagContext) (u : List Bool) : Prop :=
  let s := tagNext (q, (tagRoot q).map (P1Batch.fetch u))
  P1Batch.total (tagRoot q) ≤ 5 * (size q + 1) ^ 3 ∧
    P1Batch.total (tagSecond s) ≤ 5 * (size q + 1) ^ 3

theorem tagBudget_active (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y : NumberWord) :
    tagBudget (activeTag D ℓ a g len Y) u := by
  let q := activeTag D ℓ a g len Y
  let N := size q + 1
  let r := tagRootRaw q
  let c := (cacheFields (r, (tagRoot q).map (P1Batch.fetch u)))
  let s := tagSecondRaw (q, c)
  have hw : size (levelRow D ℓ) ≤ N := by
    simp only [N, q, activeTag, size_prod]
    omega
  have hd : 2 ^ a + 1 ≤ N := by
    simp only [N, q, activeTag, tagRow, size_prod, size_tally, tally_length]
    omega
  have hr : r.length ≤ 5 * N := by
    rw [show r.length = 1 + 4 * 2 ^ a from tagRootRaw_length D ℓ a g len Y]
    omega
  have hs : s.length ≤ (5 * N) * N := by
    rw [show s.length = (2 * 2 ^ a) * (1 + 2 ^ a) from tagSecondRaw_length D ℓ a g len Y c]
    apply Nat.mul_le_mul <;> omega
  have hr' : P1Batch.total r ≤ 5 * N ^ 3 := by
    calc
      _ ≤ r.length * size (levelRow D ℓ) := total_le_of_width_le _ _ (tagRootRaw_width D ℓ a g len Y)
      _ ≤ (5 * N) * N := Nat.mul_le_mul hr hw
      _ ≤ ((5 * N) * N) * N := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      _ = 5 * N ^ 3 := by ring
  have hs' : P1Batch.total s ≤ 5 * N ^ 3 := by
    calc
      _ ≤ s.length * size (levelRow D ℓ) := total_le_of_width_le _ _ (tagSecondRaw_width D ℓ a g len Y c)
      _ ≤ ((5 * N) * N) * N := Nat.mul_le_mul hs hw
      _ = 5 * N ^ 3 := by ring
  change P1Batch.total (clipRequests (len, r)) ≤ 5 * N ^ 3 ∧
    P1Batch.total (clipRequests (len, s)) ≤ 5 * N ^ 3
  exact ⟨(clipRequests_total len r).trans_le hr', (clipRequests_total len s).trans_le hs'⟩

theorem tagBudget_setup (D : Dims) (u : List Bool) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    tagBudget (setupTag (tagFormat D M ag, i)) u := by
  let q := setupTag (tagFormat D M ag, i)
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let Y := q.1.2.2.1
  change tagBudget q u
  by_cases h : ShrinkIdx D (P1Batch.bval i)
  · have hq : q = activeTag D ℓ (ag ℓ).1 (ag ℓ).2 (bin M) Y := setupTag_inRange D M ag i h
    exact hq.symm ▸ tagBudget_active D u ℓ (ag ℓ).1 (ag ℓ).2 (bin M) Y
  · obtain ⟨hs, _, _⟩ := setupTag_spec D M ag i
    have hf : q.1.2.1 = false := Bool.eq_false_iff.mpr fun hh => h (hs.mp hh)
    simp only [tagBudget, tagRoot, tagRootRaw, tagNext, tagSecond, tagSecondRaw, hf, Bool.cond_false,
      clipRequests, Code.polyPush, List.map_nil, P1Batch.total, List.sum_nil, Nat.zero_le, and_self]

end P1SolGreedy.SolDemand

namespace P1SolGreedy

open SolDemand Classical

set_option maxHeartbeats 1200000 in
/-- Two batches implement C6 for every witness of its prescribed length. -/
theorem taskC6 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypTags dims M ag) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C6fam dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let setup := setupC6 dims M ag
  have hp : Poly setup := setupC6_poly dims M ag hf
  let q (p : QDom M K) := setup (SetupIdx p)
  let u (p : QDom M K) := p.val.2.1
  let s (p : QDom M K) := tagNext (q p, (tagRoot (q p)).map (P1Batch.fetch (u p)))
  have hs : Dom smallSize (fun p : QDom M K => size (q p)) := (hp.length.map SetupIdx).sub index_size
  have hsmall : Dom smallSize (fun p : QDom M K => 5 * (size (q p) + 1) ^ 3) :=
    (Dom.const _ 5).mul ((hs.add (Dom.const _ 1)).pow 3)
  have publicEq (p : QDom M K) : q p =
      setupTag (tagFormat (dims p.val.1.length) (M p.val.1.length) (ag p.val.1.length), p.val.2.2) := by
    simp only [q, setup, setupC6, SetupIdx, bval_bin]
  have hlen (p : QDom M K) : P1Batch.bval (q p).1.1 = (u p).length := by
    rw [publicEq, setupTag_length]
    exact p.property.1.symm
  have bounds (p : QDom M K) : tagBudget (q p) (u p) :=
    (publicEq p).symm ▸ tagBudget_setup _ _ _ _ _
  have hAddr₁ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ tagRoot (q p)) : P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  have hAddr₂ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ tagSecond (s p)) : P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  let dec (p : TagState × List NumberWord) := decideTag (tagFinish p)
  have hdec : Poly dec := tagFinish_poly.compose decideTag_poly
  let ck (p : QDom M K) := decide (C6fam dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))
  have hc (p : QDom M K) : ck p = dec (s p, (tagSecond (s p)).map (P1Batch.fetch (u p))) :=
    (evaluateTag_correct dims M ag p.val.1 p.val.2.1 p.val.2.2 p.property.1).symm
  obtain ⟨a, ha, T⟩ := prepareWitness (M := M) (K := K) hl setup hp
  obtain ⟨b, hb', T'⟩ := twoBatchCheck hb (fun p : QDom M K => send p.val) u q smallSize _
    tagRoot tagNext tagSecond dec ck T tagRoot_poly tagNext_poly tagSecond_poly hdec
    hs (hsmall.mono (fun p => (bounds p).1)) hAddr₁ (hsmall.mono (fun p => (bounds p).2)) hAddr₂ hc
  apply pack_budget (E := 5) (ha.add hb')
  exact T'.bound 1 (fun p => by dsimp only [u]; omega)

theorem progC6 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hl : LenHyp) (hf : FmtHypTags dims M ag) :
    ∃ (Rc : Prog Ltr) (c C : ℕ), ∀ p : QDom M K,
      P1Int.ProgAnswers Rc P1Dispatch.answer (P1Int.inputRegs Ltr.bit p.val.1 p.val.2.1 p.val.2.2)
        (decide (C6fam dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) (C * (budget c p.val + 1)) := by
  obtain ⟨c, h⟩ := taskC6 dims ag M K batchHyp hl hf
  obtain ⟨Rc, C, hRc⟩ := P1Dispatch.ofTask_tight' (fun p : QDom M K => p.val)
    (fun p => budget c p.val) (fun x u i => decide (C6fam dims ag x u i)) h
  exact ⟨Rc, c, C, hRc⟩

#print axioms taskC6
#print axioms progC6

end P1SolGreedy
