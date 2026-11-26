import P1SolGreedy.GreedyReaders
import P1ChkFinal.BatchLink
import P1Dispatch.TaskBridge
import OAI.Computability.IntegerMultiplication.Carry.Accum
import OAI.Computability.IntegerMultiplication.Code.Iter

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

/-- The three requests depend on the public layout and family index. -/
def reqC9 (dims : ℕ → Dims) (z : IndexWord) : List P1Batch.Req :=
  let D := dims (P1Batch.bval z.1)
  let ℓ := P1Batch.bval z.2
  if ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true then
    let Y := (D.lv ℓ).bases - 1
    [fieldReq D (secLev ℓ .layout) 0,
      fieldReq D (secLev ℓ .energy) (Y * 2 + eCode true),
      fieldReq D (secLev ℓ .energy) (Y * 2 + eCode false)]
  else []

def decideC9 (z : IndexWord × List (List Bool)) : Bool :=
  let l := Code.Iter.pick ([] : List Bool) (z.2, tally 0)
  let e₀ := Code.Iter.pick ([] : List Bool) (z.2, tally 1)
  let e₁ := Code.Iter.pick ([] : List Bool) (z.2, tally 2)
  let zero := Carry.lt_ (l, [true])
  bif Carry.lt_ (l, [false, true]) then
    (bif Carry.lt_ (e₀, e₁) then !zero else zero)
  else false

theorem decideC9_poly : Poly decideC9 := by
  unfold decideC9
  fun_prop

theorem value_eq_bitsVal (w : List Bool) : Bits.value w = bitsVal w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [Bits.value_cons, bitsVal, ih, Bits.digit, Bool.false_eq_true,
      ite_false, ite_true]

theorem decideC9_reads (z : IndexWord) (l e₀ e₁ : List Bool) :
    decideC9 (z, [l, e₀, e₁]) =
      decide (bitsVal l < 2 ∧
        decide (bitsVal l = 1) = decide (bitsVal e₀ < bitsVal e₁)) := by
  unfold decideC9
  dsimp only
  have h₀ : Code.Iter.pick ([] : List Bool) ([l, e₀, e₁], tally 0) = l := rfl
  have h₁ : Code.Iter.pick ([] : List Bool) ([l, e₀, e₁], tally 1) = e₀ := rfl
  have h₂ : Code.Iter.pick ([] : List Bool) ([l, e₀, e₁], tally 2) = e₁ := rfl
  simp only [h₀, h₁, h₂, Carry.lt_r, value_eq_bitsVal]
  change (bif decide (bitsVal l < 2) then
      (bif decide (bitsVal e₀ < bitsVal e₁) then !decide (bitsVal l < 1) else decide (bitsVal l < 1))
      else false) = _
  by_cases h : bitsVal l < 2
  · by_cases hzero : bitsVal l < 1
    · have hn : bitsVal l ≠ 1 := by omega
      by_cases he : bitsVal e₀ < bitsVal e₁ <;> simp [h, hzero, hn, he]
    · have hn : bitsVal l = 1 := by omega
      by_cases he : bitsVal e₀ < bitsVal e₁ <;> simp [hn, he]
  · simp [h]

open Classical in
theorem decideC9_correct (dims : ℕ → Dims) (x u ρ : List Bool) :
    decide (C9fam dims x u (P1Batch.bval ρ)) =
      decideC9 ((bin x.length, ρ), (reqC9 dims (bin x.length, ρ)).map (P1Batch.fetch u)) := by
  by_cases h : P1Batch.bval ρ ≤ (dims x.length).top ∧ ((dims x.length).lv (P1Batch.bval ρ)).shrink = true
  · simp only [reqC9, bval_bin, h.1, h.2, true_and, ite_true, List.map_cons, List.map_nil, decideC9_reads,
      ← readField_eq, C9fam, true_implies, C9chk, rdLayout, rdEnergy]
    rw [decide_eq_decide]
    rfl
  · simp only [C9fam, h, false_implies, decide_true, reqC9, bval_bin, ite_false, List.map_nil]
    rfl

abbrev C9Context := NumberWord × BaseRow

def setupC9 (q : PublicFmt × NumberWord) : C9Context :=
  (q.1.2.1, selectRow defaultRow (q.2, q.1.2.2))

theorem setupC9_poly : Poly setupC9 := by
  have h : Poly (selectRow defaultRow) := selectRow_poly _
  unfold setupC9
  fun_prop

def c9RawRequests (r : BaseRow) : List P1Batch.Req :=
  let Y := Carry.sub0 (r.2.1, [true])
  bif r.1 then
    [fieldWords (rowSection .layout r, []),
      fieldWords (rowSection .energy r, false :: Y),
      fieldWords (rowSection .energy r, true :: Y)]
  else []

@[fun_prop] theorem c9RawRequests_poly : Poly c9RawRequests := by
  unfold c9RawRequests
  dsimp only
  fun_prop

def c9Requests (q : C9Context) : List P1Batch.Req := clipRequests (q.1, c9RawRequests q.2)

theorem c9Requests_poly : Poly c9Requests := by
  unfold c9Requests
  fun_prop

theorem bval_sub0 (x y : NumberWord) :
    P1Batch.bval (Carry.sub0 (x, y)) = P1Batch.bval x - P1Batch.bval y := by
  rw [← value_bval, Carry.sub0_v, value_bval, value_bval]

theorem c9RawRequests_numbers (dims : ℕ → Dims) (M : ℕ → ℕ) (z : IndexWord) :
    (c9RawRequests (setupC9 (formatIndex dims M z)).2).map requestNumbers =
      (reqC9 dims z).map requestNumbers := by
  let D := dims (P1Batch.bval z.1)
  let ℓ := P1Batch.bval z.2
  let last := (D.lv ℓ).bases - 1
  change (c9RawRequests (selectRow defaultRow (z.2, (fmtGreedy D (M (P1Batch.bval z.1))).2.2))).map
    requestNumbers = (reqC9 dims z).map requestNumbers
  rw [selectRow_level]
  change (c9RawRequests (if ℓ ≤ D.top then levelRow D ℓ else defaultRow)).map requestNumbers =
    (if ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true then
      [fieldReq D (secLev ℓ .layout) 0, fieldReq D (secLev ℓ .energy) (last * 2 + eCode true),
        fieldReq D (secLev ℓ .energy) (last * 2 + eCode false)] else []).map requestNumbers
  by_cases h : ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true
  · rw [ite_eq_left h.1, ite_eq_left h]
    let Y := Carry.sub0 ((levelRow D ℓ).2.1, [true])
    have hY : P1Batch.bval Y = last := by
      change P1Batch.bval (Carry.sub0 (bin (D.lv ℓ).bases, [true])) = _
      rw [bval_sub0, bval_bin]
      rfl
    have ht : P1Batch.bval (false :: Y) = last * 2 + eCode true := by
      change 0 + 2 * P1Batch.bval Y = last * 2 + 0
      rw [hY]
      omega
    have hf : P1Batch.bval (true :: Y) = last * 2 + eCode false := by
      change 1 + 2 * P1Batch.bval Y = last * 2 + 1
      rw [hY]
      omega
    have hsh : (levelRow D ℓ).1 = true := h.2
    unfold c9RawRequests
    change ((bif (levelRow D ℓ).1 then
        [fieldWords (rowSection .layout (levelRow D ℓ), []),
          fieldWords (rowSection .energy (levelRow D ℓ), false :: Y),
          fieldWords (rowSection .energy (levelRow D ℓ), true :: Y)] else []).map requestNumbers) = _
    simp only [hsh, Bool.cond_true, List.map_cons, List.map_nil, requestNumbers_rowField, ht, hf]
    rfl
  · rw [ite_eq_right h]
    by_cases hℓ : ℓ ≤ D.top
    · rw [ite_eq_left hℓ]
      have hs : (levelRow D ℓ).1 = false := Bool.eq_false_iff.mpr (fun ht => h ⟨hℓ, ht⟩)
      simp only [c9RawRequests, hs, Bool.cond_false, List.map_nil]
    · rw [ite_eq_right hℓ]
      rfl

theorem c9Requests_total (dims : ℕ → Dims) (M : ℕ → ℕ) (z : IndexWord) :
    P1Batch.total (c9Requests (setupC9 (formatIndex dims M z))) ≤
      3 * size (setupC9 (formatIndex dims M z)) := by
  have he := total_of_requestNumbers (c9RawRequests_numbers dims M z)
  unfold c9Requests
  rw [clipRequests_total, he]
  let D := dims (P1Batch.bval z.1)
  let ℓ := P1Batch.bval z.2
  by_cases h : ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true
  · have hl : (setupC9 (formatIndex dims M z)).2 = levelRow D ℓ := by
      change selectRow defaultRow (z.2, (fmtGreedy D (M (P1Batch.bval z.1))).2.2) = levelRow D ℓ
      rw [selectRow_level, ite_eq_left h.1]
    have h₀ := width_le_size_levelRow D ℓ .layout
    have h₁ := width_le_size_levelRow D ℓ .energy
    have h' : P1Batch.bval z.2 ≤ (dims (P1Batch.bval z.1)).top ∧
        ((dims (P1Batch.bval z.1)).lv (P1Batch.bval z.2)).shrink = true := h
    have hw : size (levelRow D ℓ) ≤ size (setupC9 (formatIndex dims M z)) :=
      hl ▸ size_snd_le (setupC9 (formatIndex dims M z))
    simp only [reqC9, h'.1, h'.2, true_and, ite_true, P1Batch.total, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, fieldReq, bval_bin]
    change D.width (secLev ℓ .layout) + (D.width (secLev ℓ .energy) + (D.width (secLev ℓ .energy) + 0)) ≤ _
    omega
  · have h' : ¬(P1Batch.bval z.2 ≤ (dims (P1Batch.bval z.1)).top ∧
        ((dims (P1Batch.bval z.1)).lv (P1Batch.bval z.2)).shrink = true) := h
    simp only [reqC9, h', ite_false, P1Batch.total, List.map_nil, List.sum_nil, Nat.zero_le]

end P1SolGreedy.SolDemand

namespace P1SolGreedy

open SolDemand Classical

/-- The Task form of D8 for family 8, with only public format data as advice. -/
theorem taskC9 (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypGreedy dims M) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C9fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let setup (z : IndexWord) := setupC9 (formatIndex dims M z)
  have hp : Poly setup := (formatIndex_poly dims M hf).compose setupC9_poly
  have hs : Dom smallSize (fun p : QDom M K => size (setup (SetupIdx p))) :=
    (hp.length.map SetupIdx).sub index_size
  have ht : Dom smallSize (fun p : QDom M K => P1Batch.total (c9Requests (setup (SetupIdx p)))) :=
    ((Dom.const _ 3).mul hs).mono (fun p => c9Requests_total dims M (SetupIdx p))
  have hlen (p : QDom M K) : P1Batch.bval (setup (SetupIdx p)).1 = p.val.2.1.length := by
    change P1Batch.bval (bin (M (P1Batch.bval (bin p.val.1.length)))) = p.val.2.1.length
    rw [bval_bin, bval_bin, p.property.1]
  let dec (p : C9Context × List (List Bool)) := decideC9 (([], []), p.2)
  have hdec : Poly dec := (Code.Poly.pair (Code.Poly.const _) (Easy.snd.poly)).compose decideC9_poly
  apply taskOneBatch hb hl setup hp c9Requests c9Requests_poly dec hdec _ ht
  · intro p r hr
    have he := clipRequests_bound _ _ hr
    rwa [hlen p] at he
  · intro p
    let z := SetupIdx p
    have hreq : (c9Requests (setup z)).map (P1Batch.fetch p.val.2.1) =
        (reqC9 dims z).map (P1Batch.fetch p.val.2.1) := by
      unfold c9Requests
      rw [clipRequests_fetch _ _ (hlen p)]
      exact fetches_of_requestNumbers _ (c9RawRequests_numbers dims M z)
    change decide (C9fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)) =
      decideC9 (([], []), (c9Requests (setup z)).map (P1Batch.fetch p.val.2.1))
    rw [hreq]
    exact decideC9_correct dims p.val.1 p.val.2.1 p.val.2.2

/-- The raw-register form of D8 for family 8. -/
theorem progC9 (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hl : LenHyp) (hf : FmtHypGreedy dims M) :
    ∃ (Rc : Prog Ltr) (c C : ℕ), ∀ p : QDom M K,
      P1Int.ProgAnswers Rc P1Dispatch.answer (P1Int.inputRegs Ltr.bit p.val.1 p.val.2.1 p.val.2.2)
        (decide (C9fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) (C * (budget c p.val + 1)) := by
  obtain ⟨c, h⟩ := taskC9 dims M K batchHyp hl hf
  obtain ⟨Rc, C, hRc⟩ := P1Dispatch.ofTask_tight' (fun p : QDom M K => p.val)
    (fun p => budget c p.val) (fun x u i => decide (C9fam dims x u i)) h
  exact ⟨Rc, c, C, hRc⟩

#print axioms taskC9
#print axioms progC9

end P1SolGreedy
