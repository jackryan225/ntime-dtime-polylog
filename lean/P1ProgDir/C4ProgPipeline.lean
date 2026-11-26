import P1ProgDir.C4ProgWords
import P1ProgDir.C4ProgBatch

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Batch (Req fetch total)

/-- The public data for a port: the number of intervals, the lane exponent,
the location count, the opposite port with type zero, the source port type,
and the padding bit as a word. -/
abbrev OwnerGeometry := (Word × Tally) × Word × Word × Word × Word

/-- Tape count, tape number and start-block section. -/
abbrev StartGeometry := Word × Word × SectionWord

/-- The ordinary value and the value when an owner link exists. The flag
selects the computed owner address in place of the second value. -/
abbrev Expectation := Word × Bool × Word

/-- Witness length, geometry, directory requests and addressed comparisons. -/
abbrev ReadPlan := Word × OwnerGeometry × StartGeometry × List Req × List (Req × Expectation)

def secondWord (l : List Word) : Word := l.tail.headD []

@[fun_prop] theorem easy_secondWord : Easy secondWord := by
  let f : List Word → Word := fun l => l.headD []
  have hf : Easy f := Iter.leader []
  have e : secondWord = (fun l : List Word => List.casesOn l [] (fun _ t => f t)) := by
    funext l
    cases l <;> rfl
  rw [e]
  exact Easy.listCase [] (Easy.snd.compose hf)

@[fun_prop] theorem poly_secondWord : Poly secondWord := easy_secondWord.poly

def ownerOK (p : Word × Word) : Bool :=
  bif wordLT ([], p.2) then !wordLT p else false

@[fun_prop] theorem poly_ownerOK : Poly ownerOK := by
  have hnot : Poly (fun b : Bool => !b) := (Easy.finite (fun b : Bool => !b)).poly
  unfold ownerOK
  fun_prop

theorem ownerOK_true (I raw : Word) :
    ownerOK (I, raw) = true ↔ 0 < value raw ∧ value raw ≤ value I := by
  unfold ownerOK
  cases h : wordLT ([], raw)
  · have hn : ¬0 < value raw := fun hp => by rw [(wordLT_true [] raw).mpr hp] at h; contradiction
    simp only [Bool.cond_false, Bool.false_eq_true, hn, false_and]
  · have hp := (wordLT_true [] raw).mp h
    change 0 < value raw at hp
    rw [Bool.cond_true, Bool.not_eq_true', ← Bool.not_eq_true, wordLT_true, not_lt]
    simp only [hp, true_and]

def ownerIndex (w : Word) : Word := wordSub (w, [true])

@[fun_prop] theorem poly_ownerIndex : Poly ownerIndex := by unfold ownerIndex; fun_prop

def clampReq (p : Word × Req) : Req := (wordMin (p.1, p.2.1), p.2.2)

@[fun_prop] theorem poly_clampReq : Poly clampReq := by unfold clampReq; fun_prop

theorem clampReq_address (m : Word) (q : Req) : P1Batch.bval (clampReq (m, q)).1 ≤ value m := by
  simp only [clampReq, bval_eq_value, value_wordMin, Nat.min_le_left]

def firstScan (p : ReadPlan) : ReadPlan × List Req :=
  (p, polyPush clampReq (p.1, p.2.2.2.1))

private theorem poly_firstScan : Poly firstScan := by
  have hp : Poly (polyPush clampReq) := Poly.push ([] : Word) (([], []) : Req) poly_clampReq
  unfold firstScan
  fun_prop

def farRequest (p : ReadPlan × List Word) : Req :=
  let plan := p.1
  let own := secondWord p.2
  let d := plan.2.2.1
  let i := add (Binary.school (ownerIndex own, d.1), d.2.1)
  bif ownerOK (plan.2.1.1.1, own) then wordFieldReq (plan.1, d.2.2, i) else ([], [])

@[fun_prop] theorem poly_farRequest : Poly farRequest := by unfold farRequest; fun_prop

theorem farRequest_address (p : ReadPlan) (w : List Word) :
    P1Batch.bval (farRequest (p, w)).1 ≤ value p.1 := by
  unfold farRequest
  dsimp only
  cases h : ownerOK (p.2.1.1.1, secondWord w)
  · simp only [h, Bool.cond_false, P1Batch.bval]
    exact Nat.zero_le _
  · simp only [h, Bool.cond_true]
    exact wordFieldReq_address _ _ _

private def secondScan (p : ReadPlan × List Word) : (ReadPlan × List Word) × List Req :=
  (p, [farRequest p])

private theorem poly_secondScan : Poly secondScan := by unfold secondScan; fun_prop

def ownerAddress (p : OwnerGeometry × Word × Word × Word) : Word :=
  let fmt := p.1
  let slot := wordPortSlot (fmt.1.2, p.2.1, p.2.2.2, fmt.2.2.2.1)
  let base := add (fmt.2.2.1, slot)
  let j := ownerIndex p.2.2.1
  let offset := add (base, Binary.school (fmt.2.1, j))
  add (false :: offset, fmt.2.2.2.2)

@[fun_prop] theorem poly_ownerAddress : Poly ownerAddress := by unfold ownerAddress; fun_prop

def expectedValue (p : (Bool × Word) × (Req × Expectation)) : Word :=
  let e := p.2.2
  bif p.1.1 then (bif e.2.1 then p.1.2 else e.2.2) else e.1

@[fun_prop] theorem poly_expectedValue : Poly expectedValue := by unfold expectedValue; fun_prop

def panelScan (p : (ReadPlan × List Word) × List Word) : List Word × List Req :=
  let plan := p.1.1
  let own := secondWord p.1.2
  let near := p.1.2.headD []
  let far := p.2.headD []
  let addr := ownerAddress (plan.2.1, near, own, far)
  let fields := plan.2.2.2.2
  (polyPush expectedValue ((ownerOK (plan.2.1.1.1, own), addr), fields),
    polyPush clampReq (plan.1, fields.map Prod.fst))

private theorem poly_panelScan : Poly panelScan := by
  have hh : Poly (fun l : List Word => l.headD []) := (Iter.leader ([] : Word)).poly
  have hp : Poly (polyPush clampReq) := Poly.push ([] : Word) (([], []) : Req) poly_clampReq
  have he := Poly.push (false, ([] : Word)) ((([], []) : Req), (([], false, []) : Expectation)) poly_expectedValue
  have hm : Poly (fun fields : List (Req × Expectation) => fields.map Prod.fst) := Easy.fst.mapping.poly
  unfold panelScan
  fun_prop

def wordsAgree (p : List Word × List Word) : Bool :=
  let paired := (cutLists (ruler p.1, zipSafe ([] : Word) ([] : Word) p)).1
  (paired.map wordEq).foldl (· && ·) true

@[fun_prop] theorem poly_wordsAgree : Poly wordsAgree := by
  have hf : Poly (fun p : List Bool × Bool => p.1.foldl (· && ·) p.2) := by
    apply Poly.fold_left (f := fun (p : Bool × Bool) => p.1 && p.2)
      (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly 1 0
    intros
    rfl
  have hz : Easy (fun p : List Word × List Word =>
      (cutLists (ruler p.1, zipSafe ([] : Word) ([] : Word) p)).1) := by
    exact (easy_cut ((show Easy (fun p : List Word × List Word => ruler p.1) from by fun_prop).pair
      (Easy.zipSafe _ _))).fstCompose
  unfold wordsAgree
  exact ((hz.poly.compose (Poly.maps _ poly_wordEq)).pair ((Easy.const (true : Bool)).poly)).compose hf

theorem wordsAgree_true (l r : List Word) (hl : l.length = r.length) :
    wordsAgree (l, r) = true ↔ l.map value = r.map value := by
  unfold wordsAgree cutLists
  dsimp only
  rw [ruler_length, hl, P1Batch.take_zipSafe [] [] l r hl]
  have h (l r : List Word) (b : Bool) (hl : l.length = r.length) :
      ((l.zip r).map wordEq).foldl (· && ·) b = true ↔ b = true ∧ l.map value = r.map value := by
    induction l generalizing r b with
    | nil =>
      cases r with
      | nil => simp
      | cons y r => simp at hl
    | cons x l ih =>
      cases r with
      | nil => simp at hl
      | cons y r =>
        rw [List.length_cons, List.length_cons, Nat.succ.injEq] at hl
        simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, ih r _ hl,
          Bool.and_eq_true, wordEq_true, List.cons.injEq, and_assoc]
  simpa only [true_and] using h l r true hl

def checkPlan (u : Word) (p : ReadPlan) : Bool :=
  let r₁ := (firstScan p).2.map (fetch u)
  let r₂ := [fetch u (farRequest (p, r₁))]
  let q := panelScan ((p, r₁), r₂)
  wordsAgree (q.1, q.2.map (fetch u))

def allFieldWidths (p : ReadPlan) : ℕ :=
  total p.2.2.2.1 + value p.2.2.1.2.2.2 + total (p.2.2.2.2.map Prod.fst)

theorem total_clamp (m : Word) (qs : List Req) : total (polyPush clampReq (m, qs)) = total qs := by
  simp only [total, polyPush, List.map_map, Function.comp_def, clampReq]

theorem farRequest_width (p : ReadPlan) (near : List Word) :
    total [farRequest (p, near)] ≤ value p.2.2.1.2.2.2 := by
  unfold farRequest
  dsimp only
  cases ownerOK (p.2.1.1.1, secondWord near)
  · exact Nat.zero_le _
  · simp only [Bool.cond_true, total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, wordFieldReq, bval_eq_value, le_refl]

/-- Compile the three scans using a compact public plan. The field-width
bound is independent of all fetched words, including malformed owner codes. -/
theorem checkPlan_task {X : Type} (u : X → Word) (small : X → ℕ) (p : X → ReadPlan)
    (hm : ∀ x, value (p x).1 = (u x).length)
    (hs : Dom small (fun x => size (p x))) (hw : Dom small (fun x => allFieldWidths (p x))) :
    ScanTask u small (fun x => send (p x, u x)) (fun x => send (checkPlan (u x) (p x))) := by
  let r₁ x := ((firstScan (p x)).2.map (fetch (u x)))
  let r₂ x := [fetch (u x) (farRequest (p x, r₁ x))]
  have first : Dom small (fun x => total (firstScan (p x)).2) := hw.mono fun x => by
    simp only [firstScan, total_clamp, allFieldWidths]
    omega
  obtain ⟨t₁, h₁⟩ := ScanTask.scan (u := u) poly_firstScan p hs first (by
    intro x q hq
    simp only [firstScan, polyPush] at hq
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
    rw [← hm x]
    exact clampReq_address _ _)
  have second : Dom small (fun x => total (secondScan (p x, r₁ x)).2) := hw.mono fun x =>
    (farRequest_width (p x) (r₁ x)).trans (by unfold allFieldWidths; omega)
  obtain ⟨t₂, h₂⟩ := ScanTask.scan (u := u) poly_secondScan (fun x => (p x, r₁ x)) h₁ second (by
    intro x q hq
    change q ∈ [farRequest (p x, r₁ x)] at hq
    rcases List.mem_singleton.mp hq with rfl
    rw [← hm x]
    exact farRequest_address _ _)
  let stages x := ((p x, r₁ x), r₂ x)
  have third : Dom small (fun x => total (panelScan (stages x)).2) := hw.mono fun x => by
    simp only [stages, panelScan, total_clamp, allFieldWidths]
    omega
  obtain ⟨t₃, h₃⟩ := ScanTask.scan (u := u) poly_panelScan stages h₂ third (by
    intro x q hq
    simp only [stages, panelScan, polyPush] at hq
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
    rw [← hm x]
    exact clampReq_address _ _)
  have t₄ := ScanTask.compact (u := u) poly_wordsAgree _ h₃
  have t₅ := ScanTask.dropWitness (u := u) (fun x => checkPlan (u x) (p x)) (Dom.const small 1)
  exact t₁.compose (t₂.compose (t₃.compose (t₄.compose t₅)))

end P1ProgDir.SolC4
