import P1ProgDir.SmallBatch
import P1ProgDir.FieldWords
import P1ProgDir.C14Family

namespace P1ProgDir.SolC14Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open OAI.Computability.IntegerMultiplication.Carry
open P1Wit P1ChkDir
open P1ProgDir.SolFieldWords P1ProgDir.SolSmallBatch P1ProgDir.SolOffsets
open P1ProgDir.SolSigned P1ProgDir.SolC14Reply
open P1ProgDir.SolBatchCore (atWord easy_atWord)

/-- Selector, guess count, interval count, width, lane exponent and section offsets. -/
abbrev Header := (Word × Word) × (Word × Tally × Tally) × (Word × Word × Word)
abbrev Middle := List Word × Header
abbrev ReplyState := Bool × Bool × Word × Tally

def active (p : Header) : Bool := more (p.1.2, p.1.1)

theorem easy_active : Easy active :=
  easy_more ((Easy.fst.compose Easy.snd).pair (Easy.fst.compose Easy.fst))

def firstReq (p : Header) : P1Batch.Req :=
  fieldRequest p.2.2.2.2 (born p.2.1.2.1.length) p.1.1

theorem poly_firstReq : Poly firstReq := by
  unfold firstReq
  apply poly_fieldRequest
  · exact Poly.identity.sndCompose.sndCompose.sndCompose.sndCompose
  · exact Poly.identity.sndCompose.fstCompose.sndCompose.fstCompose.compose easy_chart.poly
  · exact Poly.identity.fstCompose.fstCompose

def first (p : Header) : List P1Batch.Req × Header :=
  ((bif active p then [firstReq p] else []), p)

theorem poly_first : Poly first :=
  (easy_active.poly.choose
    ((poly_firstReq.pair (Code.Poly.const ([] : List P1Batch.Req))).compose Poly.cons)
    (Code.Poly.const [])).pair Poly.identity

def owner (m : Middle) : Word := m.1.headD []

def validOwner (m : Middle) : Bool :=
  more (owner m, []) && !more (owner m, m.2.2.1.1)

theorem easy_owner : Easy owner := Easy.fst.compose (Iter.leader [])

theorem easy_validOwner : Easy validOwner := by
  have hI : Easy (fun m : Middle => m.2.2.1.1) :=
    Easy.snd.compose (Easy.snd.compose (Easy.fst.compose Easy.fst))
  exact ((easy_more (easy_owner.pair (Easy.const []))).pair (easy_more (easy_owner.pair hI))).compose
    (Easy.finite (fun p : Bool × Bool => p.1 && !p.2))

theorem validOwner_iff (m : Middle) :
    validOwner m = true ↔ 0 < value (owner m) ∧ value (owner m) ≤ value m.2.2.1.1 := by
  have h (b : Bool) : (!b) = true ↔ ¬ b = true := by cases b <;> decide
  simp only [validOwner, Bool.and_eq_true, h, more_lt, value_nil, not_lt]

def startIndex (r t : ℕ) (m : Middle) : Word :=
  add (scale r (decMagnitude (owner m)), born t)

theorem poly_startIndex (r t : ℕ) : Poly (startIndex r t) :=
  poly_add (poly_scale r (easy_owner.poly.compose easy_decMagnitude.poly)) (Code.Poly.const (born t))

def startReq (r t : ℕ) (m : Middle) : P1Batch.Req :=
  fieldRequest m.2.2.2.1 (born m.2.2.1.2.1.length) (startIndex r t m)

def prevIndex (r t d : ℕ) (m : Middle) : Word :=
  add (scale 3 (startIndex r t m), born d)

def prevReq (r t d : ℕ) (m : Middle) : P1Batch.Req :=
  fieldRequest m.2.2.2.2.1 (born m.2.2.1.2.1.length) (prevIndex r t d m)

theorem poly_startReq (r t : ℕ) : Poly (startReq r t) :=
  poly_fieldRequest Poly.identity.sndCompose.sndCompose.sndCompose.fstCompose
    (Poly.identity.sndCompose.sndCompose.fstCompose.sndCompose.fstCompose.compose easy_chart.poly)
    (poly_startIndex r t)

theorem poly_prevReq (r t d : ℕ) : Poly (prevReq r t d) :=
  poly_fieldRequest Poly.identity.sndCompose.sndCompose.sndCompose.sndCompose.fstCompose
    (Poly.identity.sndCompose.sndCompose.fstCompose.sndCompose.fstCompose.compose easy_chart.poly)
    (poly_add (poly_scale 3 (poly_startIndex r t)) (Code.Poly.const (born d)))

def secondReqs (r t : ℕ) (m : Middle) : List P1Batch.Req :=
  [startReq r t m, prevReq r t 0 m, prevReq r t 1 m, prevReq r t 2 m]

theorem poly_secondReqs (r t : ℕ) : Poly (secondReqs r t) :=
  poly_list [startReq r t, prevReq r t 0, prevReq r t 1, prevReq r t 2] (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact poly_startReq r t
    all_goals exact poly_prevReq r t _)

def second (r t : ℕ) (m : Middle) : List P1Batch.Req × ReplyState :=
  ((bif validOwner m then secondReqs r t m else []),
    active m.2, validOwner m, m.2.1.1, m.2.2.1.2.2)

theorem poly_second (r t : ℕ) : Poly (second r t) := by
  apply (easy_validOwner.poly.choose (poly_secondReqs r t) (Code.Poly.const [])).pair
  exact (Poly.identity.sndCompose.compose easy_active.poly).pair
    (easy_validOwner.poly.pair (Poly.identity.sndCompose.fstCompose.fstCompose.pair
      Poly.identity.sndCompose.sndCompose.fstCompose.sndCompose.sndCompose))

def reply (p : List Word × ReplyState) : Bool :=
  !p.2.1 || (p.2.2.1 && windowTest
    (false :: p.2.2.2.1, quotient (p.2.2.2.2, atWord 0 p.1), atWord 1 p.1, atWord 2 p.1, atWord 3 p.1))

theorem easy_reply : Easy reply := by
  let P := List Word × ReplyState
  have ha : Easy (fun p : P => p.2.1) := Easy.snd.compose Easy.fst
  have hv : Easy (fun p : P => p.2.2.1) := Easy.snd.compose (Easy.snd.compose Easy.fst)
  have hq : Easy (fun p : P => p.2.2.2.1) := Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
  have hh : Easy (fun p : P => p.2.2.2.2) := Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd))
  have hs (n : ℕ) : Easy (fun p : P => atWord n p.1) := Easy.fst.compose (easy_atWord n)
  have ht := (((Easy.const false).pair hq).compose Easy.cons).pair
    (((hh.pair (hs 0)).compose easy_quotient).pair ((hs 1).pair ((hs 2).pair (hs 3))))
  exact (ha.pair (hv.pair (ht.compose easy_windowTest))).compose
    (Easy.finite (fun p : Bool × Bool × Bool => !p.1 || (p.2.1 && p.2.2)))

structure Fits (D : Dims) (r t : ℕ) (p : Header) (w : Word) : Prop where
  guessCount : value p.1.2 = D.nGB
  blocks : value p.2.1.1 = D.I
  width : p.2.1.2.1.length = D.bigW
  lanes : 2 ^ p.2.1.2.2.length = D.N
  start : value p.2.2.1 = D.off secStart
  prev : value p.2.2.2.1 = D.off secPrev
  guess : value p.2.2.2.2 = D.off secGuess
  tapes : r = D.r
  inputTape : t < r
  witness : guessEnd D ≤ w.length

variable {D : Dims} {r t : ℕ} {p : Header} {w : Word}

theorem Fits.wordWidth (h : Fits D r t p w) : value (born p.2.1.2.1.length) = D.bigW :=
  (birthValue _).trans h.width

theorem first_total : Dom (fun p : Header => size p) (fun p => P1Batch.total (first p).1) := by
  apply (Dom.base _).mono
  intro p
  have hw : p.2.1.2.1.length ≤ size p := by simp only [size_prod, size_tally]; omega
  cases h : active p <;>
    simp only [first, h, Bool.cond_true, Bool.cond_false, P1Batch.total, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, firstReq, fieldRequest, P1Batch.bval_eq_value, birthValue,
      size_prod, size_tally] <;> omega

theorem second_total (r t : ℕ) :
    Dom (fun m : Middle => size m) (fun m => P1Batch.total (second r t m).1) := by
  apply ((Dom.const _ 4).mul (Dom.base _)).mono
  intro m
  have hw : m.2.2.1.2.1.length ≤ size m := by simp only [size_prod, size_tally]; omega
  cases h : validOwner m <;>
    simp only [second, h, Bool.cond_true, Bool.cond_false, P1Batch.total, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, secondReqs, startReq, prevReq, fieldRequest, P1Batch.bval_eq_value,
      birthValue, size_prod, size_tally] <;> omega

theorem active_iff (h : Fits D r t p w) : active p = true ↔ value p.1.1 < D.nGB := by
  rw [active, more_lt, h.guessCount]

theorem first_fits (h : Fits D r t p w) (q : P1Batch.Req) (hq : q ∈ (first p).1) :
    P1Batch.bval q.1 + P1Batch.bval q.2 ≤ w.length := by
  by_cases hi : active p = true
  · simp only [first, hi, Bool.cond_true, List.mem_singleton] at hq
    subst q
    exact fieldRequest_fits h.guess (h.wordWidth.trans (width_guess D).symm)
      ((active_iff h).mp hi) (by decide) h.witness
  · have hi' : active p = false := by cases e : active p <;> simp_all
    simp only [first, hi', Bool.cond_false, List.not_mem_nil] at hq

theorem owner_read (h : Fits D r t p w) (hi : active p = true) :
    value (owner (readPlan first p w)) = rdGuess D w (value p.1.1) := by
  simp only [owner, readPlan, first, hi, Bool.cond_true, List.map_cons, List.map_nil, List.headD_cons]
  exact fieldRequest_read w _ _ _ h.guess (h.wordWidth.trans (width_guess D).symm)

theorem startIndex_value (r t : ℕ) (m : Middle) (h : 0 < value (owner m)) :
    value (startIndex r t m) = (value (owner m) - 1) * r + t := by
  have e := decMagnitude_value (owner m) h
  have he : value (decMagnitude (owner m)) = value (owner m) - 1 := by omega
  rw [startIndex, add_val, scale_exact, he, birthValue, Nat.mul_comm]

theorem prevIndex_value (r t d : ℕ) (m : Middle) :
    value (prevIndex r t d m) = value (startIndex r t m) * 3 + d := by
  rw [prevIndex, add_val, scale_exact, birthValue, Nat.mul_comm]

theorem index_lt (h : Fits D r t p w) (m : Middle) (hm : m.2 = p)
    (hv : validOwner m = true) : value (startIndex r t m) < D.I * D.r := by
  obtain ⟨h₀, hI⟩ := (validOwner_iff m).mp hv
  rw [hm, h.blocks] at hI
  rw [startIndex_value r t m h₀, ← h.tapes]
  have htr := h.inputTape
  calc
    _ < (value (owner m) - 1 + 1) * r := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem second_fits (h : Fits D r t p w) (q : P1Batch.Req)
    (hq : q ∈ (second r t (readPlan first p w)).1) :
    P1Batch.bval q.1 + P1Batch.bval q.2 ≤ w.length := by
  let m := readPlan first p w
  change q ∈ (second r t m).1 at hq
  by_cases hv : validOwner m = true
  · have hidx := index_lt h m rfl hv
    have hstart : P1Batch.bval (startReq r t m).1 + P1Batch.bval (startReq r t m).2 ≤ w.length :=
      fieldRequest_fits h.start (h.wordWidth.trans (width_start D).symm) hidx (by decide) h.witness
    have hprev (d : ℕ) (hd : d < 3) :
        P1Batch.bval (prevReq r t d m).1 + P1Batch.bval (prevReq r t d m).2 ≤ w.length := by
      apply fieldRequest_fits h.prev (h.wordWidth.trans (width_prev D).symm) _ (by decide) h.witness
      change value (prevIndex r t d m) < D.I * D.r * 3
      rw [prevIndex_value]
      omega
    simp only [second, hv, Bool.cond_true, secondReqs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hstart
    · exact hprev 0 (by decide)
    · exact hprev 1 (by decide)
    · exact hprev 2 (by decide)
  · have hv' : validOwner m = false := by cases e : validOwner m <;> simp_all
    simp only [second, hv', Bool.cond_false, List.not_mem_nil] at hq

theorem reply_iff {K : Type} (tape : K ≃ Fin D.r) (k : K)
    (h : Fits D r t p w) (ht : t = tape k) :
    reply (readPlan (second r t) (readPlan first p w) w) = true ↔
      C14F D tape k (fun q => ((q : ℕ) : ℤ)) w (value p.1.1) := by
  let m := readPlan first p w
  by_cases hi : active p = true
  · let Q : Fin D.nGB := ⟨value p.1.1, (active_iff h).mp hi⟩
    have ho := owner_read h hi
    by_cases hv : validOwner m = true
    · obtain ⟨h₀, hI⟩ := (validOwner_iff m).mp hv
      have hval : value (startIndex r t m) = (rdGuess D w Q - 1) * D.r + tape k := by
        rw [startIndex_value r t m h₀, h.tapes, ht]
        change value (owner (readPlan first p w)) = _ at ho
        rw [ho]
      have hb : signedValue (quotient (p.2.1.2.2, P1Batch.fetch w (startReq r t m))) =
          bigOf D.N (unzigzag (rdStart D w (rdGuess D w Q - 1) (tape k))) := by
        rw [quotient_value, ← Int.natCast_pow, h.lanes, signedValue]
        have e := fieldRequest_read w p.2.2.1 (born p.2.1.2.1.length) (startIndex r t m)
          h.start (h.wordWidth.trans (width_start D).symm)
        change value (P1Batch.fetch w (startReq r t m)) = _ at e
        rw [e, hval] <;> rfl
      have hp (d : ℕ) :
          value (P1Batch.fetch w (prevReq r t d m)) = rdPrev D w (rdGuess D w Q - 1) (tape k) d := by
        have e := fieldRequest_read w p.2.2.2.1 (born p.2.1.2.1.length) (prevIndex r t d m)
          h.prev (h.wordWidth.trans (width_prev D).symm)
        change value (P1Batch.fetch w (prevReq r t d m)) = _ at e
        rw [e, prevIndex_value, hval] <;> rfl
      change reply (readPlan (second r t) m w) = true ↔ _
      simp only [reply, readPlan, second, hv, Bool.cond_true, secondReqs, List.map_cons, List.map_nil]
      change (!active p || (true && windowTest (false :: p.1.1, _, _, _, _))) = true ↔ _
      rw [hi]
      simp only [Bool.not_true, Bool.true_and, Bool.false_or]
      exact P1ProgDir.SolC14Family.in_range D tape k w Q _ _ _ _ _
        (by rw [signedValue_cons]; rfl) (by rw [← ho]; exact h₀)
        (by rw [← ho]; exact hI.trans_eq h.blocks) hb (hp 0) (hp 1) (hp 2)
    · have hv' : validOwner m = false := by cases e : validOwner m <;> simp_all
      change reply (readPlan (second r t) m w) = true ↔ _
      simp only [reply, readPlan, second, hv', Bool.false_and, Bool.or_false]
      change (!active p) = true ↔ _
      rw [hi]
      simp only [Bool.not_true, Bool.false_eq_true, false_iff]
      intro hc
      obtain ⟨h₀, hI, _⟩ := (P1ProgDir.SolC14Family.c14_family_readback D tape k
        (fun q => ((q : ℕ) : ℤ)) w Q).mp hc
      exact hv ((validOwner_iff m).mpr ⟨by rw [ho]; exact h₀, by rw [ho]; exact hI.trans_eq h.blocks.symm⟩)
  · have he : D.nGB ≤ value p.1.1 := Nat.le_of_not_gt (fun hlt => hi ((active_iff h).mpr hlt))
    have hi' : active p = false := by cases e : active p <;> simp_all
    refine iff_of_true ?_ (C14F_out D tape k _ w he)
    change (!active p || _) = true
    rw [hi']
    rfl

end P1ProgDir.SolC14Batch
