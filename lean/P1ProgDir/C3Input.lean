import P1ProgDir.C3Scan
import P1ProgDir.C2Trits
import P1ProgDir.C14Reply

namespace P1ProgDir.SolC3Input

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Wit P1ChkDir
open P1ProgDir.SolGeometry P1ProgDir.SolFieldWords P1ProgDir.SolOffsets P1ProgDir.SolSigned
open P1ProgDir.SolSmallBatch P1ProgDir.SolC2Trits

/-- The interval count and three section starts, then the field width and lane exponent. -/
abbrev Layout := (Word × Word × Word × Word) × Tally × Tally
abbrev Header := Word × Layout
abbrev Output := List Word × Header

abbrev ScanArgs := Bool × Bool × Word × Tally × SolC3Scan.Context

def active (r : ℕ) (p : Header) : Bool := more (scale (6 * r) p.2.1.1, p.1)
def direction (p : Header) : Bool := sign p.1
def fieldIdx (p : Header) : Word := magnitude p.1
def flatIdx (p : Header) : Word := qword (p := 3) (fieldIdx p)

def startReq (p : Header) : P1Batch.Req :=
  fieldRequest p.2.1.2.1 (born p.2.2.1.length) (flatIdx p)

def linkReq (p : Header) : P1Batch.Req :=
  fieldRequest (bif direction p then p.2.1.2.2.2 else p.2.1.2.2.1)
    (born p.2.2.1.length) (fieldIdx p)

def plan (r : ℕ) (p : Header) : List P1Batch.Req × Header :=
  ((bif active r p then [startReq p, linkReq p] else []), p)

theorem easy_active (r : ℕ) : Easy (active r) :=
  easy_more ((easy_scale _ (Easy.snd.compose (Easy.fst.compose Easy.fst))).pair Easy.fst)

theorem easy_direction : Easy direction := Easy.fst.compose easy_sign
theorem easy_fieldIdx : Easy fieldIdx := Easy.fst.compose easy_magnitude
theorem easy_flatIdx : Easy flatIdx := easy_qword easy_fieldIdx

theorem poly_plan (r : ℕ) : Poly (plan r) := by
  have hwidth : Poly (fun p : Header => born p.2.2.1.length) :=
    Poly.identity.sndCompose.sndCompose.fstCompose.compose easy_chart.poly
  have hs : Poly startReq := poly_fieldRequest Poly.identity.sndCompose.fstCompose.sndCompose.fstCompose
    hwidth easy_flatIdx.poly
  have ho : Poly (fun p : Header => bif direction p then p.2.1.2.2.2 else p.2.1.2.2.1) :=
    easy_direction.poly.choose Poly.identity.sndCompose.fstCompose.sndCompose.sndCompose.sndCompose
      Poly.identity.sndCompose.fstCompose.sndCompose.sndCompose.fstCompose
  have hl : Poly linkReq := poly_fieldRequest ho hwidth easy_fieldIdx.poly
  have hrs : Poly (fun p : Header => [startReq p, linkReq p]) :=
    (hs.pair ((hl.pair (Code.Poly.const ([] : List P1Batch.Req))).compose Poly.cons)).compose Poly.cons
  exact ((easy_active r).poly.choose hrs (Code.Poly.const [])).pair Poly.identity

def intervalWord (r : ℕ) [NeZero r] (p : Header) : Word := qword (p := r) (flatIdx p)
def tapeWord (r : ℕ) [NeZero r] (p : Header) : Word := modWord r (flatIdx p)
def deltaWord (p : Header) : Word := modWord 3 (fieldIdx p)

def adjustBlock (p : Word × Word) : Word :=
  bif SolC14Reply.zeroWord p.1 then dec p.2 else
    bif SolC2Reply.eqWord (p.1, [true]) then p.2 else inc p.2

theorem easy_adjustBlock : Easy adjustBlock := by
  have h₀ : Easy (fun p : Word × Word => SolC14Reply.zeroWord p.1) :=
    Easy.fst.compose SolC14Reply.easy_zeroWord
  have h₁ : Easy (fun p : Word × Word => SolC2Reply.eqWord (p.1, [true])) :=
    (Easy.fst.pair (Easy.const ([true] : Word))).compose SolC2Reply.easy_eqWord
  have hp : Easy (fun p : Word × Word => bif SolC2Reply.eqWord (p.1, [true]) then p.2 else inc p.2) :=
    (h₁.pair Easy.identity).compose (Easy.ifst (Easy.snd.compose easy_inc) Easy.snd)
  exact (h₀.pair Easy.identity).compose (Easy.ifst hp (Easy.snd.compose SolSigned.easy_dec))

theorem adjustBlock_value (δ b : Word) (h : value δ < 3) :
    signedValue (adjustBlock (δ, b)) = signedValue b - 1 + (value δ : ℤ) := by
  have hv : value δ = 0 ∨ value δ = 1 ∨ value δ = 2 := by omega
  rcases hv with h₀ | h₁ | h₂
  · have e := (SolC14Reply.zeroWord_eq δ).mpr h₀
    simp only [adjustBlock, e, Bool.cond_true, dec_value, h₀, Nat.cast_zero, add_zero]
  · have e₀ : SolC14Reply.zeroWord δ = false := by
      cases e : SolC14Reply.zeroWord δ
      · rfl
      · have z := (SolC14Reply.zeroWord_eq δ).mp e
        omega
    have e₁ := (SolC2Reply.eqWord_eq (δ, [true])).mpr h₁
    simp only [adjustBlock, e₀, e₁, Bool.cond_false, Bool.cond_true, h₁, Nat.cast_one]
    omega
  · have e₀ : SolC14Reply.zeroWord δ = false := by
      cases e : SolC14Reply.zeroWord δ
      · rfl
      · have z := (SolC14Reply.zeroWord_eq δ).mp e
        omega
    have e₁ : SolC2Reply.eqWord (δ, [true]) = false := by
      cases e : SolC2Reply.eqWord (δ, [true])
      · rfl
      · have z := (SolC2Reply.eqWord_eq (δ, [true])).mp e
        change value δ = 1 at z
        omega
    simp only [adjustBlock, e₀, e₁, Bool.cond_false, inc_value, h₂, Nat.cast_ofNat]
    omega

def cutOffset (r : ℕ) [NeZero r] (p : Header) : Tally :=
  tally (value (tapeWord r p) * p.2.2.1.length)

theorem poly_cutOffset (r : ℕ) [NeZero r] : Poly (cutOffset r) := by
  let width (p : Header) := p.2.2.1
  let t (p : Header) := tapeWord r p
  let off (p : Header) := product (t p, born (width p).length)
  have ht : Poly t := easy_flatIdx.poly.compose (easy_modWord r).poly
  have hw : Poly width := Poly.identity.sndCompose.sndCompose.fstCompose
  have ho : Poly off := poly_mul ht (hw.compose easy_chart.poly)
  have hval (p : Header) : P1Batch.bval (off p) = value (t p) * (width p).length := by
    rw [P1Batch.bval_eq_value, exact_prod, birthValue]
  have hdom : Dom (fun p : Header => size p)
      (fun p => P1Batch.bval (off p) + (off p).length) := by
    apply (((Dom.const _ r).mul hw.length).add ho.length).mono
    intro p
    have hv : value (t p) ≤ r := by
      exact ((modWord_value r _).trans_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne r)))).le
    have hmul := Nat.mul_le_mul_right (width p).length hv
    rw [hval, size_tally, size_word]
    have ht' : r * (width p).length ≤ r * (2 * (width p).length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨α, hα, hpre⟩ := ho
  refine ⟨_, hα.add hdom, (hpre.compose (P1Batch.countdown.on off)).conform
    (fun _ => rfl) (fun _ => rfl) (fun p => ?_)⟩
  rw [hval] <;> rfl

def storedLink (p : Output) : Word := SolBatchCore.atWord 1 p.1

def probe (p : Output) : Word :=
  adjustBlock (deltaWord p.2, quotient (p.2.2.2.2, SolBatchCore.atWord 0 p.1))

def scanWithOffset (r : ℕ) [NeZero r] (p : Output × Tally) : ScanArgs :=
  let z := p.1.2
  let code := storedLink p.1
  let Q := probe p.1
  (active r z, !more (code, z.2.1.1), z.2.1.1, timesTally r z.2.2.1,
    (direction z, SolC14Reply.zeroWord code, intervalWord r z, decMagnitude code, dec Q, inc Q),
    z.2.2.2, p.2, z.2.2.1)

def scanArgs (r : ℕ) [NeZero r] (p : Output) : ScanArgs :=
  scanWithOffset r (p, cutOffset r p.2)

set_option maxHeartbeats 800000 in
theorem easy_scanWithOffset (r : ℕ) [NeZero r] : Easy (scanWithOffset r) := by
  let X := Output × Tally
  have hhead : Easy (fun p : X => p.1.2) := Easy.fst.compose Easy.snd
  have hI : Easy (fun p : X => p.1.2.2.1.1) := hhead.sndCompose.fstCompose.fstCompose
  have hw : Easy (fun p : X => p.1.2.2.2.1) := hhead.sndCompose.sndCompose.fstCompose
  have hh : Easy (fun p : X => p.1.2.2.2.2) := hhead.sndCompose.sndCompose.sndCompose
  have hs (n : ℕ) : Easy (fun p : X => SolBatchCore.atWord n p.1.1) :=
    (Easy.fst.compose Easy.fst).compose (SolBatchCore.easy_atWord n)
  have hprobe : Easy (fun p : X => probe p.1) := ((hhead.compose (easy_fieldIdx.compose (easy_modWord 3))).pair
      ((hh.pair (hs 0)).compose easy_quotient)).compose easy_adjustBlock
  have hlink := hs 1
  have hv := (easy_more (hlink.pair hI)).compose (Easy.finite (fun b : Bool => !b))
  have hi := hhead.compose (easy_qword (p := r) easy_flatIdx)
  have hcmp := (hhead.compose easy_direction).pair ((hlink.compose SolC14Reply.easy_zeroWord).pair
    (hi.pair ((hlink.compose easy_decMagnitude).pair
      ((hprobe.compose SolSigned.easy_dec).pair (hprobe.compose easy_inc)))))
  exact (hhead.compose (easy_active r)).pair (hv.pair (hI.pair
    ((hw.compose (easy_timesTally r)).pair (hcmp.pair (hh.pair (Easy.snd.pair hw))))))

theorem poly_scanArgs (r : ℕ) [NeZero r] : Poly (scanArgs r) :=
  (Poly.identity.pair (Poly.identity.sndCompose.compose (poly_cutOffset r))).compose
    (easy_scanWithOffset r).poly

structure Fits (D : Dims) (r : ℕ) (p : Header) (w : Word) : Prop where
  intervals : value p.2.1.1 = D.I
  start : value p.2.1.2.1 = D.off secStart
  prev : value p.2.1.2.2.1 = D.off secPrev
  next : value p.2.1.2.2.2 = D.off secNext
  width : p.2.2.1.length = D.bigW
  lanes : 2 ^ p.2.2.2.length = D.N
  tapes : r = D.r
  witness : guessEnd D ≤ w.length

variable {D : Dims} {r : ℕ} {p : Header} {w : Word}

theorem active_iff (h : Fits D r p w) :
    active r p = true ↔ value p.1 < D.I * D.r * 3 * 2 := by
  rw [active, more_lt, scale_exact, h.intervals, h.tapes]
  have he : 6 * D.r * D.I = D.I * D.r * 3 * 2 := by ring
  rw [he]

theorem fieldIdx_value (p : Header) : value (fieldIdx p) = value p.1 / 2 := by
  rcases p with ⟨q, hdr⟩
  cases q with
  | nil => simp only [fieldIdx, magnitude, List.tail_nil, value_nil, Nat.zero_div]
  | cons b w =>
    change value w = value (b :: w) / 2
    have h := digit_le b
    rw [value_cons]
    omega

theorem flatIdx_value (p : Header) : value (flatIdx p) = value p.1 / 2 / 3 := by
  rw [flatIdx, qword_value, fieldIdx_value]

theorem direction_eq (p : Header) : direction p = decide (value p.1 % 2 = 1) := by
  rcases p with ⟨q, hdr⟩
  cases q with
  | nil => rfl
  | cons b w =>
    change b = decide ((value (b :: w)) % 2 = 1)
    rw [value_cons]
    cases b <;> simp [d0, d1, Nat.add_mul_mod_self_left]

theorem total_dom (r : ℕ) :
    Dom (fun p : Header => size p) (fun p => P1Batch.total (plan r p).1) := by
  apply (Dom.base _).mono
  intro p
  have hw : 2 * p.2.2.1.length ≤ size p := by simp only [size_prod, size_tally]; omega
  unfold plan
  cases ha : active r p <;> simp only [ha, Bool.cond_true, Bool.cond_false,
    P1Batch.total, List.map_nil, List.map_cons, List.sum_nil, List.sum_cons, startReq, linkReq,
    fieldRequest, P1Batch.bval_eq_value, birthValue] <;> omega

theorem readPlan_size_linear (r : ℕ) (p : Header) (w : Word) :
    size (readPlan (plan r) p w) ≤ 4 * size p + 6 := by
  have hlen (q : P1Batch.Req) :
      size (P1Batch.fetch w q) ≤ 2 * P1Batch.bval q.2 + 1 := by
    rw [size_word, P1Batch.fetch, List.length_take]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.min_le_left _ _)) _
  have hs : size (P1Batch.fetch w (startReq p)) ≤ 2 * p.2.2.1.length + 1 :=
    (hlen (startReq p)).trans_eq (by
      simp only [startReq, fieldRequest, P1Batch.bval_eq_value, birthValue])
  have hl : size (P1Batch.fetch w (linkReq p)) ≤ 2 * p.2.2.1.length + 1 :=
    (hlen (linkReq p)).trans_eq (by
      simp only [linkReq, fieldRequest, P1Batch.bval_eq_value, birthValue])
  have hw : 2 * p.2.2.1.length ≤ size p := by simp only [size_prod, size_tally]; omega
  unfold readPlan plan
  cases ha : active r p
  · change 1 + size p + 1 ≤ _
    omega
  · change size (P1Batch.fetch w (startReq p)) + (size (P1Batch.fetch w (linkReq p)) + 1 + 1) + 1 +
      size p + 1 ≤ _
    omega

theorem plan_fits (h : Fits D r p w) (q : P1Batch.Req) (hq : q ∈ (plan r p).1) :
    P1Batch.bval q.1 + P1Batch.bval q.2 ≤ w.length := by
  cases ha : active r p
  · simp only [plan, ha, Bool.cond_false, List.not_mem_nil] at hq
  · have hn := (active_iff h).mp ha
    have hl : value (fieldIdx p) < D.I * D.r * 3 := by
      rw [fieldIdx_value]
      apply Nat.div_lt_of_lt_mul
      rwa [Nat.mul_comm 2]
    have hs : value (flatIdx p) < D.I * D.r := by
      rw [flatIdx, qword_value]
      apply Nat.div_lt_of_lt_mul
      rwa [Nat.mul_comm 3]
    simp only [plan, ha, Bool.cond_true, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact fieldRequest_fits h.start ((birthValue _).trans (h.width.trans (width_start D).symm))
        hs (by decide) h.witness
    · unfold linkReq
      cases hd : direction p
      · simp only [hd, Bool.cond_false]
        exact fieldRequest_fits h.prev ((birthValue _).trans (h.width.trans (width_prev D).symm))
          hl (by decide) h.witness
      · simp only [hd, Bool.cond_true]
        exact fieldRequest_fits h.next ((birthValue _).trans (h.width.trans (width_next D).symm))
          hl (by decide) h.witness

theorem start_read (h : Fits D r p w) (ha : active r p = true) :
    value (SolBatchCore.atWord 0 (readPlan (plan r) p w).1) =
      readField D w secStart (value p.1 / 2 / 3) := by
  simp only [readPlan, plan, ha, Bool.cond_true, List.map_cons, List.map_nil]
  change value (P1Batch.fetch w (startReq p)) = _
  rw [startReq, fieldRequest_read w _ _ _ h.start
    ((birthValue _).trans (h.width.trans (width_start D).symm)), flatIdx_value]

theorem link_read (h : Fits D r p w) (ha : active r p = true) :
    value (storedLink (readPlan (plan r) p w)) =
      readField D w (if direction p then secNext else secPrev) (value p.1 / 2) := by
  simp only [storedLink, readPlan, plan, ha, Bool.cond_true, List.map_cons, List.map_nil]
  change value (P1Batch.fetch w (linkReq p)) = _
  unfold linkReq
  cases hd : direction p
  · simp only [hd, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    rw [fieldRequest_read w _ _ _ h.prev ((birthValue _).trans (h.width.trans (width_prev D).symm)),
      fieldIdx_value]
  · simp only [hd, Bool.cond_true, ↓reduceIte]
    rw [fieldRequest_read w _ _ _ h.next ((birthValue _).trans (h.width.trans (width_next D).symm)),
      fieldIdx_value]

end P1ProgDir.SolC3Input
