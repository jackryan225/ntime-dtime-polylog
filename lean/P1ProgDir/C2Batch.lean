import P1ProgDir.C2Trits
import P1ProgDir.C14Reply

namespace P1ProgDir.SolC2Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkDir P1Wit
open P1ProgDir.SolGeometry P1ProgDir.SolFieldWords P1ProgDir.SolOffsets
open P1ProgDir.SolC2Reply P1ProgDir.SolC2Trits P1ProgDir.SolSigned P1ProgDir.SolSmallBatch

abbrev Header := (Word × Word) × Word × Tally × Tally
abbrev State := Bool × Bool × Tally × Tally
abbrev Output := List Word × State

def active (p : Header) : Bool := more (p.1.2, p.1.1)
def initial (r : ℕ) [NeZero r] (p : Header) : Bool := more (born r, p.1.1)
def current (p : Header) : P1Batch.Req := fieldRequest p.2.1 (born p.2.2.1.length) p.1.1
def pastIndex (r : ℕ) (p : Header) : Word := (sub (p.1.1, born r)).1
def past (r : ℕ) (p : Header) : P1Batch.Req :=
  fieldRequest p.2.1 (born p.2.2.1.length) (pastIndex r p)

def rowWidth (r : ℕ) (p : Header) : Word := scale (r * 2) (born p.2.2.2.length)

def rowReq (r : ℕ) [NeZero r] (p : Header) : P1Batch.Req :=
  (product (decMagnitude (qword (p := r) p.1.1), rowWidth r p), rowWidth r p)

def reqs (r : ℕ) [NeZero r] (p : Header) : List P1Batch.Req :=
  bif active p then
    current p :: (bif initial r p then [] else [past r p, rowReq r p])
  else []

def plan (r : ℕ) [NeZero r] (p : Header) : List P1Batch.Req × State :=
  (reqs r p, active p, initial r p, p.2.2.2, tally (value (modWord r p.1.1)))

theorem poly_plan (r : ℕ) [NeZero r] : Poly (plan r) := by
  have hi : Easy (fun p : Header => p.1.1) := Easy.fst.compose Easy.fst
  have ho : Poly (fun p : Header => p.2.1) := Poly.identity.sndCompose.fstCompose
  have hw : Poly (fun p : Header => born p.2.2.1.length) :=
    Poly.identity.sndCompose.sndCompose.fstCompose.compose easy_chart.poly
  have hN : Poly (fun p : Header => p.2.2.2) := Poly.identity.sndCompose.sndCompose.sndCompose
  have ha : Easy active := easy_more ((Easy.fst.compose Easy.snd).pair hi)
  have h₀ : Easy (initial r) := easy_more ((Easy.const _).pair hi)
  have hc : Poly current := poly_fieldRequest ho hw hi.poly
  have hp : Poly (past r) :=
    poly_fieldRequest ho hw ((easy_sub (hi.pair (Easy.const _))).fstCompose.poly)
  have hR : Poly (rowWidth r) := poly_scale _ (hN.compose easy_chart.poly)
  have hj := (easy_qword (p := r) hi).compose easy_decMagnitude
  have hq : Poly (rowReq r) := (poly_mul hj.poly hR).pair hR
  have ht : Poly (fun p : Header => [past r p, rowReq r p]) :=
    (hp.pair ((hq.pair (Code.Poly.const ([] : List P1Batch.Req))).compose Poly.cons)).compose Poly.cons
  exact (ha.poly.choose ((hc.pair (h₀.poly.choose (Code.Poly.const []) ht)).compose Poly.cons)
    (Code.Poly.const [])).pair (ha.poly.pair (h₀.poly.pair (hN.pair (hi.poly.compose (poly_tally_mod r)))))

def fetchedTrits (r : ℕ) (p : Output) : List Word :=
  trits r (p.2.2.2.1, p.2.2.2.2, SolBatchCore.atWord 2 p.1)

def reply (r : ℕ) (p : Output) : Bool :=
  let cur := SolBatchCore.atWord 0 p.1
  let prev := SolBatchCore.atWord 1 p.1
  let ts := fetchedTrits r p
  !p.2.1 || (bif p.2.2.1 then SolC14Reply.eqSigned (cur, []) else
    checkSum (cur, prev, countWord 2 ts, countWord 0 ts))

theorem poly_reply (r : ℕ) : Poly (reply r) := by
  have ha : Poly (fun p : Output => p.2.1) := Poly.identity.sndCompose.fstCompose
  have h₀ : Poly (fun p : Output => p.2.2.1) := Poly.identity.sndCompose.sndCompose.fstCompose
  have hg (n : ℕ) : Poly (fun p : Output => SolBatchCore.atWord n p.1) :=
    Poly.identity.fstCompose.compose (SolBatchCore.easy_atWord n).poly
  have ht : Poly (fetchedTrits r) :=
    (Poly.identity.sndCompose.sndCompose.sndCompose.fstCompose.pair
      (Poly.identity.sndCompose.sndCompose.sndCompose.sndCompose.pair (hg 2))).compose (poly_trits r)
  have hc := (hg 0).pair ((hg 1).pair ((ht.compose (easy_countWord 2).poly).pair
    (ht.compose (easy_countWord 0).poly)))
  have hz := ((hg 0).pair (Code.Poly.const ([] : Word))).compose SolC14Reply.easy_eqSigned.poly
  exact (ha.pair (h₀.choose hz (hc.compose easy_checkSum.poly))).compose
    (Easy.finite (fun p : Bool × Bool => !p.1 || p.2)).poly

structure Fits (D : Dims) (r : ℕ) (p : Header) (w : Word) : Prop where
  blocks : value p.1.2 = D.I * D.r
  start : value p.2.1 = D.off secStart
  width : p.2.2.1.length = D.bigW
  lanes : p.2.2.2.length = D.N
  tapes : r = D.r
  witness : guessEnd D ≤ w.length

variable {D : Dims} {r : ℕ} [NeZero r] {p : Header} {w : Word}

theorem total_dom (r : ℕ) [NeZero r] :
    Dom (fun p : Header => size p) (fun p => P1Batch.total (plan r p).1) := by
  apply ((Dom.const _ (r * 2 + 2)).mul (Dom.base _)).mono
  intro p
  have h₁ : p.2.2.1.length ≤ size p := by simp only [size_prod, size_tally]; omega
  have h₂ : p.2.2.2.length ≤ size p := by simp only [size_prod, size_tally]; omega
  simp only [Nat.add_mul]
  unfold plan reqs
  cases ha : active p <;> cases h₀ : initial r p <;>
    simp only [ha, h₀, Bool.cond_false, Bool.cond_true, P1Batch.total, List.map_nil, List.map_cons,
      List.sum_nil, List.sum_cons, current, past, rowReq, rowWidth, fieldRequest,
      P1Batch.bval_eq_value, birthValue, scale_exact]
  all_goals
    have h := Nat.mul_le_mul_left (r * 2) h₂
    omega

theorem read_current (h : Fits D r p w) :
    value (P1Batch.fetch w (current p)) = readField D w secStart (value p.1.1) :=
  fieldRequest_read w _ _ _ h.start ((birthValue _).trans (h.width.trans (width_start D).symm))

theorem past_index (p : Header) (h₀ : r ≤ value p.1.1) :
    value (pastIndex r p) = (value p.1.1 / r - 1) * r + value p.1.1 % r := by
  have hdiv := Nat.div_add_mod (value p.1.1) r
  have hp : 0 < value p.1.1 / r := Nat.div_pos h₀ (Nat.pos_of_ne_zero (NeZero.ne r))
  have hm := Nat.sub_add_cancel (show 1 ≤ value p.1.1 / r by omega)
  have he := congrArg (· * r) hm
  simp only [Nat.add_mul, Nat.one_mul] at he
  rw [Nat.mul_comm r] at hdiv
  unfold pastIndex
  rw [sub_val_le _ _ (by simpa only [birthValue] using h₀), birthValue]
  omega

theorem row_values (h : Fits D r p w) (h₀ : r ≤ value p.1.1) :
    P1Batch.bval (rowReq r p).1 = (value p.1.1 / r - 1) * (D.N * D.r * 2) ∧
    P1Batch.bval (rowReq r p).2 = D.N * D.r * 2 := by
  have hp : 0 < value (qword (p := r) p.1.1) := by
    rw [qword_value]
    exact Nat.div_pos h₀ (Nat.pos_of_ne_zero (NeZero.ne r))
  have e := decMagnitude_value _ hp
  have he : value (decMagnitude (qword (p := r) p.1.1)) = value (qword (p := r) p.1.1) - 1 := by omega
  simp only [rowReq, rowWidth, P1Batch.bval_eq_value, exact_prod, scale_exact,
    he, qword_value, birthValue, h.lanes]
  rw [h.tapes]
  constructor <;> ring

theorem plan_fits (h : Fits D r p w) (q : P1Batch.Req) (hq : q ∈ (plan r p).1) :
    P1Batch.bval q.1 + P1Batch.bval q.2 ≤ w.length := by
  cases ha : active p
  · simp only [plan, reqs, ha, Bool.cond_false, List.not_mem_nil] at hq
  · have hi : value p.1.1 < D.I * D.r := by
      rwa [active, more_lt, h.blocks] at ha
    have hw : value (born p.2.2.1.length) = D.width secStart :=
      (birthValue _).trans (h.width.trans (width_start D).symm)
    have hc : P1Batch.bval (current p).1 + P1Batch.bval (current p).2 ≤ w.length :=
      fieldRequest_fits h.start hw hi (by decide) h.witness
    cases h₀ : initial r p
    · have hlt : ¬ value p.1.1 < r := by
        intro hlt
        have he := (more_lt (born r) p.1.1).mpr (by rw [birthValue]; exact hlt)
        unfold initial at h₀
        rw [h₀] at he
        cases he
      have hl : value (pastIndex r p) < D.I * D.r := by
        unfold pastIndex
        rw [sub_val_le _ _ (by simpa only [birthValue] using Nat.le_of_not_gt hlt)]
        exact (Nat.sub_le _ _).trans_lt hi
      have hp : P1Batch.bval (past r p).1 + P1Batch.bval (past r p).2 ≤ w.length :=
        fieldRequest_fits h.start hw hl (by decide) h.witness
      have hj : value p.1.1 / r - 1 < D.I := by
        have he : value p.1.1 / r < D.I := Nat.div_lt_of_lt_mul (by
          simpa only [h.tapes, Nat.mul_comm] using hi)
        exact (Nat.sub_le _ _).trans_lt he
      obtain ⟨haddr, hwidth⟩ := row_values h (Nat.le_of_not_gt hlt)
      have hq' : P1Batch.bval (rowReq r p).1 + P1Batch.bval (rowReq r p).2 ≤ w.length := by
        rw [haddr, hwidth]
        simpa only [off_trit, Nat.zero_add, Nat.mul_assoc] using trit_row_fits D h.witness hj
      simp only [plan, reqs, ha, h₀, Bool.cond_true, Bool.cond_false, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hc
      · exact hp
      · exact hq'
    · simp only [plan, reqs, ha, h₀, Bool.cond_true, List.mem_singleton] at hq
      simpa only [hq] using hc

theorem reply_iff {K : Type} (tape : K ≃ Fin D.r) (h : Fits D r p w) :
    reply r (readPlan (plan r) p w) = true ↔ C2F D tape w (value p.1.1) := by
  let i := value p.1.1
  have h₀ : initial r p = true ↔ i < r := by rw [initial, more_lt, birthValue]
  have ha : active p = true ↔ i < D.I * D.r := by rw [active, more_lt, h.blocks]
  have hdiv : i / r = 0 ↔ i < r := Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero (NeZero.ne r))
  by_cases hi : i < D.I * D.r
  · rw [SolReadbacks.c2_readback, or_iff_right (Nat.not_le.mpr hi), ← h.tapes]
    have ea := ha.mpr hi
    by_cases hj : i < r
    · have e₀ := h₀.mpr hj
      have ej : value p.1.1 / r = 0 := hdiv.mpr hj
      simp only [reply, readPlan, plan, reqs, ea, e₀, Bool.cond_true, Bool.not_true,
        Bool.false_or, List.map_cons, List.map_nil, ej, ↓reduceIte]
      change SolC14Reply.eqSigned (P1Batch.fetch w (current p), []) = true ↔ _
      rw [SolC14Reply.eqSigned_eq]
      change signedValue (P1Batch.fetch w (current p)) = signedValue [] ↔ _
      rw [show signedValue [] = 0 from rfl, signedValue, read_current h]
    · have e₀ : initial r p = false := by
        cases e : initial r p
        · rfl
        · exact (hj (h₀.mp e)).elim
      have ediv : value p.1.1 / r ≠ 0 := fun h => hj (hdiv.mp h)
      simp only [reply, readPlan, plan, reqs, ea, e₀, Bool.cond_true, Bool.cond_false,
        Bool.not_true, Bool.false_or, List.map_cons, List.map_nil, ediv,
        ↓reduceIte]
      let cur := P1Batch.fetch w (current p)
      let prev := P1Batch.fetch w (past r p)
      let ws := trits r (p.2.2.2, tally (value (modWord r p.1.1)), P1Batch.fetch w (rowReq r p))
      change checkSum (cur, prev, countWord 2 ws, countWord 0 ws) = true ↔
        unzigzag (readField D w secStart i) =
          unzigzag (rdStart D w (i / r - 1) (i % r)) +
            ∑ g ∈ Finset.range D.N, SolReadbacks.tritDelta (rdTrit D w ((i / r - 1) * D.N + g) (i % r))
      have hpast : value prev = rdStart D w (i / r - 1) (i % r) := by
        have he := fieldRequest_read w p.2.1 (born p.2.2.1.length) (pastIndex r p)
          h.start ((birthValue _).trans (h.width.trans (width_start D).symm))
        change value prev = _ at he
        rw [he, past_index p (Nat.le_of_not_gt hj), rdStart, h.tapes]
      have hwords : ws.map value = (List.range D.N).map (fun g => rdTrit D w ((i / r - 1) * D.N + g) (i % r)) := by
        have ht : i % r < D.r :=
          (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne r))).trans_eq h.tapes
        obtain ⟨haddr, hw⟩ := row_values h (Nat.le_of_not_gt hj)
        unfold ws
        rw [P1Batch.fetch, haddr, hw, modWord_value, ← tally_of_length p.2.2.2,
          h.lanes]
        rw [h.tapes]
        exact trits_values D w (i / D.r - 1) (i % D.r) (by simpa only [h.tapes] using ht)
      rw [checkSum_eq, countWord_value, countWord_value, add_sub_assoc, ← trit_count_eq,
        hwords, signedValue, signedValue, read_current h, hpast, List.map_map]
      have hsum (f : ℕ → ℤ) : ((List.range D.N).map f).sum = ∑ g ∈ Finset.range D.N, f g := by
        rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
      simp only [Function.comp_def, hsum, i]
  · have ea : active p = false := by
      cases e : active p
      · rfl
      · exact (hi (ha.mp e)).elim
    refine iff_of_true ?_ (C2F_out D tape w (Nat.le_of_not_gt hi))
    change (!active p || _) = true
    rw [ea]
    rfl

end P1ProgDir.SolC2Batch
