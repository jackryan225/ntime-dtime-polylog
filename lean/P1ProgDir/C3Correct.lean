import P1ProgDir.C3Engine

namespace P1ProgDir.SolC3Correct

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Wit P1ChkDir
open P1ProgDir.SolGeometry P1ProgDir.SolC2Trits P1ProgDir.SolC3Input P1ProgDir.SolC3Engine
open P1ProgDir.SolC3Scan P1ProgDir.SolSigned P1ProgDir.SolSmallBatch P1ProgDir.SolOffsets

variable {D : Dims} {r : ℕ} [NeZero r] {p : Header} {w : Word}

theorem packed_req (h : Fits D r p w) :
    let z := packed r (readPlan (plan r) p w)
    P1Batch.bval z.1.1 = D.off secStart ∧
    P1Batch.bval z.1.2 = D.I * (D.r * D.bigW) ∧
    P1Batch.bval z.2.2.2.1 = D.I ∧ z.2.2.2.2.1.length = D.r * D.bigW := by
  simp only [packed, scanArgs, scanWithOffset, readPlan, plan, P1Batch.bval_eq_value, exact_prod,
    birthValue, timesTally_length, h.start, h.intervals, h.tapes, h.width]
  all_goals repeat' constructor

theorem packed_fits (h : Fits D r p w) :
    let z := packed r (readPlan (plan r) p w)
    P1Batch.bval z.1.1 + P1Batch.bval z.1.2 ≤ w.length := by
  let z := packed r (readPlan (plan r) p w)
  change P1Batch.bval z.1.1 + P1Batch.bval z.1.2 ≤ w.length
  obtain ⟨ha, hl, _⟩ := packed_req h
  rw [ha, hl]
  exact start_slice_fits D h.witness

theorem packed_rows (h : Fits D r p w) :
    rows (packed r (readPlan (plan r) p w)) w = startRows D w := by
  unfold rows startRows rowInput P1Batch.fetch
  obtain ⟨ha, hl, hI, hr⟩ := packed_req h
  rw [ha, hl, hI]
  have hwidth : (packed r (readPlan (plan r) p w)).2.2.2.2.1 = tally (D.r * D.bigW) := by
    rw [← hr]
    exact (tally_of_length _).symm
  rw [hwidth]

theorem ownToN_cases {I : ℕ} (code : ℕ) (h : code ≤ I) :
    ∃ o : Option (Fin I), ownToN o = code := by
  by_cases hn : code = 0
  · exact ⟨none, hn.symm⟩
  · exact ⟨some ⟨code - 1, by omega⟩, by
      change code - 1 + 1 = code
      omega⟩

theorem ownToN_le {I : ℕ} (o : Option (Fin I)) : ownToN o ≤ I := by
  cases o with
  | none => exact Nat.zero_le _
  | some j => exact j.isLt

theorem ownToN_injective (I : ℕ) : Function.Injective (ownToN (I := I)) := by
  intro o o' he
  have h := congrArg (ownOfN I) he
  rw [ownOfN_toN, ownOfN_toN] at h
  exact Option.some.inj h

open Classical in
theorem reply_iff {K : Type} (tape : K ≃ Fin D.r) (h : Fits D r p w) :
    reply (packed r (readPlan (plan r) p w)) w = true ↔ C3F D tape w (value p.1) := by
  let j := value p.1
  let out := readPlan (plan r) p w
  let z := packed r out
  let ctx := context z.2
  let code := value (storedLink out)
  have htag : z.2.1 = active r p := rfl
  change (finish (SolIndexedSweep.run rowTest (rows z w, ctx), z.2.1, z.2.2.1) = true ↔ _)
  rw [htag]
  by_cases hn : j < D.I * D.r * 3 * 2
  · have ha := (active_iff h).mpr hn
    have hc : code = readField D w (if direction p then secNext else secPrev) (j / 2) :=
      link_read h ha
    rw [SolC3Index.c3_readback D tape w hn]
    dsimp only
    rw [← direction_eq p, ← hc]
    have valid : z.2.2.1 = true ↔ code ≤ D.I := by
      change (!more (storedLink out, p.2.1.1)) = true ↔ _
      have hb (b : Bool) : (!b) = true ↔ ¬ b = true := by cases b <;> decide
      rw [hb, more_lt, h.intervals, not_lt]
    simp only [finish, ha, Bool.not_true, Bool.false_or, Bool.and_eq_true, valid]
    by_cases hv : code ≤ D.I
    · simp only [hv, true_and]
      obtain ⟨o, ho⟩ := ownToN_cases code hv
      have huni (o' : Option (Fin D.I)) : code = ownToN o' ↔ o' = o := by
        rw [← ho]
        exact ⟨fun e => ownToN_injective _ e.symm, fun e => congrArg _ e.symm⟩
      have hex (P : Option (Fin D.I) → Prop) : (∃ o', o' = o ∧ P o') ↔ P o :=
        ⟨fun ⟨_, he, hp⟩ => he ▸ hp, fun hp => ⟨o, rfl, hp⟩⟩
      simp only [huni, hex]
      let i : Fin D.I := ⟨j / 2 / 3 / D.r, SolC3Index.interval_lt D hn⟩
      let k := j / 2 / 3 % D.r
      let Q := bigOf D.N (unzigzag (readField D w secStart (j / 2 / 3))) - 1 + ((j / 2 % 3 : ℕ) : ℤ)
      have hk : k < D.r := Nat.mod_lt _ (h.tapes ▸ Nat.pos_of_ne_zero (NeZero.ne r))
      have hQ : signedValue (probe out) = Q := by
        have hout : out.2 = p := rfl
        have hstart : value (SolBatchCore.atWord 0 out.1) = readField D w secStart (j / 2 / 3) :=
          start_read h ha
        unfold probe
        rw [hout, adjustBlock_value]
        · rw [quotient_value, ← Int.natCast_pow, h.lanes, signedValue, hstart,
            deltaWord, modWord_value, fieldIdx_value] <;> rfl
        · rw [deltaWord, modWord_value]
          exact Nat.mod_lt _ (by decide)
      rw [packed_rows h]
      apply scan_iff D w ctx.2 ctx.1 i k hk Q (direction p) o
      · have hh := value_lt p.2.1.1
        change D.I < 2 ^ (ruler p.2.1.1).length
        rw [ruler_length, ← h.intervals]
        exact hh
      · rfl
      · change SolC14Reply.zeroWord (storedLink out) = o.isNone
        rw [Bool.eq_iff_iff, SolC14Reply.zeroWord_eq]
        change code = 0 ↔ _
        rw [← ho]
        cases o with
        | none => exact iff_of_true rfl rfl
        | some v =>
          change (v : ℕ) + 1 = 0 ↔ false = true
          simp only [Nat.add_one_ne_zero, Bool.false_eq_true]
      · change value (intervalWord r p) = i.val
        rw [intervalWord, qword_value, flatIdx_value]
        change j / 2 / 3 / r = j / 2 / 3 / D.r
        rw [h.tapes]
      · intro v he
        have hc' : code = (v : ℕ) + 1 := by rw [← ho, he]; rfl
        change value (decMagnitude (storedLink out)) = v.val
        have e := decMagnitude_value (storedLink out) (show 0 < code by omega)
        change value (decMagnitude (storedLink out)) + 1 = code at e
        omega
      · change signedValue (dec (probe out)) = Q - 1
        rw [dec_value, hQ]
      · change signedValue (inc (probe out)) = Q + 1
        rw [inc_value, hQ]
      · change (tally (value (tapeWord r p) * p.2.2.1.length)).length = _
        rw [tally_length, tapeWord, modWord_value, flatIdx_value, h.width, h.tapes]
      · exact h.width
      · exact h.lanes
    · simp only [hv, false_and, false_iff]
      rintro ⟨o, ho, _⟩
      apply hv
      rw [ho]
      exact ownToN_le o
  · have ha : active r p = false := by
      cases e : active r p
      · rfl
      · exact (hn ((active_iff h).mp e)).elim
    rw [ha]
    exact iff_of_true rfl (C3F_out D tape w (Nat.le_of_not_gt hn))

theorem prepare {X : Type} (D : X → Dims) (r : ℕ) [NeZero r]
    (hdr : X → Header) (w : X → Word) (hfit : ∀ x, Fits (D x) r (hdr x) (w x)) :
    let z := fun x => packed r (readPlan (plan r) (hdr x) (w x))
    ∃ β : X → ℕ, Dom (fun x => size (hdr x)) β ∧
      Task (fun x => (w x).length + β x + ((D x).I + 1) * (size (z x) + 1))
        (fun x => send (hdr x, w x))
        (fun x => send (reply (z x) (w x))) := by
  let mid (x : X) := readPlan (plan r) (hdr x) (w x)
  let z (x : X) := packed r (mid x)
  obtain ⟨a, ha, h₁⟩ := SolSmallBatch.task hdr w (plan r) (poly_plan r)
    ((total_dom r).map hdr) (fun x => plan_fits (hfit x))
  obtain ⟨b, hb, h₂⟩ := (poly_packed r).on
    (readPlan_size hdr w (plan r) (poly_plan r) ((total_dom r).map hdr))
  have hc : Task (fun x => (w x).length + ((D x).I + 1) * (size (z x) + 1))
      (fun x => send (z x, w x)) (fun x => send (reply (z x) (w x))) :=
    (SolC3Engine.task z w (fun x => packed_fits (hfit x))).conform
      (fun x => by
        have e := (packed_req (hfit x)).2.2.1
        change (w x).length + (P1Batch.bval (z x).2.2.2.1 + 1) * (size (z x) + 1) = _
        rw [e]) (fun _ => rfl) (fun _ => rfl)
  have hd : Easy (fun p : Header × Word => (p, p.2)) := Easy.identity.pair Easy.snd
  let β (x : X) := size (hdr x) + a x + b x
  refine ⟨β, ((Dom.base _).add ha).add hb, ?_⟩
  refine ((((hd.on (fun x => (hdr x, w x))).compose (h₁.left (fun x => send (w x)))).compose
    (h₂.left (fun x => send (w x)))).compose hc).bound 6 ?_
  intro x
  let m := (w x).length
  let W := ((D x).I + 1) * (size (z x) + 1)
  change size (hdr x, w x) + (2 * m + a x) + b x + (m + W) + 1 ≤ 6 * (m + β x + W + 1)
  rw [size_prod (hdr x, w x), size_word (w x)]
  change size (hdr x) + (2 * m + 1) + 1 + (2 * m + a x) + b x + (m + W) + 1 ≤
    6 * (m + (size (hdr x) + a x + b x) + W + 1)
  omega

end P1ProgDir.SolC3Correct
