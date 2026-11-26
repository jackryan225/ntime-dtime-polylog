import P1Hier.UTParseCover

/-! Prefix decoding with a fixed zero reserve. A completed parse used some of the
reserve exactly when its residual has fewer bits than the reserve. The transcript
format additionally tests that the residual consists entirely of zeros. -/

namespace P1Hier.AstraParse

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

structure Grammar {α : Type} [Codec α] (s : α → Bits) (K : ℕ) : Prop where
  reader : Reads s
  completion : Complete s K

namespace Grammar

variable {α β : Type} [Codec α] [Codec β] {s : α → Bits} {t : β → Bits} {A B : ℕ}

theorem unit : Grammar unitWord 0 := ⟨Reads.unit, Complete.unit⟩
theorem bit : Grammar bitWord 1 := ⟨Reads.bit, Complete.bit⟩

theorem prod (g : Grammar s A) (h : Grammar t B) : Grammar (prodWord s t) (A + B) :=
  ⟨g.reader.prod h.reader, g.completion.prod h.completion⟩

theorem sum (g : Grammar s A) (h : Grammar t B) : Grammar (sumWord s t) (A + B + 1) :=
  ⟨g.reader.sum h.reader, g.completion.sum h.completion⟩

theorem option (g : Grammar s A) : Grammar (optionWord s) (A + 1) :=
  ⟨g.reader.option, g.completion.option⟩

theorem list (g : Grammar s A) : Grammar (serL s) (A + 1) :=
  ⟨g.reader.list, g.completion.list⟩

private theorem unit_list_word (l : List Unit) : serL unitWord l = serN l.length := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    rw [serL_cons, List.length_cons, serN_succ, ih]
    <;> rfl

theorem unary : Grammar serN 1 := by
  have g := Grammar.unit.list
  refine ⟨g.reader.via (fun n => List.replicate n ()) ?_ (fun _ => rfl),
    g.completion.via List.length (fun l => (unit_list_word l).symm)⟩
  intro n
  rw [unit_list_word, List.length_replicate]

theorem move : Grammar serMv 2 := by
  have g := Grammar.bit.option
  exact ⟨g.reader.via id (fun m => by cases m <;> rfl) (fun _ => rfl),
    g.completion.via id (fun m => by cases m <;> rfl)⟩

theorem result : Grammar serRes 3 := by
  have g := Grammar.unary.sum Grammar.bit
  exact ⟨g.reader.via id (fun m => by cases m <;> rfl) (fun _ => rfl),
    g.completion.via id (fun m => by cases m <;> rfl)⟩
theorem cell : Grammar serCell 4 := Grammar.unary.prod (Grammar.unary.prod Grammar.move)

theorem entry : Grammar serEntry 9 :=
  Grammar.unary.prod (Grammar.cell.list.prod Grammar.result)

theorem transcript : Grammar serT 10 := Grammar.entry.list

private abbrev Fields := ℕ × ℕ × ℕ × ℕ × ℕ × List Entry

private def fields (c : MCode) : Fields := (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)

private def ofFields (v : Fields) : MCode :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩

theorem code : Grammar serCode 15 := by
  have g := Grammar.unary.prod (Grammar.unary.prod (Grammar.unary.prod
    (Grammar.unary.prod (Grammar.unary.prod Grammar.transcript))))
  exact ⟨g.reader.via fields (fun _ => rfl) (fun _ => rfl),
    g.completion.via ofFields (fun _ => rfl)⟩

end Grammar

variable {α : Type} {s : α → Bits} {K : ℕ}

private theorem easy_enough (k : ℕ) : Easy (fun w : Bits => decide (k ≤ w.length)) := by
  have hpair : Easy (fun w : Bits => (w, zeros k)) := easy_id.pair (Easy.const _)
  have h : Easy (fun w : Bits => !(Code.Iter.small (w, zeros k))) :=
    (hpair.compose Code.Iter.small_easy).compose Code.Iter.negate
  apply UM.easy_congr h
  intro w
  by_cases hk : k ≤ w.length
  · simp only [Code.Iter.small, zeros_length, not_lt_of_ge hk, hk, decide_false, decide_true,
      Bool.not_false]
  · simp only [Code.Iter.small, zeros_length, lt_of_not_ge hk, hk, decide_true, decide_false,
      Bool.not_true]

noncomputable def passes (h : Complete s K) (tailOK : Bits → Bool) (x : Bits) : Bool :=
  decide (K ≤ (padded h x).2.length) && tailOK (padded h x).2

noncomputable def checked (h : Complete s K) (tailOK : Bits → Bool) (d : α) (x : Bits) :
    Bool × α :=
  (passes h tailOK x, bif passes h tailOK x then (padded h x).1 else d)

private theorem easy_checked [Codec α] (g : Grammar s K) (tailOK : Bits → Bool)
    (ht : Easy tailOK) (d : α) : Easy (checked g.completion tailOK d) := by
  have h := easy_padded g.reader g.completion
  have hz := Easy.sndCompose h
  have hp : Easy (passes g.completion tailOK) :=
    UM.easy_and (hz.compose (easy_enough K)) (hz.compose ht)
  exact hp.pair (UM.easy_bif hp (Easy.fstCompose h) (Easy.const d))

private theorem checked_valid (h : Complete s K) (pf : PF s) (tailOK : Bits → Bool)
    (a d : α) (z : Bits) (ht : tailOK (z ++ zeros K) = true) :
    checked h tailOK d (s a ++ z) = (true, a) := by
  have hk : K ≤ (z ++ zeros K).length := by rw [List.length_append, zeros_length]; omega
  simp only [checked, passes, padded_valid h pf a z, hk, ht, decide_true, Bool.true_and,
    Bool.cond_true]

private theorem passes_sound (h : Complete s K) (tailOK : Bits → Bool) (x : Bits)
    (hp : passes h tailOK x = true) :
    ∃ z, x = s (padded h x).1 ++ z ∧ tailOK (z ++ zeros K) = true := by
  change (decide (K ≤ (padded h x).2.length) && tailOK (padded h x).2) = true at hp
  have both := Bool.and_eq_true_iff.mp hp
  obtain ⟨z, hx, hz⟩ := padded_split h x (of_decide_eq_true both.1)
  exact ⟨z, hx, (congrArg tailOK hz).symm.trans both.2⟩

/-- Agreement with a prefix-free specification, including its prescribed fallback
on every failing input. Appending the reserve must preserve the suffix test. -/
theorem easy_decoder [Codec α] (g : Grammar s K) (pf : PF s) (d : α)
    (obs : Bits → Option α) (tailOK : Bits → Bool) (ht : Easy tailOK)
    (htail : ∀ z, tailOK (z ++ zeros K) = tailOK z)
    (sound : ∀ x a, obs x = some a → ∃ z, x = s a ++ z ∧ tailOK z = true)
    (complete : ∀ a z, tailOK z = true → obs (s a ++ z) = some a) :
    Easy (fun x => ((obs x).isSome, (obs x).getD d)) := by
  apply UM.easy_congr (easy_checked g tailOK ht d)
  intro x
  apply congrArg send
  cases ho : obs x with
  | none =>
    have hbad : passes g.completion tailOK x = false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      obtain ⟨z, hx, hz⟩ := passes_sound g.completion tailOK x hp
      have hv := complete (padded g.completion x).1 z ((htail z).symm.trans hz)
      have he := (congrArg obs hx).trans hv
      rw [ho] at he
      cases he
    simp only [checked, hbad, Bool.cond_false, Option.isSome_none, Option.getD_none]
  | some a =>
    obtain ⟨z, hx, hz⟩ := sound x a ho
    rw [hx]
    exact checked_valid g.completion pf tailOK a d z ((htail z).trans hz)

theorem allFalse_pad (z : Bits) (k : ℕ) : UM.allFalse (z ++ zeros k) = UM.allFalse z := by
  apply Bool.eq_iff_iff.mpr
  change UM.allFalse (z ++ zeros k) = true ↔ UM.allFalse z = true
  simp only [UM.allFalse_iff]
  constructor
  · intro h b hb
    exact h b (List.mem_append_left _ hb)
  · intro h b hb
    rcases List.mem_append.mp hb with hz | hz
    · exact h b hz
    · exact List.eq_of_mem_replicate hz

end P1Hier.AstraParse

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Hier.AstraParse

theorem px2_easy (d : MCode) : Easy (px2 d) := by
  apply easy_decoder Grammar.code pf_serCode d px (fun _ => true) (Easy.const true)
    (fun _ => rfl)
  · intro x c h
    obtain ⟨z, hz⟩ := px_some h
    exact ⟨z, hz, rfl⟩
  · intro c z _
    exact px_serCode c z

theorem decT2_easy : Easy decT2 := by
  apply easy_decoder Grammar.transcript (pf_serL pf_serEntry) [] decT allFalse easy_allFalse
    (fun z => allFalse_pad z 10)
  · intro x τ h
    obtain ⟨z, hz, hzero⟩ := decT_some x τ h
    exact ⟨z, hz, (allFalse_iff z).mpr hzero⟩
  · intro τ z hz
    exact decT_eq τ z ((allFalse_iff z).mp hz)

end P1Hier.UM
