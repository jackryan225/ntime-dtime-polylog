import P1Wrap.OuterDecode

/-! # The outer verdict as a charged task

For a fixed machine code the W1 budget is linear in the tree holding the
input, unary clock and transcript. After the parameter call every operation
therefore has an `Easy` bound on the prepared input.
-/

namespace P1Wrap.W3.AstraOuter

open C1Challenge P1Int
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Hier (MCode Entry)

noncomputable section

private abbrev W1Args := List Bool × ℕ × List Entry
private abbrev Words := List Bool × List Bool
private abbrev Prepared := (Tally × Tally) × Words

private theorem easy_fixedCheck (c : MCode)
    (hW1 : Task P1Hier.checkBudget send (fun i => send (P1Hier.UM.chk i))) :
    Easy (fun p : W1Args => P1Hier.UM.chk (c, p)) := by
  have supplyCode : Easy (fun p : W1Args => (c, p)) := (Easy.const c).pair easy_id
  have run : Computes (fun p : W1Args => size p + P1Hier.checkBudget (c, p))
      (fun p => P1Hier.UM.chk (c, p)) :=
    Task.compose supplyCode (hW1.on (fun p : W1Args => (c, p)))
  refine Easy.of_bound run ((size c + 1) ^ 2 + 2) ?_
  intro p
  have hy : p.1.length + p.2.1 + 1 ≤ size p := by
    simp only [size_prod, P1Hier.UM.size_bits', P1Hier.UM.size_nat']
    omega
  have ht : size p.2.2 ≤ size p := by
    simp only [size_prod]
    omega
  have hc := Nat.mul_le_mul_left ((size c + 1) ^ 2) hy
  change size p + ((size c + 1) ^ 2 * (p.1.length + p.2.1 + 1) + size p.2.2) ≤ _
  rw [Nat.add_mul ((size c + 1) ^ 2) 2]
  omega

private def pieces (s : Prepared) : Words := cutLists (s.1.1, s.2.1)

private def hasRoom (s : Prepared) : Bool := decide (s.1.1.length = (pieces s).1.length)

private theorem hasRoom_iff (s : Prepared) :
    hasRoom s = true ↔ s.1.1.length ≤ s.2.1.length := by
  simp only [hasRoom, decide_eq_true_iff, pieces, cutLists, List.length_take]
  omega

private def padded (s : Prepared) : List Bool :=
  fill true (ruler s.2.2) ++ false :: (s.2.2 ++ (pieces s).1 ++ fill false s.1.2)

private def stageAnswer (c : MCode) (s : Prepared) : Bool :=
  hasRoom s && (layoutOK c.table (pieces s).2 &&
    P1Hier.UM.chk (c, padded s, s.2.1.length, parsedRows c.table (pieces s).2))

private theorem easy_stage (c : MCode)
    (hW1 : Task P1Hier.checkBudget send (fun i => send (P1Hier.UM.chk i))) :
    Easy (stageAnswer c) := by
  have hm : Easy (fun s : Prepared => s.1.1) := Easy.fstCompose Easy.fst
  have hp : Easy (fun s : Prepared => s.1.2) := Easy.sndCompose Easy.fst
  have hw : Easy (fun s : Prepared => s.2.1) := Easy.fstCompose Easy.snd
  have hx : Easy (fun s : Prepared => s.2.2) := Easy.sndCompose Easy.snd
  have cut : Easy pieces := easy_cut (hm.pair hw)
  have hprefix := Easy.fstCompose cut
  have hsuffix := Easy.sndCompose cut
  have room : Easy hasRoom := (hm.pair hprefix).compose Code.Iter.linked
  have body := easy_append (easy_append hx hprefix) (easy_fill false hp)
  have hy : Easy padded :=
    easy_append (easy_fill true (Easy.ruler hx)) (((Easy.const false).pair body).compose Easy.cons)
  have clock := hw.compose P1Hier.UM.easy_length
  have rows := hsuffix.compose (easy_parsedRows c.table)
  have check := (hy.pair (clock.pair rows)).compose (easy_fixedCheck c hW1)
  exact P1Hier.UM.easy_and room
    (P1Hier.UM.easy_and (hsuffix.compose (easy_layoutOK c.table)) check)

private theorem stage_true_iff (c : MCode) (s : Prepared) :
    stageAnswer c s = true ↔ s.1.1.length ≤ s.2.1.length ∧
      ∃ (τ : List Entry) (r : ℕ), (∀ e ∈ τ, e ∈ c.table) ∧
        (pieces s).2 = encT c.table τ ++ List.replicate r false ∧
        P1Hier.Check c (padded s) s.2.1.length τ := by
  simp only [stageAnswer, Bool.and_eq_true_iff, hasRoom_iff, P1Hier.UM.chk, decide_eq_true_iff]
  exact and_congr Iff.rfl
    (layout_check_iff c.table (pieces s).2 (P1Hier.Check c (padded s) s.2.1.length))

private def ready (j a b : ℕ) (p : Words) : Prepared :=
  ((tally (lpM2 (sOf j) a b p.2.length), tally (padLen j a b p.2.length)), p)

private theorem pieces_ready (j a b : ℕ) (w x : List Bool) :
    pieces (ready j a b (w, x)) =
      (w.take (lpM2 (sOf j) a b x.length), w.drop (lpM2 (sOf j) a b x.length)) := by
  simp only [pieces, ready, cutLists, tally_length]

private theorem padded_ready (j a b : ℕ) (w x : List Bool) :
    padded (ready j a b (w, x)) = padIn j a b x (w.take (lpM2 (sOf j) a b x.length)) := by
  unfold padded
  rw [pieces_ready]
  simp only [ready, fill_eq, ruler_length, tally_length, padIn]

private theorem stage_ready (M : Machine) (j a b : ℕ) (w x : List Bool) :
    stageAnswer (P1Hier.code (flipM M)) (ready j a b (w, x)) = outerVerdict M j a b w x := by
  classical
  rw [Bool.eq_iff_iff, stage_true_iff, outerVerdict, decide_eq_true_iff, padded_ready, pieces_ready]
  simp only [ready, tally_length]

/-- The budget covers every guess, including a short prefix or malformed transcript. -/
theorem outer_task (M : Machine) {j a b : ℕ}
    (hP : Computes (fun s : Tally => nuOf j a b s.length)
      (fun s : Tally => (tally (lpM2 (sOf j) a b s.length), tally (padLen j a b s.length))))
    (hu : Easy P1Hier.UM.unGuess)
    (hW1 : Task P1Hier.checkBudget send (fun i => send (P1Hier.UM.chk i))) :
    Task (fun p : List Bool × List Bool => p.1.length + nuOf j a b p.2.length)
      (fun p => send (withGuess p.1 p.2)) (fun p => send (outerVerdict M j a b p.1 p.2)) := by
  have splitInput : Easy (fun z : List Bool => (ruler (P1Hier.UM.unGuess z).2, P1Hier.UM.unGuess z)) :=
    (Easy.ruler (Easy.sndCompose hu)).pair hu
  have t₁ : Task (fun p : Words => size (withGuess p.1 p.2))
      (fun p => send (withGuess p.1 p.2)) (fun p => send (ruler p.2, p)) :=
    (Task.on splitInput (fun p : Words => withGuess p.1 p.2)).conform
      (fun _ => rfl) (fun _ => rfl) (fun p => by
        change send (ruler (P1Hier.UM.unGuess (withGuess p.1 p.2)).2,
          P1Hier.UM.unGuess (withGuess p.1 p.2)) = send (ruler p.2, p)
        rw [P1Hier.UM.unGuess_withGuess])
  have t₂ : Task (fun p : Words => nuOf j a b p.2.length)
      (fun p => send (ruler p.2, p)) (fun p => send (ready j a b p)) := by
    have h := (Task.on hP (fun p : Words => ruler p.2)).left (fun p : Words => send p)
    refine h.conform (fun p => ?_) (fun _ => rfl) (fun p => ?_)
    · simp only [ruler_length]
    · simp only [ready, send_prod, ruler_length]
  have t₃ := Task.on (easy_stage (P1Hier.code (flipM M)) hW1) (ready j a b)
  have combined := (t₁.compose t₂).compose t₃
  refine (combined.bound (b' := fun p => p.1.length + nuOf j a b p.2.length) 12
    (fun p => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun p => ?_)
  · change size (withGuess p.1 p.2) + nuOf j a b p.2.length + size (ready j a b p) + 1 ≤ _
    simp only [ready, size_prod, size_tally, tally_length, P1Hier.UM.size_bits', length_withGuess', nuOf]
    omega
  · exact congrArg send (stage_ready M j a b p.1 p.2)

end

end P1Wrap.W3.AstraOuter
