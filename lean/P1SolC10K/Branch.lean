import P1SolC10K.Stage

namespace P1SolC10K.Sol

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Wit.SolSpace
open P1C10 P1Int.P11 P1Int.SolTrueRecords
open private Follows levelDims layoutRows from P1Wit.SpaceFacts

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- Choose a single level on a fixed branch, carrying the actual dimensions and the remaining width bound. -/
theorem branchStep {fx : C10Fix} (ok : ScheduleCodeOK Bt fx) (D : Dims) (w : List Bool)
    (lanes : ∀ (j a g : ℕ) (Z : State a g), PanelFits D (D.lv j) Z → (D.lv j).laneW = g)
    {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E)
    (c : E.Choices) (start : ℕ) (f : ExecFits D E start)
    (inj : TablesInjective D E start (tableTree Bt κ hκ D E o start))
    (r : E.Records) (hr : E.Bounded Bt.recordLimit r) (xs : List Phase) (hphase : Follows E xs)
    (loss : ∀ ph ∈ xs, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent))
    (rows : ∀ j, D.lv (start + j) = ((layoutRows S X.positions g xs)[j]?).getD
      (levelDims S.expanderExponent 0 0 0 none))
    (budget : Bt.recordLimit ^ xs.length * (X.maxWireWidth + 1) < 2 ^ D.wW) :
    ∀ (ℓ : ℕ) (hs : start ≤ ℓ) (hl : ℓ < D.top),
      (∀ m, ReadsSection D w ℓ
        (branchRecord Bt κ hκ D E o c start f inj ⟨ℓ, Nat.lt_succ_of_lt hl⟩ hs) m) →
      ((∀ Y < (D.lv (ℓ + 1)).bases, C10at fx D w ℓ Y) ↔
        ∀ m, panelKind m = true → ReadsSection D w (ℓ + 1)
          (branchRecord Bt κ hκ D E o c start f inj ⟨ℓ + 1, Nat.succ_lt_succ hl⟩ (hs.trans (Nat.le_succ ℓ))) m) := by
  induction E generalizing start xs with
  | done X =>
    intro ℓ hs hl _
    have hend : start = D.top := f.1
    omega
  | @more a g a' g' X p tail ih =>
    cases xs with
    | nil => exact hphase.elim
    | cons ph xs =>
      obtain ⟨hdeg, hlanes, htail⟩ := hphase
      have hb : Bt.recordLimit ^ xs.length * (Bt.recordLimit * (X.maxWireWidth + 1)) < 2 ^ D.wW := by
        rwa [← Nat.mul_assoc, ← pow_succ]
      intro ℓ hs hl hread
      by_cases heq : start = ℓ
      · subst ℓ
        have he := Nat.add_right_cancel (hlanes.symm.trans (origin_lanes Bt κ hκ o.1))
        rw [loss ph List.mem_cons_self, ← hdeg] at he
        have hkind : ph.shrink = isShrink Bt κ hκ o.1 := by
          have hp : a < packingLaneBits a 0 := by
            unfold packingLaneBits
            have := Nat.two_pow_pos a
            omega
          cases h₁ : ph.shrink <;> cases h₂ : isShrink Bt κ hκ o.1 <;>
            simp only [h₁, h₂, Bool.false_eq_true, ite_false, ite_true] at he ⊢
          · omega
          · omega
        have row := rows 0
        simp only [Nat.add_zero, layoutRows, List.getElem?_cons_zero, Option.getD_some, ← hdeg, hkind] at row
        have hlim : 0 < Bt.recordLimit := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
        have hlocal : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW :=
          (Nat.le_mul_of_pos_left _ (Nat.pow_pos hlim)).trans_lt hb
        obtain ⟨child, nextExtra, hchild⟩ := branchRecordStart Bt κ hκ (tail c.1) (o.2 c.1) c.2
          (f.2.2 c.1) (inj.2 c.1) (Nat.succ_le_of_lt hl)
        have hn := branchRecordTail Bt κ hκ (p := p) (tail := tail) o c start f inj
          ⟨start + 1, Nat.succ_lt_succ hl⟩ le_rfl
        rw [hn, hchild]
        rw [branchRecordHead Bt κ hκ (p := p) (tail := tail) o c start f inj] at hread
        exact passStep Bt κ hκ ok D w start o.1 c.1 f.2.1 child nextExtra r.1 hr.1 row hlocal
          (lanes (start + 1) _ _ _ child) hread
      · have hs' : start + 1 ≤ ℓ := by omega
        have hin := branchRecordTail Bt κ hκ (p := p) (tail := tail) o c start f inj
          ⟨ℓ, Nat.lt_succ_of_lt hl⟩ hs'
        have hout := branchRecordTail Bt κ hκ (p := p) (tail := tail) o c start f inj
          ⟨ℓ + 1, Nat.succ_lt_succ hl⟩ (hs'.trans (Nat.le_succ ℓ))
        rw [hin] at hread
        rw [hout]
        obtain ⟨hpos, hfollow⟩ := htail c.1
        have hdiv : 0 < ph.divisor := by
          by_contra! hz
          have hp := X.positions_pos
          rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hpos
          omega
        have hpos' : X.positions / ph.divisor = (p.next c.1).positions := by
          rw [hpos, Nat.mul_comm, Nat.mul_div_cancel _ hdiv]
        have hlanes' : g - ph.laneLoss = g' := by omega
        refine ih c.1 (o.2 c.1) c.2 (start + 1) (f.2.2 c.1) (inj.2 c.1) (r.2 c.1) (hr.2 c.1)
          xs hfollow (fun ph hm => loss ph (List.mem_cons_of_mem _ hm)) ?_ ?_ ℓ hs' hl hread
        · intro j
          have hj := rows (j + 1)
          have hind : start + (j + 1) = (start + 1) + j := by omega
          simpa only [hind, layoutRows, List.getElem?_cons_succ, hpos', hlanes'] using hj
        · exact (Nat.mul_le_mul_left _ ((Nat.succ_le_succ (hr.1 c.1).2.2).trans (hr.1 c.1).2.1)).trans_lt hb

end
end P1SolC10K.Sol
