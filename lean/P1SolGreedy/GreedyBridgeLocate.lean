import P1SolGreedy.GreedyBridgePrefix
import P1SolGreedy.GreedyBridgeLocal
import P1ChkFinal.EnergyFit

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Wit.SolSpace P1Int.P11 P1Int.SolTrueRecords
open P1ChkFinal.EnergyFit
open private Follows levelDims layoutRows from P1Wit.SpaceFacts
open private LiveTree live_choices from P1Int.RecordsFitProof
open private levelFrom levelFrom_head levelFrom_tail from P1Int.WLinkProof

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- A pass at the tested row, with a witness for its panels and a characterization of all matching choices. -/
def LocatedRow (D : Dims) (u : List Bool) (ℓ : ℕ) (G : Prop) : Prop :=
  ∃ (a g b n : ℕ) (X : State a g) (p : StatePass F X b n) (o : PassOrigin Bt κ hκ p)
      (f : PanelFits D (D.lv ℓ) X) (r : p.Records) (c : p.step.Choice),
    p.Bounded r Bt.recordLimit ∧
    D.lv ℓ = levelDims S.expanderExponent a g X.positions (some (isShrink Bt κ hκ o)) ∧
    Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW ∧ energyOK Bt κ hκ D.bigW o ∧
    (∀ m, panelKind m = true → ReadsKind D u ℓ (originRow Bt κ hκ D ℓ o f c) m) ∧
    ((∃ i : p.step.Choice, ∀ m, ReadsKind D u ℓ (originRow Bt κ hκ D ℓ o f i) m) ↔ G)

noncomputable abbrev panelsFromOrigin (D : Dims) {a g b n : ℕ} {X : State a g}
    (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E) (start : ℕ) (f : ExecFits D E start) :=
  mkPanels D E start f (panelTree Bt κ hκ D E o start)

noncomputable abbrev termsFromOrigin (D : Dims) {a g b n : ℕ} {X : State a g}
    (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E) (start : ℕ) (f : ExecFits D E start)
    (hinj : TablesInjective D E start (tableTree Bt κ hκ D E o start)) :=
  mkTerms D E start f (tableTree Bt κ hκ D E o start) hinj

theorem locate (D : Dims) (u : List Bool) (ℓ : ℕ) (hℓ : ℓ < D.top) (G : Prop)
    {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E)
    (c : E.Choices) (start : ℕ) (f : ExecFits D E start)
    (hinj : TablesInjective D E start (tableTree Bt κ hκ D E o start))
    (r : E.Records) (hr : E.Bounded Bt.recordLimit r) (xs : List Phase) (hphase : Follows E xs)
    (hLoss : ∀ ph ∈ xs, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent))
    (hrows : ∀ j, D.lv (start + j) = ((layoutRows S X.positions g xs)[j]?).getD
      (levelDims S.expanderExponent 0 0 0 none))
    (hW : Bt.recordLimit ^ xs.length * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (live : LiveTree E) (hE : energyTree Bt κ hκ D.bigW E o) (hs : start ≤ ℓ)
    (hprev : readsBefore u E (panelsFromOrigin Bt κ hκ D E o start f)
      (termsFromOrigin Bt κ hκ D E o start f hinj) c ℓ)
    (hp : ∀ m, panelKind m = true → ReadsKind D u ℓ (levelFrom E
      (panelsFromOrigin Bt κ hκ D E o start f) (termsFromOrigin Bt κ hκ D E o start f hinj)
      c ⟨ℓ, Nat.lt_succ_of_lt hℓ⟩ hs) m)
    (hG : G ↔ ∃ z : E.Choices, readsBefore u E (panelsFromOrigin Bt κ hκ D E o start f)
      (termsFromOrigin Bt κ hκ D E o start f hinj) z (ℓ + 1)) :
    LocatedRow Bt κ hκ D u ℓ G := by
  induction E generalizing start xs with
  | done =>
    have htop : start = D.top := f.1
    exact (Nat.not_le_of_lt hℓ (htop ▸ hs)).elim
  | @more a g a' g' X p tail ih =>
    cases xs with
    | nil => exact hphase.elim
    | cons ph xs =>
      obtain ⟨hdeg, hlanes, htail⟩ := hphase
      have he := Nat.add_right_cancel (hlanes.symm.trans (origin_lanes Bt κ hκ o.1))
      rw [hLoss ph List.mem_cons_self, ← hdeg] at he
      have hkind : ph.shrink = isShrink Bt κ hκ o.1 := by
        have hgap : a < packingLaneBits a 0 := by
          unfold packingLaneBits
          have := Nat.two_pow_pos a
          omega
        cases hh : ph.shrink <;> cases ho : isShrink Bt κ hκ o.1 <;>
          simp only [hh, ho, Bool.false_eq_true, ite_false, ite_true] at he ⊢
        · omega
        · omega
      have hrow := hrows 0
      simp only [Nat.add_zero, layoutRows, List.getElem?_cons_zero, Option.getD_some, ← hdeg, hkind] at hrow
      have hlim : 0 < Bt.recordLimit := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hbudget : Bt.recordLimit ^ xs.length * (Bt.recordLimit * (X.maxWireWidth + 1)) < 2 ^ D.wW := by
        rwa [← Nat.mul_assoc, ← pow_succ]
      let P := panelsFromOrigin Bt κ hκ D (.more p tail) o start f
      let T := termsFromOrigin Bt κ hκ D (.more p tail) o start f hinj
      change readsBefore u (.more p tail) P T c ℓ at hprev
      change G ↔ ∃ z : (StateExecution.more p tail).Choices, readsBefore u (.more p tail) P T z (ℓ + 1) at hG
      by_cases hdepth : start = ℓ
      · subst start
        have hlocal : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW :=
          (Nat.le_mul_of_pos_left _ (Nat.pow_pos hlim)).trans_lt hbudget
        refine ⟨a, g, a', g', X, p, o.1, f.2.1, r.1, c.1, hr.1, hrow, hlocal, hE.1, ?_, ?_⟩
        · intro m hm
          have hh := hp m hm
          change ReadsKind D u ℓ (levelFrom (.more p tail) P T c ⟨ℓ, T.1.in_range⟩ le_rfl) m at hh
          rw [levelFrom_head] at hh
          exact hh
        · exact (hG.trans (exists_readsBefore_head u P T (fun i => live_choices (tail i) (live.2 i)))).symm
      · have hlt : start < ℓ := lt_of_le_of_ne hs hdepth
        obtain ⟨hhead, hprev'⟩ := (readsBefore_more u P T c hlt).mp hprev
        have hG' := hG.trans (exists_readsBefore_tail u P T c.1 hhead (Nat.lt_succ_of_lt hlt))
        obtain ⟨hpos, hfollow⟩ := htail c.1
        have hdiv : 0 < ph.divisor := by
          by_contra! hz
          have hp' := X.positions_pos
          rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul] at hpos
          omega
        have hpos' : X.positions / ph.divisor = (p.next c.1).positions := by
          rw [hpos, Nat.mul_comm, Nat.mul_div_cancel _ hdiv]
        have hlanes' : g - ph.laneLoss = g' := by omega
        refine ih c.1 (o.2 c.1) c.2 (start + 1) (f.2.2 c.1) (hinj.2 c.1)
          (r.2 c.1) (hr.2 c.1) xs hfollow ?_ ?_ ?_ (live.2 c.1) (hE.2 c.1) hlt hprev' ?_ hG'
        · exact fun q hq => hLoss q (List.mem_cons_of_mem _ hq)
        · intro j
          have hj := hrows (j + 1)
          have hindex : start + (j + 1) = (start + 1) + j := by omega
          simpa only [hindex, layoutRows, List.getElem?_cons_succ, hpos', hlanes'] using hj
        · exact (Nat.mul_le_mul_left _
            ((Nat.succ_le_succ (hr.1 c.1).2.2).trans (hr.1 c.1).2.1)).trans_lt hbudget
        · intro m hm
          have hh := hp m hm
          change ReadsKind D u ℓ (levelFrom (.more p tail) P T c ⟨ℓ, Nat.lt_succ_of_lt hℓ⟩ hs) m at hh
          rw [levelFrom_tail P T c ⟨ℓ, Nat.lt_succ_of_lt hℓ⟩ hlt] at hh
          exact hh

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.locate
