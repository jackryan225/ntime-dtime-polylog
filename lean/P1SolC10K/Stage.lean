import P1SolC10K.BranchRecords
import P1SolC10K.Panels

namespace P1SolC10K.Sol

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1P7 P1ChkFinal P1C10 P1Int.P11 P1Int.SolTrueRecords
open private levelDims from P1Wit.SpaceFacts
open private origin_of_reads from P1Int.WLinkProof

structure ScheduleCodeOK {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (fx : C10Fix) : Prop where
  shrink : ∀ i : Fin S.steps, ShrinkCodeOK Bt.shrink (S.shrink i)
    (fx.rcS (S.degreeExponent i.castSucc) (S.degreeExponent i.succ))
  refresh : RefreshCodeOK (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD' S) (schedule_hd' S) fx.rcR
  degree : fx.dH = 2 ^ S.expanderExponent

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

theorem passStep {fx : C10Fix} (ok : ScheduleCodeOK Bt fx) (D : Dims) (w : List Bool) (ℓ : ℕ)
    {a g b n : ℕ} {X : State a g} {p : StatePass F X b n} (o : PassOrigin Bt κ hκ p) (c : p.step.Choice)
    (fit : PanelFits D (D.lv ℓ) X) (child : PanelFits D (D.lv (ℓ + 1)) (p.next c))
    (extra : StepRecords D (D.lv (ℓ + 1))) (r : p.Records) (hr : p.Bounded r Bt.recordLimit)
    (row : D.lv ℓ = levelDims S.expanderExponent a g X.positions (some (isShrink Bt κ hκ o)))
    (budget : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW) (lane : (D.lv (ℓ + 1)).laneW = n)
    (reads : ∀ m, ReadsSection D w ℓ (headRecord Bt κ hκ D ℓ o c fit) m) :
    (∀ Y < (D.lv (ℓ + 1)).bases, C10at fx D w ℓ Y) ↔
      ∀ m, panelKind m = true → ReadsSection D w (ℓ + 1) (levelRecordsOfState (p.next c) child extra) m := by
  have haux := origin_of_reads Bt κ hκ D w ℓ o c fit r hr row budget (fun m => reads m)
  let v := panelAt Bt κ hκ D ℓ o c
  have hpanel : ∀ y, PanelMatch D w ℓ (addr X y) (panel X y) :=
    (panelSections (w := w) X fit ⟨v.layout, v.colour, v.offset, v.energy, tableAt Bt κ hκ D ℓ o c⟩).2
      (fun m _ => reads m)
  apply Iff.trans ?_ (panelSections (p.next c) child extra)
  cases o with
  | shrink i he X =>
    subst he
    have hk : (D.lv ℓ).shrink = true := row ▸ rfl
    obtain ⟨hc, ho, hl, ht⟩ := haux
    unfold C10at
    simp only [hk, ite_true, slotBits_eq fit.slots, slotBits_eq child.slots, lane, child.bases]
    exact C10sCode_stage Bt.shrink (S.shrink i) (ok.shrink i) _ D w ℓ X c fit.bases hpanel hc ho ht hl
  | refresh X =>
    have hk : (D.lv ℓ).shrink = false := row ▸ rfl
    unfold C10at
    simp only [hk, Bool.false_eq_true, ite_false, slotBits_eq fit.slots, slotBits_eq child.slots,
      lane, ok.degree, child.bases]
    exact C10rCode_stage S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      Bt.refresh S.port_order S.degree_bounds.2 ok.refresh _ D w ℓ X c fit.bases hpanel haux

end
end P1SolC10K.Sol
