import P1SolF0R.HeaderStages

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Int P1Wrap P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

noncomputable section

def readFactor0 {F : Type} [CommRing F] (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (test : EntryCode → Bool) (cross : CrossIn → Bool) (a b bigBias : ℕ)
    (p : RawInput (Offered F)) : List (Label F) :=
  let args := withClocks a b bigBias p.1.1.length
  let plans := batchAdvance (witnessRequests V.K) (planHeaders V tape cross) p.1.2 p.2 args
  finish test (batchAdvance pinRequests (resolveEntries V) p.1.1 plans args)

private def widthPerInterval (r : ℕ) (p : PublicClocks) : ℕ :=
  p.1.2.1 * r * 2 + r * p.1.2.2.2.2.1 + 2 * (r * 3 * p.1.2.2.2.2.1)

private theorem intervalWidth_dom (a b bigBias r : ℕ) :
    Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => widthPerInterval r (withClocks a b bigBias n)) := by
  let log := fun n : ℕ => Nat.log 2 (n + 1)
  have hN : Dom log (fun n => Params.N (lpTime a b n)) := (block_dom a b).mono (fun n => by
    unfold Params.bb
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right _ (Params.B_pos _))
  have hw : Dom log (fun n => bigBias + 6 * Params.lam (lpTime a b n)) :=
    (Dom.const _ _).add ((Dom.const _ _).mul (lam_lpTime_dom a b))
  refine (((hN.mul (Dom.const log r)).mul (Dom.const log 2)).add
    (((Dom.const log r).mul hw).add ((Dom.const log 2).mul (((Dom.const log r).mul
      (Dom.const log 3)).mul hw)))).mono (fun n => ?_)
  simp only [widthPerInterval, withClocks, publicParams]
  omega

private theorem witnessRequests_total {F : Type} (K : Type) [Fintype K] (p : PublicClocks × Offered F) :
    P1Batch.total (witnessRequests K p) ≤ p.2.2.length * widthPerInterval (Fintype.card K) p.1 := by
  apply total_flatMap_le
  intro q _
  exact (total_intervalReqs _ _ _ _ _).le

private theorem total_map_pin_le (qs : List PinQuery) :
    P1Batch.total (qs.map pinReq) ≤ qs.length := by
  induction qs with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    change P1Batch.bval (pinReq q).2 + P1Batch.total (qs.map pinReq) ≤ qs.length + 1
    have hq : P1Batch.bval (pinReq q).2 ≤ 1 := by cases q <;> simp only [pinReq] <;> decide
    omega

private theorem pinRequests_total {F : Type} (p : PublicClocks × PlannedList F) :
    P1Batch.total (pinRequests p) ≤ p.2.2.length * p.1.2.2.1.length := by
  apply total_flatMap_le
  intro q _
  have h := total_map_pin_le ((List.range p.1.2.2.1.length).map fun j => readAt (.inl 0) q.1.2 j)
  simpa only [reqPins, List.map_map, List.length_map, List.length_range, Function.comp_def] using h

set_option maxHeartbeats 1000000 in
/-- Compile the two batches and the entry test with the budget of the frozen target. -/
theorem readFactor0_computes {F : Type} [CommRing F] [Fintype F]
    (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (test : EntryCode → Bool) (cross : CrossIn → Bool)
    (htest : Poly test) (hcross : Poly cross) (a b bigBias : ℕ) :
    ∃ e : ℕ, Computes (fun p : RawInput (Offered F) =>
      p.1.1.length + p.1.2.length + (size p.2 + Nat.log 2 (p.1.1.length + 1) + 1) ^ e)
      (readFactor0 V tape test cross a b bigBias) := by
  letI : Inhabited (Label F) := ⟨⟨0⟩⟩
  let x (p : RawInput (Offered F)) := p.1.1
  let u (p : RawInput (Offered F)) := p.1.2
  let s (p : RawInput (Offered F)) := size p.2 + Nat.log 2 ((x p).length + 1)
  let σ (p : RawInput (Offered F)) := s p + Nat.log 2 ((u p).length + 1)
  let A (p : RawInput (Offered F)) := withClocks a b bigBias (x p).length
  let small (p : RawInput (Offered F)) := (((x p).length, (u p).length), p.2)
  let planned (p : RawInput (Offered F)) := batchAdvance (witnessRequests V.K) (planHeaders V tape cross) (u p) p.2 (A p)
  let ready (p : RawInput (Offered F)) := batchAdvance pinRequests (resolveEntries V) (x p) (planned p) (A p)
  have hs : Dom σ (fun p => size p.2) := (Dom.base σ).mono (fun p => by dsimp [σ, s]; omega)
  have hxl : Dom σ (fun p => Nat.log 2 ((x p).length + 1)) :=
    (Dom.base σ).mono (fun p => by dsimp [σ, s]; omega)
  have hul : Dom σ (fun p => Nat.log 2 ((u p).length + 1)) :=
    (Dom.base σ).mono (fun p => by dsimp [σ]; omega)
  have hx : Dom σ (fun p => size (x p).length) :=
    (((Dom.const σ 2).mul hxl).add (Dom.const σ 3)).mono (fun p => binary_size_le_log (x p).length)
  have hu : Dom σ (fun p => size (u p).length) :=
    (((Dom.const σ 2).mul hul).add (Dom.const σ 3)).mono (fun p => binary_size_le_log (u p).length)
  have hlen : Dom σ (fun p => size ((x p).length, (u p).length)) :=
    ((hx.add hu).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  have hA : Dom σ (fun p => size (A p)) := ((withClocks_poly a b bigBias).length.map
    (fun p => (x p).length)).sub hx
  have hlocal : Dom σ (fun p => size (A p, p.2)) :=
    ((hA.add hs).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  have hin : Dom σ (fun p => size (((x p).length, (u p).length), (A p, p.2))) :=
    ((hlen.add hlocal).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  have hsi : Dom σ (fun p => size (small p)) :=
    ((hlen.add hs).add (Dom.const σ 1)).mono (fun p => by simp only [small, size_prod, le_refl])
  have hw : Dom σ (fun p => widthPerInterval (Fintype.card V.K) (A p)) :=
    ((intervalWidth_dom a b bigBias (Fintype.card V.K)).map (fun p => (x p).length)).sub hxl
  have hn : Dom σ (fun p => p.2.2.length) := hs.mono (fun p =>
    (P1ChkFinal.length_le_size _).trans (by rw [size_prod]; omega))
  have h₁ : Dom σ (fun p => P1Batch.total (witnessRequests V.K (A p, p.2))) :=
    (hn.mul hw).mono (fun p => witnessRequests_total V.K (A p, p.2))
  have hp := batch_output_dom (witnessRequests V.K) (planHeaders V tape cross)
    (witnessRequests_poly V.K) (planHeaders_poly V tape hcross) u A (fun p => p.2) σ hlocal h₁
  have hp' : Dom σ (fun p => size (planned p)) := hp
  have hnp : Dom σ (fun p => (planned p).2.length) := hp'.mono (fun p =>
    (P1ChkFinal.length_le_size _).trans (by rw [size_prod]; omega))
  have hb : Dom σ (fun p => (A p).2.2.1.length) := hA.mono (fun p =>
    (P1ChkFinal.length_le_size _).trans (by simp only [size_prod]; omega))
  have h₂ : Dom σ (fun p => P1Batch.total (pinRequests (A p, planned p))) :=
    (hnp.mul hb).mono (fun p => pinRequests_total (A p, planned p))
  obtain ⟨c₁, hc₁, hbatch⟩ := twoBatches_task (witnessRequests V.K) (planHeaders V tape cross)
    pinRequests (resolveEntries V) (witnessRequests_poly V.K) (planHeaders_poly V tape hcross)
    pinRequests_poly (resolveEntries_poly V) x u A (fun p => p.2) σ hin h₁ h₂
  have hready := batch_output_dom pinRequests (resolveEntries V) pinRequests_poly (resolveEntries_poly V)
    x A planned σ (((hA.add hp').add (Dom.const σ 1)).mono (fun p => by rw [size_prod])) h₂
  let addClocks (v : (ℕ × ℕ) × Offered F) := (v.1, (withClocks a b bigBias v.1.1, v.2))
  have hac : Poly addClocks :=
    Easy.fst.poly.pair ((Easy.fst.poly.fstCompose.compose (withClocks_poly a b bigBias)).pair Easy.snd.poly)
  obtain ⟨c₂, hc₂, hprepare⟩ := hac
  obtain ⟨c₃, hc₃, hfinish⟩ := finish_poly (F := F) htest
  let c (p : RawInput (Offered F)) := size p.2 + c₂ (small p) + c₁ p + c₃ (ready p)
  have hc : Dom σ c := ((hs.add ((hc₂.map small).sub hsi)).add hc₁).add ((hc₃.map ready).sub hready)
  have hrun := (((measureInput_task (S := Offered F)).compose
    ((hprepare.on small).right (fun p => send (x p, u p)))).compose hbatch).compose (hfinish.on ready)
  obtain ⟨e, C, hC⟩ := absorb_budget (fun p => (x p).length) (fun p => (u p).length) s c hc
  refine ⟨e, hrun.bound (4 * C) (fun p => ?_)⟩
  have hsum : (x p).length + (u p).length + size p.2 + (size (x p, u p) + c₂ (small p)) +
      ((x p).length + (u p).length + c₁ p) + c₃ (ready p) + 1 ≤
        4 * ((x p).length + (u p).length + c p + 1) := by
    simp only [c, size_prod, P1ChkFinal.size_listBool]
    omega
  exact hsum.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 (hC p))

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.readFactor0_computes
