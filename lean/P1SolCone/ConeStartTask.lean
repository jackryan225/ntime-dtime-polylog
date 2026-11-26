import P1SolCone.InitialConeState
import P1SolCone.ConeScale

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code Staff Strip
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1SolFmt.SolFigure P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ)

abbrev QueryWords := Bits.Word × Bits.Word × Bits.Word

theorem coneTerminal_headerTask {F : Type} [Fintype F] :
    ∃ cost : Qry → ℕ, Dom (coneScale B V a b) cost ∧
      Task (fun q => coneScan B a b q + cost q) (fun q => send q)
        (fun q => send ((q.1,q.2.1), (smallQuery q,
          encodeConeState (initialConeState (F := F) (coneDims B V a b d bigBias termBias q.1.length)
            q.2.1 (Mbar B V a b q.1.length) (P1Batch.bval q.2.2))))) := by
  let σ := coneScale B V a b
  let h (q : Qry) := coneTerminalHeader B V a b d bigBias termBias (smallQuery q)
  let u (q : Qry) := q.2.1
  let x (q : Qry) := q.1
  let m (q : Qry) := smallQuery q
  let binN (q : Qry) := q.1.length |> bin
  let lay (q : Qry) := coneDims B V a b d bigBias termBias q.1.length
  let clk (q : Qry) := coneReadClock B V a b bigBias termBias (binN q)
  let newWidth (q : Qry) := Mbar B V a b q.1.length
  let w := fun p : QueryWords => P1Batch.bval p.1
  let dW (q : Qry) := coneFieldWidth B V a b bigBias termBias (w (m q))
  have hp := coneTerminalHeader_poly B V a b d bigBias termBias
  have hms : Dom σ (fun q => size (m q)) := smallQuery_dom B V a b
  have ht : Dom σ (fun q => size (h q)) := (hp.length.map m).sub hms
  have locW := diameter _ (coneFieldWidth_realizes B V a b bigBias termBias
    (Easy.fst.poly : Poly (Prod.fst : QueryWords → Bits.Word)))
  have hB : Dom σ dW := (locW.map m).sub hms
  have hcap : Dom σ (fun q => (h q).2.2.1) := by
    have H := diameter _ (coneMbarRealizes B V a b
      (Easy.fst.poly : Poly (Prod.fst : QueryWords → Bits.Word)))
    exact (H.map m).sub hms
  have hh (q : Qry) :
      h q = actualTerminalHeader (lay q) (u q).length (newWidth q) (P1Batch.bval q.2.2) (clk q) := by
    simp only [h, coneTerminalHeader, smallQuery, m, bval_bin, x, lay, u, clk, binN, newWidth]
  obtain ⟨⟨t₂,ht₂,run₂⟩,hreply⟩ := terminalReplay_task h u σ dW ht hB hcap
    (fun q => by rw [hh]; rfl) (fun q f hf => coneTerminalHeader_width B V a b d bigBias termBias (m q) f hf)
  let prep := (prepareConeQuery_easy.on (id : Qry → Qry))
  let wdata (q : Qry) := (x q, u q)
  let ml (q : Qry) := (m q,h q)
  obtain ⟨t₁,ht₁,run₁⟩ := (Code.Poly.identity.pair hp).on hms
  let reply (q : Qry) := replayTerminalPayload (h q) (u q)
  let out (q : Qry) := (m q,(h q,reply q))
  have put : Easy (fun p : (List Bool × List Bool) × (QueryWords × TerminalHeader) =>
      ((p.1.1,p.2), (p.1.2,p.2.2))) := by fun_prop
  have pull : Easy (fun p : (List Bool × (QueryWords × TerminalHeader)) × (List Bool × (Bool × HalfCode)) =>
      ((p.1.1,p.2.1),(p.1.2.1,p.1.2.2,p.2.2))) := by fun_prop
  have done : Poly (fun p : QueryWords × TerminalHeader × (Bool × HalfCode) =>
      (p.1, initialConeCode (F := F) p.2)) :=
    Easy.fst.poly.pair (Easy.snd.poly.compose initialConeCode_poly)
  have hpair : Dom σ (fun q => size (h q, reply q)) :=
    ((ht.add hreply).add (Dom.const σ 1)).mono (fun q => by rw [size_prod])
  have hOut : Dom σ (fun q => size (out q)) :=
    ((hms.add hpair).add (Dom.const σ 1)).mono (fun q => by change size (m q, (h q,reply q)) ≤ _; rw [size_prod])
  obtain ⟨t₃,ht₃,run₃⟩ := done.on hOut
  have hml : Dom σ (fun q => size (ml q)) :=
    ((hms.add ht).add (Dom.const σ 1)).mono (fun q => by change size (m q,h q) ≤ _; rw [size_prod])
  have setup := prep.compose (run₁.right (fun q => send (wdata q)))
  have prepareReplay := setup.compose (put.on (fun q => (wdata q,ml q)))
  have replay := prepareReplay.compose (run₂.right (fun q => send (x q,ml q)))
  have routed := replay.compose (pull.on (fun q => ((x q,ml q),(u q,reply q))))
  have exe := routed.compose (run₃.right (fun q => send (wdata q)))
  refine ⟨fun q => t₁ q + t₂ q + t₃ q + 3 * size (ml q) + size (reply q) + 20,
    (((((ht₁.add ht₂).add ht₃).add ((Dom.const σ 3).mul hml)).add hreply).add (Dom.const σ 20)), ?_⟩
  apply ((exe.bound 20 (fun q => ?_)).conform (fun q => rfl) (fun _ => rfl) (fun q => ?_))
  · have hScan : (x q).length + (u q).length + q.2.2.length + 1 ≤ coneScan B a b q :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h₁ : (send (wdata q)).count = size (wdata q) := rfl
    have h₂ : (send (x q,ml q)).count = size (x q,ml q) := rfl
    have hq : size q = 2 * (x q).length + 2 * (u q).length + 2 * q.2.2.length + 5 := by
      change size (x q,(u q,q.2.2)) = _
      simp only [size_prod,P1ChkFinal.size_listBool]
      omega
    simp only [h₁,h₂,wdata,id_eq,hq,size_prod,P1ChkFinal.size_listBool]
    omega
  · change send (wdata q,(m q,initialConeCode (F := F) (h q,replayTerminalPayload (h q) (u q)))) = _
    rw [hh]
    have haxis : ((lay q).lv (lay q).top).lanes * ((lay q).lv (lay q).top).slots ≤ (clk q).length := by
      have hN : P1Batch.bval (binN q) = q.1.length := bval_bin _
      have h := coneAxisClock_fits B V a b d bigBias termBias (binN q)
      specialize h (lay q).top
      rw [hN] at h
      exact (h le_rfl).trans (coneReadClock_axes B V a b bigBias termBias (binN q))
    have hslots : ((lay q).lv (lay q).top).slots ≤ (clk q).length := by
      have pos := (coneDims_rowBounds B V a b d bigBias termBias q.1.length (lay q).top le_rfl).lanes_eq
      exact (Nat.le_mul_of_pos_left _ (by rw [pos]; exact Nat.two_pow_pos _)).trans haxis
    rw [initialConeCode_eq _ _ _ _ _ hslots haxis]

end

end P1SolCone.SolCone
