import P1Final.TwoInputsRec
import P1Net.P4

/-!
# P1Final.NetP4: the first open input is PROVED; C1 from ONE named Prop (owner: P1-lean-integ)

Lane net proved `P1Net.contractEqCount_holds` (P4 for the routed network, Astra's P1-astra-contract files compiled
unchanged; board 2000, jobs netC-49/50). So `P1Int.P11.OpenNetP4` holds, and the final theorem needs only
`P1Int.P11.OpenChecksRec`.
-/

namespace P1Final

/-- **Open input 1, PROVED**: the routed network count for every schedule, ring, machine, input and skeleton. -/
theorem netP4 : P1Int.P11.OpenNetP4 := by
  intro S F _ V a x Bk _ I _ h σ
  exact P1Net.contractEqCount_holds (P1Int.toOAI V) Bk (P1Int.P11.netLayout V a x) I σ (P1Int.four_le_baseDegree S)
    P1Benes.NetBridge.bset F

/-- **C1 from the one open input `OpenChecksRec`.** -/
theorem c1_of_checksRec (hchk : P1Int.P11.OpenChecksRec) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_net_and_checksRec netP4 hchk

end P1Final
