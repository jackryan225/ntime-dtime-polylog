import P1Net.ContractProofPack

/-! The physical site predicate and the two source-terminal readouts shared by the encoder proofs. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) (input : List Bool)
  {g : ℕ} (L : GuessLayout V g)

local notation "zR" => runLabels V B I σ ha bset input
local notation "Wx" => strWidth V B

abbrev RunSite (ι : Fin I) (v : Loc V.K h) (l : BitWord h) : Prop :=
  rnSiteOK V B L I σ ha bset (((ι, v), false), l)
    (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst zR (((ι, v), false), l))

theorem run_port_source_out (ι : Fin I) (k : V.K) (δ : Fin 3) (l : BitWord h) :
    slotOut V B I σ ha zR (ι, .portIn k δ) l 0 Wx =
      runHistory V B I σ input k (portBlock I σ ι k δ (laneEquiv h l)) ((ι : ℕ) * 2 ^ h) := by
  have hm : locMate (.portIn k δ : Loc V.K h) 0 = some (.rt k (rcol0 h) (code3 δ), 2) := rfl
  rw [run_local_out (W := Wx) V B I σ ha bset input ι hm rfl l]
  exact asWord_self _

theorem run_state_source_out (ι : Fin I) (l : BitWord h) :
    slotOut V B I σ ha zR (ι,.eIn) l 0 Wx =
      runBoundary V B h input ((ι : ℕ) * 2 ^ h) (laneEquiv h l) := by
  have hm : locMate (.eIn : Loc V.K h) 0 = some (.st (scol0 h) (code1 false), 2) := rfl
  rw [run_local_out (W := Wx) V B I σ ha bset input ι hm rfl l]
  exact asWord_self _

end P1Net.AstraContract
