import P1Net.ContractProofSites
import P1Net.ContractProofLinks
import P1Net.ContractProofSwitchSites

/-! The accepting run gives a satisfying physical labelling with the prescribed first pins. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  {g : ℕ} (L : GuessLayout V g)

/-- A complete accepting guess supplies a concrete labelling satisfying every actual physical site. -/
noncomputable def encodeRun (route : Routes bset) (w : GoodGuess V B L I σ) : RoutedGood V B L I σ ha bset := by
  refine ⟨runLabels V B I σ ha bset (L.input w.val), ?_⟩
  intro u
  obtain ⟨⟨⟨ι,v⟩, twin⟩,l⟩ := u
  cases twin with
  | true => exact True.intro
  | false =>
    cases v with
    | tabC => exact run_center_ok V B I σ ha bset L w ι l
    | tabP c => exact run_path_ok V B I σ ha bset (L.input w.val) L w.property.2 route ι l c
    | portIn k δ => exact run_port_in_ok V B I σ ha bset L w.val ι k δ l
    | portOut k δ => exact run_port_out_ok V B I σ ha bset (L.input w.val) L route ι l k δ
    | rt k c π => exact run_rt_ok V B I σ ha bset (L.input w.val) L route ι k c π l
    | st c π => exact run_st_ok V B I σ ha bset (L.input w.val) L ι c π l
    | eIn => exact run_ein_ok V B I σ ha bset (L.input w.val) L ι l
    | eOut => exact run_eout_ok V B I σ ha bset (L.input w.val) L route ι l

theorem encodeRun_pins (route : Routes bset) (w : GoodGuess V B L I σ) (k : V.K) (Z : ℤ)
    (ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) :
    seedWord V B I σ ha (encodeRun V B I σ ha bset L route w).val k Z =
      encC V B (initBlock (B := B) (L.input w.val) k Z) :=
  run_seedWord V B I σ ha bset (L.input w.val) k Z ex

end P1Net.AstraContract
