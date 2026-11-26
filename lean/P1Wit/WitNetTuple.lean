import P1Wit.WitDirRecords
import P1Wit.WitExecutionRecords
import P1Count.LinkP5
import P1Int.Bridge
import P1Int.Expander
import P1Net.Factors

namespace P1Wit

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel
open P1Int SolWitfill

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h)

namespace SolWitfill

abbrev RoutedSkeleton (V : C1Challenge.Machine) (I h : ℕ) :=
  Fin (I * 2 ^ h) → (toOAI V).K → Fin 3

abbrev routedState (σ : RoutedSkeleton V I h) :=
  P1Net.rnState (toOAI V) Bk I σ (four_le_baseDegree S)

abbrev netExecution (σ : RoutedSkeleton V I h) :=
  Bt.execute κ hκ Tc hn (routedState (S := S) V Bk I σ)

end SolWitfill

/-- The D9 site order supplied to the network count for every branch. -/
def netSiteOrder (σ : RoutedSkeleton V I h) (ι : (netExecution Bt κ hκ V Bk I Tc hn σ).Choices) :
    ((netExecution Bt κ hκ V Bk I Tc hn σ).finalState ι).network.Site ≃
      Fin (Fintype.card ((netExecution Bt κ hκ V Bk I Tc hn σ).finalState ι).network.Site) :=
  stateOrd ((netExecution Bt κ hκ V Bk I Tc hn σ).finalState ι)

namespace SolWitfill

/-- Renumber the small intervals and tapes of the actual routed skeleton. -/
def netSkeleton {D : Dims} (hI : D.I = I) (hN : D.N = 2 ^ h)
    (ρ : (toOAI V).K ≃ Fin D.r) : RoutedSkeleton V I h ↪ Skeleton D :=
  let e : Fin (D.I * D.N) ≃ Fin (I * 2 ^ h) := finCongr (by rw [hI, hN])
  { toFun := fun σ i j => σ (e i) (ρ.symm j)
    inj' := by
      intro σ σ' eq
      funext i j
      simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
        congrFun (congrFun eq (e.symm i)) (ρ j) }

/-- Bounded local records needed to make the witness of a routed tuple.
Panels are indexed by the actual execution states. Term tables are supplied
at the nodes where those admitted choices occur. -/
structure NetRecordInputs (D : Dims) (d : ℕ) where
  interval_count : D.I = I
  initial_lanes : D.N = 2 ^ h
  tape_order : (toOAI V).K ≃ Fin D.r
  start_fits : ∀ (σ : RoutedSkeleton V I h) (i : Fin D.I) (j : Fin D.r),
    zigzag (P1Net.betaOf (netSkeleton V I interval_count initial_lanes tape_order σ)
      j (i.val * D.N)) < 2 ^ D.bigW
  panels : ∀ σ, ExecutionPanels D (netExecution Bt κ hκ V Bk I Tc hn σ) 0
  terms : ∀ σ, ExecutionTerms D (netExecution Bt κ hκ V Bk I Tc hn σ) 0
  owner_fits : D.I < 2 ^ D.bigW
  terms_fits_flag : 0 < D.wW
  chain_fits_len : ∀ σ ι,
    Fintype.card ((netExecution Bt κ hκ V Bk I Tc hn σ).finalState ι).network.Site + 1 ≤ D.chainLen
  chain_fits_entry : d ≤ 2 ^ D.chainW
  omega_fits : ∀ σ ι (y : Fin (D.lv D.top).bases),
    widthPrefix (finValue ((panels σ).final (netExecution Bt κ hκ V Bk I Tc hn σ) ι).fits.wireWidth)
      (y.val * ((D.lv D.top).lanes * (D.lv D.top).slots)) < 2 ^ D.bigW

end SolWitfill

variable [Algebra (ZMod 2) F]
  (F1 : ∀ σ : RoutedSkeleton V I h, Factors F (routedState (S := S) V Bk I σ).network)
  (unowned acc : RoutedSkeleton V I h → ℕ)

namespace SolWitfill

abbrev orderedCountData : P1Count.CountData F :=
  (P1Count.NetData.ofExec Bt κ hκ (RoutedSkeleton V I h) Tc hn (routedState (S := S) V Bk I)
    F1 (netSiteOrder Bt κ hκ V Bk I Tc hn) unowned acc).toCountData

/-- Assemble the records for a routed execution with its D9 order. -/
def netTupleRecords {D : Dims} {d : ℕ}
    (H : NetRecordInputs Bt κ hκ V Bk I Tc hn D d) :
    TupleRecords D (orderedCountData Bt κ hκ V Bk I Tc hn F1 unowned acc) d where
  skeleton := netSkeleton V I H.interval_count H.initial_lanes H.tape_order
  directory := fun σ => directoryOfSkeleton
    (netSkeleton V I H.interval_count H.initial_lanes H.tape_order σ)
    (H.tape_order (toOAI V).inputTape) (fun q => (q.val : ℤ)) (H.start_fits σ)
  level := fun σ => levelOfExecution (netExecution Bt κ hκ V Bk I Tc hn σ) (H.panels σ) (H.terms σ)
  branch_injective := fun σ => levelOfExecution_terms_injective _ (H.panels σ) (H.terms σ)
  payload := fun σ => payloadOfExecution _ (H.panels σ) (H.terms σ)
  owner_fits := H.owner_fits
  terms_fits_flag := H.terms_fits_flag
  chain_fits_len := H.chain_fits_len
  chain_fits_entry := H.chain_fits_entry
  omega_fits := fun σ ι y => by
    rw [levelOfExecution_final]
    exact H.omega_fits σ ι y

variable {D : Dims} {d : ℕ}
  (H : NetRecordInputs Bt κ hκ V Bk I Tc hn D d)

omit [NeZero Bk] [Algebra (ZMod 2) F] in
/-- The payload-size input to P6 is exactly the final total width from P5. -/
theorem netTuple_payload_length
    (t : (orderedCountData Bt κ hκ V Bk I Tc hn F1 unowned acc).Tup d) :
    (tuplePayload (netTupleRecords Bt κ hκ V Bk I Tc hn F1 unowned acc H) t).length =
      ((netExecution Bt κ hκ V Bk I Tc hn t.1).finalState t.2.1).totalWidth :=
  payloadOfExecution_length _ (H.panels t.1) (H.terms t.1) t.2.1 t.2.2.1

omit [NeZero Bk] [Algebra (ZMod 2) F] in
/-- The encoder's injectivity for the routed execution. -/
theorem encExecTuple_injective (m : ℕ)
    (hm : ∀ t, D.fixedLen + (tuplePayload (netTupleRecords Bt κ hκ V Bk I Tc hn F1 unowned acc H) t).length ≤ m) :
    Function.Injective (encTuple (netTupleRecords Bt κ hκ V Bk I Tc hn F1 unowned acc H) m) :=
  encTuple_injective _ m hm

end SolWitfill

end

end P1Wit

#print axioms P1Wit.netSiteOrder
#print axioms P1Wit.SolWitfill.netTupleRecords
#print axioms P1Wit.SolWitfill.netTuple_payload_length
#print axioms P1Wit.SolWitfill.encExecTuple_injective
