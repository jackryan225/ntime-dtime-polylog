import P1SolGreedy.GreedyBridgeScoutCopy
import P1ChkFinal.EnergyFit
import P1Int.RecordsFitProof

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Int P1Int.P11 P1Wit P1Wit.SolWitfill
open P1ChkFinal.EnergyFit

namespace P1SolGreedy.SolBridge

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- The local estimate, quantified over states fitting an actual row. -/
def fittedShrinkEnergy (D : Dims) : Prop :=
  ∀ ℓ, ℓ ≤ D.top → ∀ {a g : ℕ} (X : State a (packingLaneBits a g)),
    PanelFits D (D.lv ℓ) X → ∀ (s : X.ShrinkSelection Bt.shrink) (y : X.Base) (l : Bool),
      P1ChkGreedy.truePrefix X (P1ChkGreedy.termW Bt.shrink X s) y l < 2 ^ D.bigW

theorem energyOK_of_fit (D : Dims) (hrows : fittedShrinkEnergy Bt D)
    {a g b n ℓ : ℕ} {X : State a g} {p : StatePass F X b n}
    (o : PassOrigin Bt κ hκ p) (hℓ : ℓ ≤ D.top) (hf : PanelFits D (D.lv ℓ) X) :
    energyOK Bt κ hκ D.bigW o := by
  cases o with
  | shrink i h X =>
    subst h
    exact hrows ℓ hℓ X hf
  | refresh X => exact True.intro

theorem energyTree_of_fit (D : Dims) (hrows : fittedShrinkEnergy Bt D)
    {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) (o : PassOrigins Bt κ hκ E)
    (start : ℕ) (hf : ExecFits D E start) :
    energyTree Bt κ hκ D.bigW E o := by
  induction E generalizing start with
  | done => exact True.intro
  | more p tail ih =>
    exact ⟨energyOK_of_fit Bt κ hκ D hrows o.1 hf.1.le hf.2.1,
      fun i => ih i (o.2 i) (start + 1) (hf.2.2 i)⟩

end P1SolGreedy.SolBridge

open Filter P1Wrap P1Wit.SolSpace P1SolGreedy.SolBridge
open private live_choices live_execute from P1Int.RecordsFitProof

theorem P1SolGreedy.energyFitLong : P1ChkFinal.EnergyFit.EnergyFitLong := by
  intro k instK S Bt F instF instA κ hκ V a b d bigBias termBias hb
  let K := portConsts Bt
  let Cw := ShrinkMotif.fieldFactor Bt.shrink
  obtain ⟨C, hC⟩ := genuine_spaceIn Bt κ hκ K (toOAI V) 1 le_rfl (portConsts_b0 Bt)
    (portConsts_C2 Bt) (four_le_baseDegree S) d bigBias termBias
  obtain ⟨nF, hnF⟩ := recordsFit Bt κ hκ V a b d bigBias termBias hb
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x : List Bool, x.length = n →
      EnergyFitTarget Bt κ hκ V a b x d bigBias termBias := by
    filter_upwards [(tendsto_lpTime a b).eventually hC,
      (tendsto_lpTime a b).eventually (Scout.eventually_energy_fields_fit K C Cw),
      eventually_ge_atTop nF] with n hspace hbound hn
    intro x hx
    subst n
    intro σ
    let t := lpTime a b x.length
    let D := fixedDims Bt V a b x d bigBias termBias
    let E := fixedExec Bt κ hκ V a b x σ
    obtain ⟨c⟩ : Nonempty E.Choices := live_choices E (live_execute Bt κ hκ _ _ _)
    have hg : 2 * (a * (x.length ^ 2 + 1)) ≤ t := by dsimp [t, lpTime]; omega
    have hS : SpaceIn K 1 C t D (E.finalState c).totalWidth :=
      hspace _ hg σ c
    have hbig : 6 * Params.lam t ≤ D.bigW := Nat.le_add_left _ _
    refine energyTree_of_fit Bt κ hκ D ?_ E _ 0 ((hnF x hn).choose_spec.choose_spec.2.1 σ)
    intro ℓ hℓ aa gg X f s
    exact hbound D _ hS hbig ℓ hℓ X f.bases f.lanes f.slots _
      (Scout.supply_width_from_old X Bt.shrink s D.wW f.width)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  exact ⟨n₀, fun x hx => hn₀ x.length hx x rfl⟩

#print axioms P1SolGreedy.energyFitLong
