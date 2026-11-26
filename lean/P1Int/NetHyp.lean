import P1Int.NetGlue

/-!
# P1Int.NetHyp: the count hypothesis of P11 in NETWORK FORM (G3-chief queue item 3, first part)

Owner: P1-lean-integ (second restart, 2026-11-25). `P1Int.P11.CountHyp s` is the hypothesis from which the glue
proves Lemma P (`lemmaP_of_countHyp`). Its per-input part `CountInput` asks for an abstract network with the
identities `hacc`, `hP4`, `hP5`. `P1Int.NetGlue` proves these for lane net's routed network. This file states what is
LEFT after that step:

* `NetInput Bt κ hκ bs l V a b x letter answer chk m kk bnd`: for ONE input `x`, the parameters `B`, `I`, `h`, `Tc`
  (as `∃`: lanes pick `P1Wrap.Params`), `hn : Tc · S.laneBits ≤ h` (P10), the run bound `lpTime a b |x| ≤ I · 2^h · B`
  (net), lane net's open Prop `P1Net.ContractEqCount` for every skeleton candidate, the order `ord` of the final
  sites, the witness encoding `enc`, its injectivity (P6, Sol witfill), and `hchecks` (checkers + P6) for the count
  data `P1Int.P11.netData` (= `P1Count.NetData.ofExec` on lane net's networks).
* `NetHyp Bt κ hκ bs l s`: the text of `CountHyp s` with `CountInput` replaced by `NetInput`. The port data
  `S`, `Bt`, `F`, `κ`, `hκ`, `bs`, `l` are PARAMETERS (fixed once from `PortTwo`, see `P1Int.PortData`).
* `countInput_of_netInput`, `countHyp_of_netHyp : l 1 = 1 → NetHyp Bt κ hκ bs l s → CountHyp s`.

D7: `NetHyp` quantifies over clocks with `1 ≤ b` only (same as `CountHyp`).
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression OAI.Computability.VPVNP.WireTensor

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

open scoped Classical in
/-- **What is left for one input after the network glue** (TARGET SHAPE of lanes net, P6 / Sol witfill and the
checker lanes). `m` is the witness length and `kk` the selector length (`lpM2 s a b |x|`, `lpK2 a b |x|` in
`NetHyp`), `bnd` the budget of one check program. -/
def NetInput (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) {A : Type} (letter : Bool → A)
    (answer : Option A → Bool) (chk : ℕ → Option (Prog A)) (m kk bnd : ℕ) : Prop :=
  ∃ (Bk : ℕ) (_ : NeZero Bk) (I : ℕ) (_ : NeZero I) (h Tc : ℕ) (hn : Tc * S.laneBits ≤ h),
    lpTime a b x.length ≤ I * 2 ^ h * Bk ∧
    (∀ σ : NetSk V I h,
      P1Net.ContractEqCount (toOAI V) Bk (netLayout V a x) I σ (four_le_baseDegree S)
        P1Benes.NetBridge.bset F) ∧
    ∃ (ord : ∀ (σ : NetSk V I h)
        (ι : (Bt.execute κ hκ Tc hn (P1Net.rnState (toOAI V) Bk I σ (four_le_baseDegree S))).Choices),
        ((Bt.execute κ hκ Tc hn
            (P1Net.rnState (toOAI V) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site ≃
          Fin (Fintype.card ((Bt.execute κ hκ Tc hn
            (P1Net.rnState (toOAI V) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site))
      (enc : (netData Bt κ hκ V a x Bk I Tc hn ord).toCountData.Tup D → (Fin m → Bool))
      (_ : Function.Injective enc),
      ∀ u : Fin m → Bool,
        (∀ c < 2 ^ 4, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = kk - 4 →
          ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd) ↔
        ∃ t, (netData Bt κ hκ V a x Bk I Tc hn ord).toCountData.Valid bs l t ∧ enc t = u

/-- **The count hypothesis of P11 in network form** (D8 + the network glue): the text of `CountHyp s` with
`CountInput` replaced by `NetInput` for the fixed port data. -/
def NetHyp (s : ℝ) : Prop := ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A)) (c n₁ : ℕ),
    ∀ x : List Bool, n₁ ≤ x.length →
    4 ≤ lpK2 a b x.length ∧ ∃ bnd : ℕ, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
      (∀ u : Fin (lpM2 s a b x.length) → Bool, ∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc →
        ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
          ∃ v, ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) v bnd) ∧
      NetInput Bt κ hκ bs l V a b x letter answer chk (lpM2 s a b x.length) (lpK2 a b x.length) bnd

/-- `NetInput` gives `CountInput` (the network glue `countInput_of_net`). -/
theorem countInput_of_netInput (hl : l 1 = 1) {V : C1Challenge.Machine} {a b : ℕ} {x : List Bool}
    {A : Type} {letter : Bool → A} {answer : Option A → Bool} {chk : ℕ → Option (Prog A)} {m kk bnd : ℕ}
    (hin : NetInput Bt κ hκ bs l V a b x letter answer chk m kk bnd) :
    CountInput V a b x letter answer chk m kk bnd := by
  obtain ⟨Bk, hBk, I, hI, h, Tc, hn, hT, hP4, ord, enc, hinj, hchecks⟩ := hin
  haveI := hBk
  haveI := hI
  exact countInput_of_net Bt κ hκ V a x Bk I Tc hn b hT hP4 bs l hl ord letter answer chk m kk bnd enc
    hinj hchecks

/-- **`CountHyp` from the network form.** -/
theorem countHyp_of_netHyp (hl : l 1 = 1) {s : ℝ} (h : NetHyp Bt κ hκ bs l s) : CountHyp s := by
  intro L V a b n₀ hb1 hV
  obtain ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, c, n₁, hx⟩ := h L V a b n₀ hb1 hV
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, c, n₁, fun x hxn => ?_⟩
  obtain ⟨hk, bnd, hbnd, hcost, htot, hin⟩ := hx x hxn
  exact ⟨hk, bnd, hbnd, hcost, htot, countInput_of_netInput Bt κ hκ bs l hl hin⟩

end

end P11

end P1Int
