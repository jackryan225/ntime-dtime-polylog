import P1Int.P11Count
import P1Net.Interface
import P1Count.LinkP5

/-!
# P1Int.NetGlue: the network inputs of the parity count, from lane net's objects (G3-chief queue item 2)

Owner: P1-lean-integ (second restart, 2026-11-25). `P1Int.P11.CountInput` (the per-input hypotheses of
`P1Count.lemmaP_count`) asks for a network `Xn σ` per skeleton candidate, unscaled factors `F1 σ`, a scalar
factor `e σ` at one site, the accept counts `acc σ`, a run bound `T`, and the identities `hacc`, `hP4`, `hP5`.
This file INSTANTIATES all of them with lane net's routed network and proves `hacc`, `hP4`, `hP5`, `he`, `hes`:

* `Xn σ := (P1Net.rnState (toOAI V) B I σ ha).network` at the base degree of the block schedule `S`
  (`ha := P1Int.four_le_baseDegree S`), i.e. `(P1Net.rnStateOf ..).network`;
* `F1 σ := netF1` = the `0/1` indicator of `P1Net.rnSiteOK` (canonical Beneš settings `P1Benes.NetBridge.bset`);
* `e σ := netE` = `2 ^ P1Net.uOwned` at `P1Net.scalarSite`, `1` elsewhere; `netFactors_eq`: `e σ u * F1 σ u z`
  is `P1Net.rnFactors` (the text of lane net);
* `acc σ := netAcc` = the number of guesses `w` with an accepting run of `toOAI V` on `withGuess w x` within
  `T = I · 2^h · B` steps and skeleton `σ`; `sum_netAcc`: their sum is `accCount V a x T` (`hacc`);
* `net_hP4`: `hP4` from lane net's open Prop `P1Net.ContractEqCount` (through `P1Net.contract_rn_eq_count`,
  routing hypothesis discharged by `P1Benes.NetBridge.route_bset`);
* `netData` := `P1Count.NetData.ofExec` on these networks (compressor execution of OpenAI's Theorem 7.1), so
  `hP5` is `P1Count.NetData.ofExec_hP5` (= `P1P5.contract_eq_push`, PROVED by lane P5).

`countInput_of_net`: `CountInput V a b x ..` from
  (net)  `hT : lpTime a b |x| ≤ I · 2^h · B` and `hP4 : ∀ σ, P1Net.ContractEqCount ..` (lane net's open Prop),
  (P10)  `hn : Tc · S.laneBits ≤ h`,
  (P0)   a basis `bs` of `F` over `ZMod 2` and a functional `l` with `l 1 = 1`,
  (P6)   the order `ord` of the final sites, the witness encoding `enc`, `Function.Injective enc`,
  (checks + P6) `hchecks`.
Nothing else is assumed: the verifier input layout is `P1Net.withGuessLayout` (text of `C1Challenge.withGuess`).
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression OAI.Computability.VPVNP.WireTensor

noncomputable section

/-- Lane net's verifier input is the Challenge text `withGuess`. -/
theorem guessWord_eq_withGuess (u x : List Bool) :
    P1Net.guessWord u x = C1Challenge.withGuess u x := rfl

section Net

variable (Vc : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  (h : ℕ)

/-- The guess layout of the verifier input `withGuess w x` with `a (|x|² + 1)` guess bits (lane net). -/
abbrev netLayout : P1Net.GuessLayout (toOAI Vc) (a * (x.length ^ 2 + 1)) :=
  P1Net.withGuessLayout (M := toOAI Vc) x (a * (x.length ^ 2 + 1))

/-- Skeleton candidates of the routed network: `I · 2^h` small intervals. -/
abbrev NetSk : Type := Fin (I * 2 ^ h) → (toOAI Vc).K → Fin 3

open scoped Classical in
/-- The number of guesses whose run accepts within `I · 2^h · B` steps and has skeleton `σ`. -/
def netAcc (σ : NetSk Vc I h) : ℕ :=
  (Finset.univ.filter fun w : Fin (a * (x.length ^ 2 + 1)) → Bool =>
    MultiTapeHaltsIn (toOAI Vc) (C1Challenge.withGuess (List.ofFn w) x) true (I * 2 ^ h * Bk) ∧
      P1Net.skeleton (toOAI Vc) (C1Challenge.withGuess (List.ofFn w) x) Bk (I * 2 ^ h) = σ).card

open scoped Classical in
/-- **`hacc`.** Every run has exactly one skeleton: the counts `netAcc σ` add up to the accepting guesses. -/
theorem sum_netAcc :
    ∑ σ : NetSk Vc I h, netAcc Vc a x Bk I h σ = accCount Vc a x (I * 2 ^ h * Bk) := by
  unfold netAcc accCount
  exact P1Net.sum_card_skeleton
    (fun w : Fin (a * (x.length ^ 2 + 1)) → Bool =>
      MultiTapeHaltsIn (toOAI Vc) (C1Challenge.withGuess (List.ofFn w) x) true (I * 2 ^ h * Bk))
    (fun w => P1Net.skeleton (toOAI Vc) (C1Challenge.withGuess (List.ofFn w) x) Bk (I * 2 ^ h))

variable {da : ℕ} (hda : 4 ≤ 2 ^ da) (F : Type) [CommRing F]

open scoped Classical in
/-- The unscaled factors: the `0/1` indicators of lane net's site predicate `rnSiteOK`. -/
abbrev netF1 (σ : NetSk Vc I h) : Factors F (P1Net.rnState (toOAI Vc) Bk I σ hda).network :=
  fun u z =>
    if P1Net.rnSiteOK (toOAI Vc) Bk (netLayout Vc a x) I σ hda P1Benes.NetBridge.bset u z then 1 else 0

open scoped Classical in
/-- The scalar factor: `2 ^ uOwned` at lane net's `scalarSite`, `1` at every other site. -/
abbrev netE (σ : NetSk Vc I h) : (P1Net.rnState (toOAI Vc) Bk I σ hda).network.Site → F :=
  fun u =>
    if u = P1Net.scalarSite (toOAI Vc) Bk I σ hda then
      (2 : F) ^ P1Net.uOwned (toOAI Vc) Bk (netLayout Vc a x) I σ
    else 1

/-- The product of the scalar factor and the unscaled factors is lane net's `rnFactors` (same text). -/
theorem netFactors_eq (σ : NetSk Vc I h) :
    (fun u z => netE Vc a x Bk I h hda F σ u * netF1 Vc a x Bk I h hda F σ u z) =
      P1Net.rnFactors (toOAI Vc) Bk (netLayout Vc a x) I σ hda P1Benes.NetBridge.bset F := by
  first
    | rfl
    | (funext u z; unfold P1Net.rnFactors; congr)
    | (funext u z; unfold P1Net.rnFactors; congr!)

/-- **`hP4`** from lane net's `ContractEqCount` (P4, routed, with the scalar). -/
theorem net_hP4 (σ : NetSk Vc I h)
    (hP4 : P1Net.ContractEqCount (toOAI Vc) Bk (netLayout Vc a x) I σ hda P1Benes.NetBridge.bset F) :
    contract (P1Net.rnState (toOAI Vc) Bk I σ hda).network
        (fun u z => netE Vc a x Bk I h hda F σ u * netF1 Vc a x Bk I h hda F σ u z) =
      (netAcc Vc a x Bk I h σ : F) := by
  have h1 := P1Net.contract_rn_eq_count (toOAI Vc) Bk (netLayout Vc a x) I hda σ F hP4
  rw [← netFactors_eq Vc a x Bk I h hda F σ] at h1
  unfold netAcc
  first
    | exact h1
    | (convert h1 using 3)

end Net

section Exec

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (Vc : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h)

/-- **The count data of one input**: lane count's `NetData.ofExec` on lane net's routed networks at the base
degree of `S`, with the indicator factors `netF1`, the scalar exponent `P1Net.uOwned` and the counts `netAcc`.
`ord` (P6) orders the final sites of each branch. -/
abbrev netData
    (ord : ∀ (σ : NetSk Vc I h)
      (ι : (Bt.execute κ hκ Tc hn (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).Choices),
      ((Bt.execute κ hκ Tc hn
          (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site ≃
        Fin (Fintype.card ((Bt.execute κ hκ Tc hn
          (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site)) :
    P1Count.NetData F :=
  P1Count.NetData.ofExec Bt κ hκ (NetSk Vc I h) Tc hn
    (fun σ => P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))
    (fun σ => netF1 Vc a x Bk I h (four_le_baseDegree S) F σ) ord
    (fun σ => P1Net.uOwned (toOAI Vc) Bk (netLayout Vc a x) I σ)
    (fun σ => netAcc Vc a x Bk I h σ)

open scoped Classical in
/-- **Glue: `CountInput` from lane net's P4, the run bound, P0, P6 and the checks.** The network, the factors,
the scalar site, the accept counts, `hacc`, `hP4`, `hP5`, `he`, `hes` are supplied here. -/
theorem countInput_of_net [Algebra (ZMod 2) F] (b : ℕ)
    (hT : lpTime a b x.length ≤ I * 2 ^ h * Bk)
    (hP4 : ∀ σ : NetSk Vc I h,
      P1Net.ContractEqCount (toOAI Vc) Bk (netLayout Vc a x) I σ (four_le_baseDegree S)
        P1Benes.NetBridge.bset F)
    {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (ord : ∀ (σ : NetSk Vc I h)
      (ι : (Bt.execute κ hκ Tc hn (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).Choices),
      ((Bt.execute κ hκ Tc hn
          (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site ≃
        Fin (Fintype.card ((Bt.execute κ hκ Tc hn
          (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))).finalState ι).network.Site))
    {A : Type} (letter : Bool → A) (answer : Option A → Bool) (chk : ℕ → Option (Prog A))
    (m kk bnd : ℕ)
    (enc : (netData Bt κ hκ Vc a x Bk I Tc hn ord).toCountData.Tup D → (Fin m → Bool))
    (hinj : Function.Injective enc)
    (hchecks : ∀ u : Fin m → Bool,
      (∀ c < 2 ^ 4, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = kk - 4 →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd) ↔
      ∃ t, (netData Bt κ hκ Vc a x Bk I Tc hn ord).toCountData.Valid bs l t ∧ enc t = u) :
    CountInput Vc a b x letter answer chk m kk bnd := by
  have hsum : ∑ σ, (netData Bt κ hκ Vc a x Bk I Tc hn ord).acc σ =
      accCount Vc a x (I * 2 ^ h * Bk) := sum_netAcc Vc a x Bk I h
  have h4 : ∀ σ : NetSk Vc I h,
      contract (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S)).network
        (fun u z => netE Vc a x Bk I h (four_le_baseDegree S) F σ u *
          netF1 Vc a x Bk I h (four_le_baseDegree S) F σ u z) =
      ((netData Bt κ hκ Vc a x Bk I Tc hn ord).acc σ : F) :=
    fun σ => net_hP4 Vc a x Bk I h (four_le_baseDegree S) F σ (hP4 σ)
  have h5 := fun σ : NetSk Vc I h => P1Count.NetData.ofExec_hP5 Bt κ hκ (NetSk Vc I h) Tc hn
    (fun σ => P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S))
    (fun σ => netF1 Vc a x Bk I h (four_le_baseDegree S) F σ) ord
    (fun σ => P1Net.uOwned (toOAI Vc) Bk (netLayout Vc a x) I σ)
    (fun σ => netAcc Vc a x Bk I h σ) σ
  have he : ∀ (σ : NetSk Vc I h) (u : (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S)).network.Site),
      u ≠ P1Net.scalarSite (toOAI Vc) Bk I σ (four_le_baseDegree S) →
        netE Vc a x Bk I h (four_le_baseDegree S) F σ u = 1 := fun _ _ hu => if_neg hu
  have hes : ∀ σ : NetSk Vc I h,
      netE Vc a x Bk I h (four_le_baseDegree S) F σ
          (P1Net.scalarSite (toOAI Vc) Bk I σ (four_le_baseDegree S)) =
        (2 : F) ^ (netData Bt κ hκ Vc a x Bk I Tc hn ord).unowned σ := fun _ => if_pos rfl
  unfold CountInput
  refine ⟨F, ‹CommRing F›, ‹Algebra (ZMod 2) F›, netData Bt κ hκ Vc a x Bk I Tc hn ord, D, bs, l, hl, ?_⟩
  refine ⟨fun σ => (P1Net.rnState (toOAI Vc) Bk I σ (four_le_baseDegree S)).network,
    fun σ => netF1 Vc a x Bk I h (four_le_baseDegree S) F σ, ?_⟩
  refine ⟨fun σ => P1Net.scalarSite (toOAI Vc) Bk I σ (four_le_baseDegree S),
    fun σ => netE Vc a x Bk I h (four_le_baseDegree S) F σ, ?_⟩
  refine ⟨he, hes, ?_⟩
  refine ⟨enc, hinj, I * 2 ^ h * Bk, hT, ?_⟩
  refine ⟨hsum, ?_⟩
  refine ⟨h4, ?_⟩
  refine ⟨h5, ?_⟩
  exact hchecks

end Exec

end

end P11

end P1Int
