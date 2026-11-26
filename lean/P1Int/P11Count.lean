import P1Int.P11
import P1Count.Main
import P1Wrap.ProgDet

/-!
# P1Int.P11Count: Lemma P from the ADOPTED count and dispatcher (D8), every other piece a hypothesis

Owner: P1-lean-integ. G3-chief D8 (board 11:00:32Z) adopted `P1Count.R` (dispatcher, `d = 4` family bits) and
`P1Count.lemmaP_count` (the count). This file is the P11 glue on top of them: `CountInput` lists the per-input
hypotheses of `P1Count.lemmaP_count` VERBATIM (the other lanes supply them), `CountHyp` adds the check programs,
their totality and the cost bound, and `lemmaP_of_countHyp : CountHyp s → LemmaP s` is sorry-free.
What the glue itself proves (not hypotheses): the language clause `hL` of `lemmaP_count` (from `P1Int.parDecides_oai`
and `hacc`), the totality of `R` (`P1Count.R_total`), and the change of the budget from `4·4 + bnd` to
`lpCost2 c s a b |x|` (monotonicity, and uniqueness of answers `P1Wrap.progAnswers_unique`).
The generic form (any dispatcher, staged checks) stays in `P1Int.P11` (`SetupHyp`).
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel OAI.Computability.VPVNP.WireTensor
open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- `ProgAnswers` is monotone in the budget. -/
theorem progAnswers_mono {A : Type} {R : Prog A} {answer : Option A → Bool} {regs : Reg A} {v : Bool}
    {B B' : ℕ} (h : ProgAnswers R answer regs v B) (hB : B ≤ B') : ProgAnswers R answer regs v B' := by
  obtain ⟨n, hn, r, hr, hv⟩ := h
  exact ⟨n, hn.trans hB, r, hr, hv⟩

/-- A program that answers within `B` answers `true` within `B` iff it does within any `B' ≥ B`. -/
theorem progAnswers_true_iff {A : Type} {R : Prog A} {answer : Option A → Bool} {regs : Reg A}
    {B B' : ℕ} (htot : ∃ v, ProgAnswers R answer regs v B) (hB : B ≤ B') :
    ProgAnswers R answer regs true B ↔ ProgAnswers R answer regs true B' := by
  refine ⟨fun h => progAnswers_mono h hB, fun h => ?_⟩
  obtain ⟨v, hv⟩ := htot
  have hvt : v = true := P1Wrap.progAnswers_unique hv h
  subst hvt
  exact hv

open scoped Classical in
/-- **The per-input hypotheses of `P1Count.lemmaP_count`** (VERBATIM, `d = 4`), plus the run bound `T` and the
skeleton sum `hacc` from which the glue derives `hL`. Owners: P0 (wrap) `F`, `bs`, `l`, `l 1 = 1`; net `NetData`
(`Sk`, `acc`, `unowned = P1Net.uOwned`), `Xn`, `F1`, `site`, `e` (scalar at `scalarSite`), `hP4`
(`P1Net.ContractEqCount`), `T` (`I * 2^h * B`), `lpTime ≤ T`, `hacc` (`P1Net.sum_card_skeleton`); P5 `Ch`, `Y`,
`G`, `P`, `hP5` (`P1P5.contract_eq_push`); P6 `ord`, `enc`, `enc_injective`; checkers + P6 `hchecks`
(or the stage form of `P1Count.lemmaP_count_of_stages`). Classical instances as in `P1Count.Main`. -/
def CountInput (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) {A : Type} (letter : Bool → A)
    (answer : Option A → Bool) (chk : ℕ → Option (Prog A)) (m k bnd : ℕ) : Prop :=
  ∃ (F : Type) (_ : CommRing F) (_ : Algebra (ZMod 2) F) (C : P1Count.NetData F) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (_ : l 1 = 1)
    (Xn : C.Sk → Network) (F1 : ∀ σ, Factors F (Xn σ)) (site : ∀ σ, (Xn σ).Site)
    (e : ∀ σ, (Xn σ).Site → F) (_ : ∀ σ u, u ≠ site σ → e σ u = 1)
    (_ : ∀ σ, e σ (site σ) = (2 : F) ^ C.unowned σ)
    (enc : C.toCountData.Tup D → (Fin m → Bool)) (_ : Function.Injective enc) (T : ℕ),
    lpTime a b x.length ≤ T ∧ ∑ σ, C.acc σ = accCount V a x T ∧
    (∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F)) ∧
    (∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v)) ∧
    (∀ u : Fin m → Bool,
      (∀ c < 2 ^ 4, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - 4 →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd) ↔
      ∃ t, C.toCountData.Valid bs l t ∧ enc t = u)

/-- **The hypothesis of P11 with the adopted count and dispatcher (D8).** For every two-constant parity
verifier: an alphabet with letters for the bits, ONE family of check programs `chk` (families `c < 16`, D5
numbering), constants `c, n₁`, and for every input of length at least `n₁`: `4 ≤ k`, a check budget `bnd ≥ 1`
with `16 + bnd ≤ lpCost2 c s a b |x|` (dispatch lane, D7), every check program returns within `bnd` (checker
lanes), and the count data `CountInput` at `m = lpM2 s a b |x|`, `k = lpK2 a b |x|`.
D7: only for clocks with `1 ≤ b` (the statement without it is FALSE at `a = b = 0`, see `P1Int.LemmaP`). -/
def CountHyp (s : ℝ) : Prop := ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A)) (c n₁ : ℕ),
    ∀ x : List Bool, n₁ ≤ x.length →
    4 ≤ lpK2 a b x.length ∧ ∃ bnd : ℕ, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s a b x.length ∧
      (∀ u : Fin (lpM2 s a b x.length) → Bool, ∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc →
        ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
          ∃ v, ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) v bnd) ∧
      CountInput V a b x letter answer chk (lpM2 s a b x.length) (lpK2 a b x.length) bnd

open Classical in
/-- **P11 glue with the adopted count: Lemma P.** The checker of Lemma P is the dispatcher
`P1Count.R bit letter 4 chk`. -/
theorem lemmaP_of_countHyp {s : ℝ} (h : CountHyp s) : LemmaP s := by
  intro L V a b n₀ hb1 hV
  obtain ⟨A, hA, bit, letter, hlet, hbit, answer, hacc, chk, c, n₁, hR⟩ := h L V a b n₀ hb1 hV
  refine ⟨A, hA, P1Count.R bit letter 4 chk, letter, hlet, answer, c, max n₀ n₁, fun x hx => ?_⟩
  have hx₀ : n₀ ≤ x.length := le_trans (le_max_left _ _) hx
  have hx₁ : n₁ ≤ x.length := le_trans (le_max_right _ _) hx
  obtain ⟨hk, bnd, hb, hcost, htot, F, _, _, C, D, bs, l, hl, Xn, F1, site, e, he, hes, enc, hinj, T, hT,
    hsum, hP4, hP5, hchecks⟩ := hR x hx₁
  have htotR : ∀ (u : Fin (lpM2 s a b x.length) → Bool) (γ : Fin (lpK2 a b x.length) → Bool),
      ∃ v, ProgAnswers (P1Count.R bit letter 4 chk) answer
        (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v (4 * 4 + bnd) := fun u γ =>
    P1Count.R_total bit letter hbit answer 4 chk x (List.ofFn u) (lpK2 a b x.length) hk bnd hb (htot u)
      (List.ofFn γ) (List.length_ofFn)
  refine ⟨fun u γ => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := htotR u γ
    exact ⟨v, progAnswers_mono hv hcost⟩
  · have hT' : b * (x.length ^ 2 + 1) + (2 * (a * (x.length ^ 2 + 1)) + 1 + x.length) ≤ T :=
      (time_eq_lpTime a b x.length).trans_le hT
    have hL : (L x = true) ↔ Odd (∑ σ, C.acc σ) := by
      rw [hsum]
      exact parDecides_oai hV x hx₀ T hT'
    have key := P1Count.lemmaP_count C bs l hl Xn F1 site e he hes bit letter hbit answer hacc 4 chk
      (lpK2 a b x.length) hk bnd hb x enc hinj hP4 hP5 hchecks (L x = true) hL
    refine key.trans (Iff.of_eq (congrArg (fun t => Odd (Finset.card t)) ?_))
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' fun γ => progAnswers_true_iff (htotR u γ) hcost

/-- **P11, `lemmaP_of_portTwo`, with the adopted count.** P10 (lane wrap, `P1Wrap.Params`, PROVISIONAL) gives the
dyadic exponent `j` of the port; the rest is `CountHyp` at `s = 2^-j`. -/
theorem lemmaP_of_portTwo_of_countHyp (h : PortTwo → ∃ j : ℕ, CountHyp ((2 : ℝ) ^ (-(j : ℤ)))) :
    LemmaPOfPort PortTwo := by
  intro port
  obtain ⟨j, hj⟩ := h port
  exact ⟨(2 : ℝ) ^ (-(j : ℤ)), j, by positivity, rfl, lemmaP_of_countHyp hj⟩

end P11

end P1Int
