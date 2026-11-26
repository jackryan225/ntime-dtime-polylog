import P1Int.LemmaP
import P1Int.Bridge
import P1Count.Bookkeeping
import OAI.Computability.MultitapeWeakETH.Price

/-!
# P1Int.P11: Lemma P from the port, with every wave-2 piece as an explicit hypothesis (task P11)

Owner: P1-lean-integ (G3-chief, board 09:40:05Z and D6 of 10:49:43Z). The glue is sorry-free; every piece that
another lane proves enters as a FIELD of `CountSetup` or as the hypothesis `SetupHyp` (TARGET SHAPES; this file is
the reference for the shapes, D6). Two-constant form of `P1Int.LemmaP` (board 1368): the verifier `V` has guess
length `a (n² + 1)` and base clock `b (n² + 1)`, so its full time is `lpTime a b n`.

Chain of the proof (paper lem:P; research/release/time-separation-public/ntime-dtime-polylog.tex):
  `L x = true`
  ↔ `Odd #{w | toOAI V accepts withGuess w x within T}`         (`P1Int.parDecides_oai`, needs `lpTime ≤ T`)
  ↔ `Odd (∑ σ, acc σ)`                                          (field `hacc`: net, sum over skeletons)
  ↔ `Odd #{u | every check stage passes on u}`                  (`P1Count.CountData.odd_iff_of_stages`, PROVED
                                                                 by lane count; fields `hl hP enc hinj K Stage Tr h0
                                                                 hstep hmono hform`)
  ↔ `Odd #{u | ∀ γ, R accepts (x, u, γ) within lpCost2}`         (dispatcher correctness, `SetupHyp`)
plus the dispatcher cost bound on every branch (`SetupHyp`).

Fields and their owners (PROVISIONAL where the lane has not posted a compiled statement):
* P0 (lane wrap, `P1Wrap.finite_subalgebra`, `P1Wrap.exists_functional`): `F`, `D`, `basis`, `l`, `hl`.
* count (lane W2-count, `P1Count.CountData`, compiled cnt-2/cnt-3): `C`.
* net (lane net, `P1Net.sum_card_skeleton`, `P1Net.ContractEqCount` with `P1Benes.bset`, run bound
  `I * 2^h * B ≥ lpTime`): `T`, `hT`, `hacc`; net + P5 (`P1P5.contract_eq_push`, `card_final_payloads`): `hP`.
* P6 (lane W2-P6, `P1Wit.encFn`, `enc_injective`, `enc_length_le`): `enc`, `hinj`; the codomain
  `Fin (lpM2 s a b |x|) → Bool` is the witness length (P6's `fixedLen + zLen ≤ lpM2`, from P10).
* checks (lanes W2-chkdir C1-C4 + C14, W2-chkgreedy C5-C9, W2-chkfinal C10-C13; stage order of D5; the step
  form is the lanes' `Ck_true` / `Ck_unique`): `K`, `Stage`, `Tr`, `h0`, `hstep`, `hmono`; P6 + checks: `hform`.
* dispatcher (lane P1-lean-dispatch, `P1Count.R`, D5 + amendment of 10:51Z): `R`, cost, correctness.
* P10 (lane wrap, `P1Wrap.Params`): the dyadic exponent `j` with `s = 2^-j`, the thresholds `n₁`.
-/

namespace P1Int

namespace P11

/-- **P4 with the scalar, and P5** (net `P1Net.ContractEqCount` + P5 `P1P5.contract_eq_push`), in the form of
`hP` of `P1Count.CountData.count_mod2`: `2 ^ u(σ) · ∑_ι ∑_z ∏_i W σ ι z i = acc σ` in `F`. -/
def PushIdentity {F : Type} [CommRing F] [Algebra (ZMod 2) F] (C : P1Count.CountData F) : Prop :=
  ∀ σ, (2 : F) ^ C.unowned σ * ∑ ι, ∑ z, ∏ i, C.W σ ι z i = (C.acc σ : F)

open C1Challenge OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound Module
open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- The full time bound of `parDecides_oai` for the two-constant verifier is `lpTime a b n`. -/
theorem time_eq_lpTime (a b n : ℕ) :
    b * (n ^ 2 + 1) + (2 * (a * (n ^ 2 + 1)) + 1 + n) = lpTime a b n := by
  unfold lpTime; ring

open Classical in
/-- The number of guesses `w` of length `a (|x|² + 1)` on which OpenAI's copy of `V` accepts
`withGuess w x` within `T` steps (the right side of `P1Int.parDecides_oai`). -/
noncomputable def accCount (V : Machine) (a : ℕ) (x : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin (a * (x.length ^ 2 + 1)) → Bool =>
    MultiTapeHaltsIn (toOAI V) (withGuess (List.ofFn w) x) true T).card

/-- **The parity count of one input `x`** (paper lem:P, the objects of one input). TARGET SHAPES of the
wave-2 lanes; owners in the module header. `m` is the witness length (`lpM2 s a b |x|` in `SetupHyp`; a
parameter here, because `lpM2` contains a real floor and Lean's structure elaborator diverges on it, jobs
p1intB-16..21). `F` (P0, lane wrap: `P1Wrap.Fsub κ`, finite by `P1Wrap.finite_subalgebra`) is a parameter,
quantified in `SetupHyp`. -/
structure CountSetup (m : ℕ) (V : Machine) (a b : ℕ) (x : List Bool) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] where
  /-- P0: one fixed basis of the finite `F₂`-algebra `F` over `F₂` (a constant of the proof, D4). -/
  D : ℕ
  basis : Basis (Fin D) (ZMod 2) F
  /-- P0: a functional with `l 1 = 1` (`P1Wrap.exists_functional`). -/
  l : F →ₗ[ZMod 2] ZMod 2
  hl : l 1 = 1
  /-- count: skeletons, branches, payloads, vertex tensors, `unowned = P1Net.uOwned`, `acc`. -/
  C : P1Count.CountData F
  /-- net: the run bound `T = I * 2^h * B` of the routed network, at least the verifier's full time. -/
  T : ℕ
  hT : lpTime a b x.length ≤ T
  /-- net: the accepting guesses, split by skeleton (`P1Net.sum_card_skeleton`). -/
  hacc : ∑ σ, C.acc σ = accCount V a x T
  /-- net (routed P4 with the scalar `2 ^ uOwned`, `P1Net.ContractEqCount`) + P5 (`P1P5.contract_eq_push`). -/
  hP : PushIdentity C
  /-- P6: the witness of a tuple `(σ, ι, z, chain)`, of length exactly `m`. -/
  enc : C.Tup D → (Fin m → Bool)
  /-- P6: `P1Wit.enc_injective`. -/
  hinj : Function.Injective enc
  /-- checks: the number of stages (D5 stage order). -/
  K : ℕ
  /-- checks: `Stage k u`: every check of stage `k` passes on the witness `u`. -/
  Stage : ℕ → (Fin m → Bool) → Prop
  /-- checks: `Tr k u`: the fields of the first `k` stages of `u` hold their true values. -/
  Tr : ℕ → (Fin m → Bool) → Prop
  h0 : ∀ u, Tr 0 u
  /-- checks: `Ck_true` and `Ck_unique` of the families of stage `k`. -/
  hstep : ∀ k < K, ∀ u, Tr k u → (Stage k u ↔ Tr (k + 1) u)
  hmono : ∀ k < K, ∀ u, Tr (k + 1) u → Tr k u
  /-- P6 + checks: all fields true iff `u` encodes a valid tuple (`P1Wit.enc_dec`, `decode_enc`). -/
  hform : ∀ u, Tr K u ↔ ∃ t, C.Valid basis l t ∧ enc t = u

open Classical in
/-- **The count of one input** (from lane count's `odd_iff_of_stages`): the witnesses that pass every stage have
the parity of the accepting guesses within `T`. -/
theorem CountSetup.odd_iff {m : ℕ} {V : Machine} {a b : ℕ} {x : List Bool} {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (S : CountSetup m V a b x F) :
    Odd (Finset.univ.filter fun u : Fin m → Bool => ∀ k < S.K, S.Stage k u).card ↔
      Odd (accCount V a x S.T) := by
  rw [← S.hacc]
  exact S.C.odd_iff_of_stages S.basis S.l S.hl S.hP S.enc S.hinj S.K S.Stage S.Tr S.h0 S.hstep S.hmono
    S.hform

/-- **The hypothesis of P11** (TARGET SHAPE of the dispatcher lane and, through `CountSetup`, of all wave-2
lanes): for every two-constant parity verifier there are ONE stack program `R` (the dispatcher `P1Count.R`)
and thresholds such that, on every input `x` of length at least `n₁`, every branch returns within
`lpCost2 c s a b |x|` steps, and the witnesses accepted for every selector are exactly those that pass every
check stage of a `CountSetup` of `x`. D7: only for clocks with `1 ≤ b` (false at `a = b = 0`, see `P1Int.LemmaP`). -/
def SetupHyp (s : ℝ) : Prop := ∀ (L : List Bool → Bool) (V : Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (R : Prog A) (letter : Bool → A) (_ : Function.Injective letter)
    (answer : Option A → Bool) (c n₁ : ℕ), ∀ x : List Bool, n₁ ≤ x.length →
    (∀ u : Fin (lpM2 s a b x.length) → Bool, ∀ γ : Fin (lpK2 a b x.length) → Bool,
      ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
        (lpCost2 c s a b x.length)) ∧
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra (ZMod 2) F) (S : CountSetup (lpM2 s a b x.length) V a b x F),
      ∀ u : Fin (lpM2 s a b x.length) → Bool,
      (∀ γ : Fin (lpK2 a b x.length) → Bool,
        ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true
          (lpCost2 c s a b x.length)) ↔ ∀ k < S.K, S.Stage k u

open Classical in
/-- **P11 glue: Lemma P from the per-input counts.** -/
theorem lemmaP_of_setup {s : ℝ} (h : SetupHyp s) : LemmaP s := by
  intro L V a b n₀ hb1 hV
  obtain ⟨A, hA, R, letter, hlet, answer, c, n₁, hR⟩ := h L V a b n₀ hb1 hV
  refine ⟨A, hA, R, letter, hlet, answer, c, max n₀ n₁, fun x hx => ?_⟩
  have hx₀ : n₀ ≤ x.length := le_trans (le_max_left _ _) hx
  have hx₁ : n₁ ≤ x.length := le_trans (le_max_right _ _) hx
  obtain ⟨hcost, F, _, _, S, hdisp⟩ := hR x hx₁
  refine ⟨hcost, ?_⟩
  have hT : b * (x.length ^ 2 + 1) + (2 * (a * (x.length ^ 2 + 1)) + 1 + x.length) ≤ S.T :=
    (time_eq_lpTime a b x.length).trans_le S.hT
  rw [parDecides_oai hV x hx₀ S.T hT]
  have hset : (Finset.univ.filter fun u : Fin (lpM2 s a b x.length) → Bool =>
      ∀ γ : Fin (lpK2 a b x.length) → Bool,
        ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true
          (lpCost2 c s a b x.length)) =
      (Finset.univ.filter fun u : Fin (lpM2 s a b x.length) → Bool => ∀ k < S.K, S.Stage k u) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdisp u
  refine Iff.trans ?_ (S.odd_iff.symm.trans ?_)
  · exact Iff.rfl
  · exact Iff.of_eq (congrArg (fun t => Odd (Finset.card t)) hset.symm)

/-- **P11, `lemmaP_of_portTwo` from its parts.** P10 (lane wrap, `P1Wrap.Params`) gives the dyadic exponent `j`
of the port; the rest is `SetupHyp` at `s = 2^-j`. -/
theorem lemmaP_of_portTwo_of_setup (h : PortTwo → ∃ j : ℕ, SetupHyp ((2 : ℝ) ^ (-(j : ℤ)))) :
    LemmaPOfPort PortTwo := by
  intro port
  obtain ⟨j, hj⟩ := h port
  exact ⟨(2 : ℝ) ^ (-(j : ℤ)), j, by positivity, rfl, lemmaP_of_setup hj⟩

end P11

end P1Int
