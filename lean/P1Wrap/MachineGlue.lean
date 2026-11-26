import P1Wrap.Wrapper
import P1Wrap.ProgDet
import P1Wrap.Bridge
import OAI.Computability.MultitapeWeakETH.ProgramDecision

/-!
# The two machine lemmas of W3 reduced to stack programs

`InnerProg` and `OuterProg` are the open machine lemmas of W3 at the level of OpenAI's stack programs (`Prog`); the
passage to `C1Challenge.Machine` is done here once, by OpenAI's `compile_program` (a run of cost `n` gives a halting
multitape run within `2n+1` steps) and the bridge `fromOAI` (verbatim copy in `P1Wrap.Bridge`).

* `innerVerifier_of_prog : InnerProg j a b → InnerVerifier j a b`
* `outerVerifier_of_prog : OuterProg j a b → OuterVerifier j a b`
* `port_wrapper_of_progs`: `P1Int.PortWrapper` from the two Prog-level lemmas.
-/

namespace P1Wrap.W3

open P1Int C1Challenge OAI.Computability.IntegerMultiplication P1Wrap.Bridge

noncomputable section

theorem length_flatMap_pair (w : List Bool) : (w.flatMap fun b => [true, b]).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.flatMap_cons, List.length_append, ih]; simp; ring

theorem length_withGuess' (w x : List Bool) : (withGuess w x).length = 2 * w.length + 1 + x.length := by
  unfold withGuess
  rw [List.length_append, length_flatMap_pair, List.length_cons]
  ring

/-- The initial registers of a program run on the input `bits` (letters `letB`). -/
def initRegs {B : Type} (letB : Bool → B) (bits : List Bool) : Reg B :=
  fun i => if i = 0 then bits.map letB else []

/-- **Machine lemma A, Prog form.** For every Lemma P checker `R` that returns within its budget on every branch, a
stack program `P` (any finite alphabet) reads `withGuess w y` from register 0, returns within `K (|withGuess w y| + 1)`
steps with a verdict, and the verdicts describe `Lin`. -/
def InnerProg (j a b : ℕ) : Prop :=
  ∀ (A : Type) (_ : Fintype A) (R : Prog A) (letter : Bool → A), Function.Injective letter →
    ∀ (answer : Option A → Bool) (c n₁ : ℕ),
    (∀ x : List Bool, n₁ ≤ x.length → ∀ u : Fin (lpM2 (sOf j) a b x.length) → Bool,
      ∀ γ : Fin (lpK2 a b x.length) → Bool,
      ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
        (lpCost2 c (sOf j) a b x.length)) →
    ∃ (B : Type) (_ : Fintype B) (P : Prog B) (letB : Bool → B) (_ : Function.Injective letB)
      (ans : Option B → Bool) (verdict : List Bool → List Bool → Bool) (K : ℕ),
      (∀ y w : List Bool, w.length = guessLen y.length →
        ∃ n r, Prog.Run [] P (initRegs letB (withGuess w y)) n r ∧
          n ≤ K * ((withGuess w y).length + 1) ∧ ans (r 0).head? = verdict w y) ∧
      (∀ y : List Bool, Lin j a b R letter answer c n₁ y = true ↔
        ∃ w : List Bool, w.length = guessLen y.length ∧ verdict w y = true)

theorem innerVerifier_of_prog {j a b : ℕ} (h : InnerProg j a b) : InnerVerifier j a b := by
  intro A hA R letter hlet answer c n₁ hR
  obtain ⟨B, hB, P, letB, hinj, ans, verdict, K, hrun, hspec⟩ := h A hA R letter hlet answer c n₁ hR
  obtain ⟨M, hM⟩ := OAI.Computability.MultitapeWeakETH.DecisionTapes.compile_program P letB hinj ans
  have halts : ∀ y w : List Bool, w.length = guessLen y.length →
      HaltsWithin (fromOAI M) (withGuess w y) (verdict w y) ((2 * K + 1) * ((withGuess w y).length + 1)) := by
    intro y w hw
    obtain ⟨n, r, hr, hn, hv⟩ := hrun y w hw
    have h1 := hM (withGuess w y) n r hr
    rw [hv] at h1
    exact haltsWithin_mono ((haltsWithin_fromOAI M).mpr h1) (by nlinarith)
  refine ⟨fromOAI M, 2 * K + 1, fun y => ⟨fun w hw => ⟨_, halts y w hw⟩, ?_⟩⟩
  rw [hspec y]
  constructor
  · rintro ⟨w, hw, hv⟩
    exact ⟨w, hw, by have := halts y w hw; rwa [hv] at this⟩
  · rintro ⟨w, hw, hh⟩
    exact ⟨w, hw, haltsWithin_unique (halts y w hw) hh⟩

open Classical in
/-- **Machine lemma B, Prog form** (`V*`, to be built on the W1 checker of lane hier). If `M` decides `L` within
`Tb |y|` steps, then for a constant `K` and every guess length `g` with room `m + K (Tb ν + 1) ≤ g` from `n₂` on, a
stack program reads `withGuess w x` (`|w| = g |x|`), returns within `C (g + ν + 1) + |withGuess w x|` steps with a
verdict, and at each `x` with `|x| ≥ n₂` the accepted guesses are exactly as many as the `u ∈ {0,1}^m` with
`L (padIn x u) = false`. -/
def OuterProg (j a b : ℕ) : Prop :=
  ∀ (L : List Bool → Bool) (M : Machine) (Tb : ℕ → ℕ),
    (∀ y : List Bool, ∃ T ≤ Tb y.length, HaltsWithin M y (L y) T) →
  ∃ K : ℕ, ∀ (g : ℕ → ℕ) (n₂ : ℕ),
    (∀ n, n₂ ≤ n → lpM2 (sOf j) a b n + K * (Tb (nuOf j a b n) + 1) ≤ g n) →
    ∃ (B : Type) (_ : Fintype B) (P : Prog B) (letB : Bool → B) (_ : Function.Injective letB)
      (ans : Option B → Bool) (verdict : List Bool → List Bool → Bool) (C : ℕ),
      ∀ x : List Bool, n₂ ≤ x.length →
        (∀ w : Fin (g x.length) → Bool, ∃ n r,
          Prog.Run [] P (initRegs letB (withGuess (List.ofFn w) x)) n r ∧
          n ≤ C * (g x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length ∧
          ans (r 0).head? = verdict (List.ofFn w) x) ∧
        (Finset.univ.filter fun w : Fin (g x.length) → Bool => verdict (List.ofFn w) x = true).card =
          (Finset.univ.filter fun u : Fin (lpM2 (sOf j) a b x.length) → Bool =>
            L (padIn j a b x (List.ofFn u)) = false).card

theorem outerVerifier_of_prog {j a b : ℕ} (h : OuterProg j a b) : OuterVerifier j a b := by
  classical
  intro L M Tb hM
  obtain ⟨K, hK⟩ := h L M Tb hM
  refine ⟨K, fun g n₂ hfit => ?_⟩
  obtain ⟨B, hB, P, letB, hinj, ans, verdict, C, hP⟩ := hK g n₂ hfit
  obtain ⟨M', hM'⟩ := OAI.Computability.MultitapeWeakETH.DecisionTapes.compile_program P letB hinj ans
  refine ⟨fromOAI M', 2 * C + 2, fun x hx => ?_⟩
  obtain ⟨hrun, hcount⟩ := hP x hx
  have hxν : x.length ≤ nuOf j a b x.length := by unfold nuOf; omega
  have halts : ∀ w : Fin (g x.length) → Bool,
      HaltsWithin (fromOAI M') (withGuess (List.ofFn w) x) (verdict (List.ofFn w) x)
        ((2 * C + 2) * (g x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length) := by
    intro w
    obtain ⟨n, r, hr, hn, hv⟩ := hrun w
    have h1 := hM' (withGuess (List.ofFn w) x) n r hr
    rw [hv] at h1
    refine haltsWithin_mono ((haltsWithin_fromOAI M').mpr h1) ?_
    have e : (2 * C + 2) * (g x.length + nuOf j a b x.length + 1) =
        2 * (C * (g x.length + nuOf j a b x.length + 1)) + 2 * (g x.length + nuOf j a b x.length + 1) := by
      ring
    have hwl : (withGuess (List.ofFn w) x).length = 2 * g x.length + 1 + x.length := by
      rw [length_withGuess', List.length_ofFn]
    omega
  refine ⟨fun w => ⟨_, halts w⟩, ?_⟩
  rw [← hcount]
  congr 1
  apply Finset.filter_congr
  intro w _
  constructor
  · intro hh
    exact haltsWithin_unique (halts w) hh
  · intro hv
    have := halts w
    rwa [hv] at this

/-- **W3 from the two Prog-level machine lemmas.** -/
theorem port_wrapper_of_progs (hA : ∀ j a b, InnerProg j a b) (hB : ∀ j a b, OuterProg j a b) :
    PortWrapper :=
  port_wrapper_of_machines (fun j a b => innerVerifier_of_prog (hA j a b))
    (fun j a b => outerVerifier_of_prog (hB j a b))

end

end P1Wrap.W3
