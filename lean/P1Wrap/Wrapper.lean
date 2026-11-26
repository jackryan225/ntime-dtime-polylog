import P1Wrap.W3Arith
import C1Challenge.NonVacuity
import P1Int.Mono

/-!
# W3: the port wrapper (task W3 of research/g3/leanplan/PLAN.md; paper prop:case2, l.1120-1150)

Target: `P1Int.PortWrapper` (s = 2^-j → LemmaP s → ParityHierarchy → C1Conclusion).

`port_wrapper_of_machines` proves it from two MACHINE lemmas, stated here as `Prop`s with all arithmetic outside them:

* `InnerVerifier j a b` (machine lemma A): the inner language `Lin` (the complement of the paper's `A''`: every word
  except the padded `1^n 0 x u 0^{(p+1) m}`, `n ≥ n₁`, `|u| = m`, on which `R` accepts for every selector `γ`) is in
  `NTIMELinLog`, for every stack program `R` that returns within the Lemma P budget on every branch.
* `OuterVerifier j a b` (machine lemma B, V* via W1): if a machine `M` decides a language `Lin` within `Tb |y|` steps,
  then for a constant `K` (bits per transcript row of `M`, with self-delimiting overhead), for every guess length `g`
  that leaves room `m + K (Tb ν + 1) ≤ g` from `n₂` on, some verifier `V` of guess length `g` accepts, at each `x`,
  exactly as many guesses as there are `u ∈ {0,1}^m` with `Lin (padIn x u) = false`, in time `c (g + ν + 1)` plus its
  input length. (Construction: guess `u`, the self-delimited transcript of the flipped `M` on `padIn x u` and zeros;
  check it with the W1 checker; one valid transcript per run.)

Everything else is proved here: the choice `σ = s/2`, `q = 4/s`, the use of Lemma P and of W2, the parity count, the
time bound, and the fitting inequality (`W3Arith.fits`).
-/

namespace P1Wrap.W3

open P1Int C1Challenge Filter OAI.Computability.IntegerMultiplication

noncomputable section

/-- The padded input `1^n 0 x u 0^{(p+1) m}` (`n = |x|`). -/
def padIn (j a b : ℕ) (x u : List Bool) : List Bool :=
  List.replicate x.length true ++ false :: (x ++ u ++ List.replicate (padLen j a b x.length) false)

theorem length_padIn (j a b : ℕ) (x u : List Bool) (hu : u.length = lpM2 (sOf j) a b x.length) :
    (padIn j a b x u).length = nuOf j a b x.length := by
  simp only [padIn, nuOf, List.length_append, List.length_replicate, List.length_cons, hu]
  ring

theorem replicate_true_cons_false_inj : ∀ (n n' : ℕ) (r r' : List Bool),
    List.replicate n true ++ false :: r = List.replicate n' true ++ false :: r' → n = n' ∧ r = r'
  | 0, 0, r, r', h => by simpa using h
  | 0, n' + 1, r, r', h => by simp [List.replicate_succ] at h
  | n + 1, 0, r, r', h => by simp [List.replicate_succ] at h
  | n + 1, n' + 1, r, r', h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := replicate_true_cons_false_inj n n' r r' h
      exact ⟨by omega, h2⟩

/-- `padIn` is injective on pairs with `|u| = m(|x|)`. -/
theorem padIn_inj {j a b : ℕ} {x u x' u' : List Bool} (hu : u.length = lpM2 (sOf j) a b x.length)
    (hu' : u'.length = lpM2 (sOf j) a b x'.length) (h : padIn j a b x u = padIn j a b x' u') :
    x = x' ∧ u = u' := by
  unfold padIn at h
  obtain ⟨hn, hr⟩ := replicate_true_cons_false_inj _ _ _ _ h
  rw [List.append_assoc, List.append_assoc] at hr
  obtain ⟨hx, hr2⟩ := List.append_inj hr hn
  subst hx
  have hl : u.length = u'.length := by rw [hu, hu']
  obtain ⟨hu2, -⟩ := List.append_inj hr2 hl
  exact ⟨rfl, hu2⟩

/-- `R` accepts `(x, u, γ)` within the Lemma P budget for every selector `γ` (exact text of `LemmaP`). -/
def AllAccept {A : Type} (R : Prog A) (letter : Bool → A) (answer : Option A → Bool) (j a b c : ℕ)
    (x u : List Bool) : Prop :=
  ∀ γ : Fin (lpK2 a b x.length) → Bool,
    ProgAnswers R answer (inputRegs letter x u (List.ofFn γ)) true (lpCost2 c (sOf j) a b x.length)

open Classical in
/-- The inner language: the complement of the paper's `A''`. -/
def Lin {A : Type} (j a b : ℕ) (R : Prog A) (letter : Bool → A) (answer : Option A → Bool) (c n₁ : ℕ) :
    List Bool → Bool := fun y =>
  decide (¬ ∃ x u : List Bool, n₁ ≤ x.length ∧ u.length = lpM2 (sOf j) a b x.length ∧
    y = padIn j a b x u ∧ AllAccept R letter answer j a b c x u)

theorem Lin_padIn {A : Type} {j a b : ℕ} {R : Prog A} {letter : Bool → A} {answer : Option A → Bool} {c n₁ : ℕ}
    {x u : List Bool} (hx : n₁ ≤ x.length) (hu : u.length = lpM2 (sOf j) a b x.length) :
    Lin j a b R letter answer c n₁ (padIn j a b x u) = false ↔ AllAccept R letter answer j a b c x u := by
  unfold Lin
  rw [decide_eq_false_iff_not, not_not]
  constructor
  · rintro ⟨x', u', -, hu', heq, hacc⟩
    obtain ⟨rfl, rfl⟩ := padIn_inj hu hu' heq
    exact hacc
  · intro hacc
    exact ⟨x, u, hx, hu, rfl, hacc⟩

/-- **Machine lemma A** (inner verifier). -/
def InnerVerifier (j a b : ℕ) : Prop :=
  ∀ (A : Type) (_ : Fintype A) (R : Prog A) (letter : Bool → A), Function.Injective letter →
    ∀ (answer : Option A → Bool) (c n₁ : ℕ),
    (∀ x : List Bool, n₁ ≤ x.length → ∀ u : Fin (lpM2 (sOf j) a b x.length) → Bool,
      ∀ γ : Fin (lpK2 a b x.length) → Bool,
      ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
        (lpCost2 c (sOf j) a b x.length)) →
    NTIMELinLog (Lin j a b R letter answer c n₁)

open Classical in
/-- **Machine lemma B** (outer verifier `V*`, built on W1). -/
def OuterVerifier (j a b : ℕ) : Prop :=
  ∀ (L : List Bool → Bool) (M : Machine) (Tb : ℕ → ℕ),
    (∀ y : List Bool, ∃ T ≤ Tb y.length, HaltsWithin M y (L y) T) →
  ∃ K : ℕ, ∀ (g : ℕ → ℕ) (n₂ : ℕ),
    (∀ n, n₂ ≤ n → lpM2 (sOf j) a b n + K * (Tb (nuOf j a b n) + 1) ≤ g n) →
    ∃ (V : Machine) (c : ℕ), ∀ x : List Bool, n₂ ≤ x.length →
      (∀ w : Fin (g x.length) → Bool, ∃ v, HaltsWithin V (withGuess (List.ofFn w) x) v
          (c * (g x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length)) ∧
      (Finset.univ.filter fun w : Fin (g x.length) → Bool => HaltsWithin V (withGuess (List.ofFn w) x) true
          (c * (g x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length)).card =
        (Finset.univ.filter fun u : Fin (lpM2 (sOf j) a b x.length) → Bool =>
          L (padIn j a b x (List.ofFn u)) = false).card

/-- **W3** from the two machine lemmas. -/
theorem port_wrapper_of_machines (hA : ∀ j a b, InnerVerifier j a b) (hB : ∀ j a b, OuterVerifier j a b) :
    PortWrapper := by
  classical
  intro s j hs hP hW2
  have hsj : s = sOf j := hs
  subst hsj
  obtain ⟨D, ⟨U, a, b₀, hU₀⟩, hDno⟩ := hW2 (qOf j) (one_le_qOf j)
  -- D7: Lemma P needs `1 ≤ b`; use the clock constant `b₀ + 1` (`ParDecidesFrom` is monotone in the clock)
  obtain ⟨b, hb, hU⟩ : ∃ b : ℕ, 1 ≤ b ∧
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 :=
    ⟨b₀ + 1, by omega, parDecidesFrom_mono_clock hU₀ (fun n => Nat.mul_le_mul_right _ (by omega))⟩
  obtain ⟨A, hAf, R, letter, hlet, answer, c, n₁, hR⟩ := hP D U a b 0 hb hU
  set L := Lin j a b R letter answer c n₁ with hL
  have hNT : NTIMELinLog L :=
    hA j a b A hAf R letter hlet answer c n₁ (fun x hx u γ => (hR x hx).1 u γ)
  refine ⟨sigmaOf j, sigmaOf_pos j, L, hNT, ?_⟩
  rintro ⟨M, C, hM⟩
  set Tb : ℕ → ℕ := fun ν => ⌊C * ((ν : ℝ) * Real.logb 2 (ν : ℝ) ^ sigmaOf j + 1)⌋₊ with hTb
  have hMTb : ∀ y : List Bool, ∃ T ≤ Tb y.length, HaltsWithin M y (L y) T := by
    intro y
    obtain ⟨T, hT, hh⟩ := hM y
    exact ⟨T, Nat.le_floor hT, hh⟩
  obtain ⟨K, hK⟩ := hB j a b L M Tb hMTb
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 (fits j a b K C)
  set n₃ := max n₂ n₁ with hn₃
  have hfit : ∀ n, n₃ ≤ n → lpM2 (sOf j) a b n + K * (Tb (nuOf j a b n) + 1) ≤ G (qOf j) n := by
    intro n hn
    have := hn₂ n (le_trans (le_max_left _ _) hn)
    simp only [hTb]
    omega
  obtain ⟨V, c', hV⟩ := hK (G (qOf j)) n₃ hfit
  apply hDno V (2 * c') n₃
  intro x hx
  have hx₁ : n₁ ≤ x.length := le_trans (le_max_right _ _) hx
  have hx₂ : n₂ ≤ x.length := le_trans (le_max_left _ _) hx
  obtain ⟨hhalt, hcount⟩ := hV x hx
  have hroom : nuOf j a b x.length + 1 ≤ G (qOf j) x.length := by
    have := hn₂ x.length hx₂; omega
  -- the time bound of `V` is below `2 c' G + |input|`
  have htime : ∀ w : Fin (G (qOf j) x.length) → Bool,
      c' * (G (qOf j) x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length ≤
        2 * c' * G (qOf j) x.length + (withGuess (List.ofFn w) x).length := by
    intro w
    have : c' * (G (qOf j) x.length + nuOf j a b x.length + 1) ≤ c' * (2 * G (qOf j) x.length) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : c' * (2 * G (qOf j) x.length) = 2 * c' * G (qOf j) x.length := by ring
    omega
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hhalt w
    exact ⟨v, hv.mono (htime w)⟩
  · -- the filter at the larger time bound is the filter at V's own bound
    have hset : (Finset.univ.filter fun w : Fin (G (qOf j) x.length) → Bool =>
          HaltsWithin V (withGuess (List.ofFn w) x) true
            (2 * c' * G (qOf j) x.length + (withGuess (List.ofFn w) x).length)) =
        (Finset.univ.filter fun w : Fin (G (qOf j) x.length) → Bool =>
          HaltsWithin V (withGuess (List.ofFn w) x) true
            (c' * (G (qOf j) x.length + nuOf j a b x.length + 1) + (withGuess (List.ofFn w) x).length)) := by
      apply Finset.filter_congr
      intro w _
      constructor
      · intro h
        obtain ⟨v, hv⟩ := hhalt w
        have hvt : v = true := halts_unique V hv h
        rw [hvt] at hv
        exact hv
      · intro h
        exact h.mono (htime w)
    have hu : (Finset.univ.filter fun u : Fin (lpM2 (sOf j) a b x.length) → Bool =>
          L (padIn j a b x (List.ofFn u)) = false) =
        (Finset.univ.filter fun u : Fin (lpM2 (sOf j) a b x.length) → Bool =>
          ∀ γ : Fin (lpK2 a b x.length) → Bool,
            ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true
              (lpCost2 c (sOf j) a b x.length)) := by
      apply Finset.filter_congr
      intro u _
      exact Lin_padIn hx₁ (List.length_ofFn)
    rw [(hR x hx₁).2]
    simp only [ParDecidesFrom] at *
    rw [hset, hcount, hu]

end

end P1Wrap.W3
