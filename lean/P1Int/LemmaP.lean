import P1Int.Interfaces
import OAI.Computability.IntegerMultiplication.TMProgram

/-!
# P1Int.LemmaP: Lemma P (port case) in verifier form, with the checker as an OpenAI `Prog`

Owner: P1-lean-integ. Form chosen by G3-chief (09:05Z): `R : Prog A` over a finite alphabet `A`; the
three inputs `x`, `u`, `γ` are in registers 0, 1, 2 (first bit on top of the stack), every other register
is empty; the answer is `answer` of the top symbol of register 0 when `R` returns.
Parameters: the paper's lem:P (research/papers/ntime-dtime-polylog.tex) as in PLAN.md section 3, with the
two-constant change of board 1368; `ParDecidesFrom`, `ParityHierarchy`, `C1Conclusion` from P1Int.Interfaces (copy B).

Consumers: lane wrap (W3 `port_wrapper` takes `LemmaP s` as hypothesis), wave 2 (P8 builds `R`, P11 proves
`PortTwo → ∃ s j, 0 < s ∧ s = 2^-j ∧ LemmaP s`).
-/

namespace P1Int

open C1Challenge OAI.Computability.IntegerMultiplication

/-- Registers 0, 1, 2 hold `x`, `u`, `γ` (letters of `A`); all other registers are empty. -/
def inputRegs {A : Type} (letter : Bool → A) (x u γ : List Bool) : Reg A := fun i =>
  if i = 0 then x.map letter else if i = 1 then u.map letter else if i = 2 then γ.map letter else []

/-- `R` returns on registers `regs` at cost at most `bound`, and `answer` of the top of register 0 is `b`. -/
def ProgAnswers {A : Type} (R : Prog A) (answer : Option A → Bool) (regs : Reg A) (b : Bool)
    (bound : ℕ) : Prop :=
  ∃ n ≤ bound, ∃ r : Reg A, Prog.Run [] R regs n r ∧ answer (r 0).head? = b

/-! ## Parameters of lem:P (two constants, G3-chief board 1368)

The verifier `V` has guess length `a (n² + 1)` and time `b (n² + 1)` plus its input length; so it runs at most
`t = b (n² + 1) + 2 a (n² + 1) + n + 1` steps at length `n`, and `λ, p, T, m, k` are computed from this `t`. -/

/-- `t = b (n² + 1) + 2 a (n² + 1) + n + 1`: the full time bound of the verifier at length `n`. -/
def lpTime (a b n : ℕ) : ℕ := b * (n ^ 2 + 1) + 2 * (a * (n ^ 2 + 1)) + n + 1
/-- `λ = ⌈log₂ t⌉`. -/
def lpLam2 (a b n : ℕ) : ℕ := Nat.clog 2 (lpTime a b n)
/-- `p = ⌊log₂ λ⌋`. -/
def lpP2 (a b n : ℕ) : ℕ := Nat.log 2 (lpLam2 a b n)
/-- `T = ⌊s p⌋`. -/
noncomputable def lpT2 (s : ℝ) (a b n : ℕ) : ℕ := ⌊s * (lpP2 a b n : ℝ)⌋₊
/-- `m = (p + 1)^6 ⌈t / 2^T⌉`: length of the parity witness `u`. -/
noncomputable def lpM2 (s : ℝ) (a b n : ℕ) : ℕ :=
  (lpP2 a b n + 1) ^ 6 * ((lpTime a b n + 2 ^ lpT2 s a b n - 1) / 2 ^ lpT2 s a b n)
/-- `k = λ`: length of the selector `γ`. -/
def lpK2 (a b n : ℕ) : ℕ := lpLam2 a b n
/-- Cost bound of one branch: `c m (⌊log₂ λ⌋ + 1)`. -/
noncomputable def lpCost2 (c : ℕ) (s : ℝ) (a b n : ℕ) : ℕ := c * lpM2 s a b n * (lpP2 a b n + 1)

open Classical in
/-- **Lemma P** (port case), verifier form, checker = stack program. Every language with a parity verifier of
guess length `a (n² + 1)` and time `b (n² + 1)` (+ input length) is `⊕[m] ∀[k]` of a stack program `R`
that returns within `c m (⌊log₂ λ⌋ + 1)` steps on every branch, for all inputs of length at least `n₁`.

D7 (G3-chief, board 11:01Z and 11:09Z, found by P1-lean-dispatch): the hypothesis `1 ≤ b` is NECESSARY. At
`a = b = 0` the verifier still has `|x| + 1` steps (enough to read the last input bit, e.g. `L x` = last bit of
`x`), but `lpTime 0 0 n = n + 1`, so the branch budget `lpCost2 c s 0 0 n = c (p+1)^7 ⌈(n+1)/2^T⌉` is `o(n)` and
no stack program can reach the last bit of `x` in register 0. With `1 ≤ b`, `lpTime ≥ n² + 1` and
`2^T ≤ λ` (for `s ≤ 1`), so the budget is at least `n²/λ ≥ n` for large `n`. W3 applies Lemma P with `b + 1`
(`ParDecidesFrom` is monotone in the clock). -/
def LemmaP (s : ℝ) : Prop := ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (R : Prog A) (letter : Bool → A) (_ : Function.Injective letter)
    (answer : Option A → Bool) (c n₁ : ℕ), ∀ x : List Bool, n₁ ≤ x.length →
    (∀ u : Fin (lpM2 s a b x.length) → Bool, ∀ γ : Fin (lpK2 a b x.length) → Bool,
      ∃ v, ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) v
        (lpCost2 c s a b x.length)) ∧
    (L x = true ↔ Odd (Finset.univ.filter fun u : Fin (lpM2 s a b x.length) → Bool =>
      ∀ γ : Fin (lpK2 a b x.length) → Bool,
        ProgAnswers R answer (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true
          (lpCost2 c s a b x.length)).card)

/-- The port case gives Lemma P with a dyadic constant (target of task P11). -/
def LemmaPOfPort (Port : Prop) : Prop :=
  Port → ∃ (s : ℝ) (j : ℕ), 0 < s ∧ s = (2 : ℝ) ^ (-(j : ℤ)) ∧ LemmaP s

/-- **W3** (lane wrap, `P1Wrap.port_wrapper`): Lemma P with a dyadic constant, plus the hierarchy,
gives the conclusion of `C1Challenge.c1`. -/
def PortWrapper : Prop := ∀ (s : ℝ) (j : ℕ), s = (2 : ℝ) ^ (-(j : ℤ)) → LemmaP s →
    ParityHierarchy → C1Conclusion

end P1Int
