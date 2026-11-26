import P1C10.Prog
import P1Wit.SpaceFacts
import P1Int.LemmaP

/-!
# P1C10.Fmt10Defs: the format inputs of the family-9 program at the genuine dims (lane P1-lean-c10wire)

`ProgC10Target` (Prog.lean) needs, for its dims function: `hM : ∀ n, (dims n).fixedLen ≤ M n` with
`M = lpM2 s a b` (the witness length of the dispatcher, `P1ProgDir.famProg_of_task`), `FmtHyp10 dims` and the polylog
bound `Dom log (c10Size ∘ dims)`. The genuine dims fit the witness only for large `n` (WitnessFit), so family 9 uses the
CUT dims `cutDims n₀ G n = if n₀ ≤ n then G n else zeroDims` (`zeroDims.fixedLen = 0`): `hM` holds for all `n`, and
for `|x| ≥ n₀` family 9 is C10 at the genuine dims.

Small-case tests (proved here): `zeroDims_fixedLen`, `c10Size_zeroDims`; for every dims `D`, beyond the last level
the format numbers of `fmt10` are constants (`width_secLev_beyond`, `off_secLev_beyond`: width `0`, offset `fixedLen`),
so a program for `FmtHyp10` must branch on `ℓ ≤ top + 1` (`ℓ` is given in binary).
Targets of the Sol prover P1-sol-fmt10: `Fmt10CutTarget`, `Size10CutTarget`.
-/

namespace P1C10

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression OAI.DepthThreeLowerBound
open P1Wit

/-- The empty level. -/
def zeroLevel : LevelDims := ⟨0, 0, 0, 0, 0, false, 0, 0, 0, 0⟩

/-- The empty dims (no field: `fixedLen = 0`). -/
def zeroDims : Dims :=
  { r := 0, I := 0, N := 0, nGB := 0, top := 0, lv := fun _ => zeroLevel, bigW := 0, wW := 0, chainLen := 0,
    chainW := 0 }

/-- The dims function cut below `n₀`. -/
def cutDims (n₀ : ℕ) (G : ℕ → Dims) : ℕ → Dims := fun n => if n₀ ≤ n then G n else zeroDims

theorem cutDims_of_le {n₀ n : ℕ} (G : ℕ → Dims) (h : n₀ ≤ n) : cutDims n₀ G n = G n := if_pos h

theorem cutDims_of_lt {n₀ n : ℕ} (G : ℕ → Dims) (h : n < n₀) : cutDims n₀ G n = zeroDims := if_neg (by omega)

/-- Small case: the empty dims have no field. -/
theorem zeroDims_fixedLen : zeroDims.fixedLen = 0 := by decide

/-- Small case: `c10Size` of the empty dims is `1` (the one-bit layout field is counted by `baseBits`). -/
theorem c10Size_zeroDims : c10Size zeroDims = 1 := by decide

/-- `hM` for the cut dims, from the fit for `n ≥ n₀`. -/
theorem cutDims_fixedLen_le (n₀ : ℕ) (G : ℕ → Dims) (M : ℕ → ℕ) (hfit : ∀ n, n₀ ≤ n → (G n).fixedLen ≤ M n) :
    ∀ n, (cutDims n₀ G n).fixedLen ≤ M n := by
  intro n
  by_cases h : n₀ ≤ n
  · rw [cutDims_of_le G h]; exact hfit n h
  · rw [cutDims_of_lt G (by omega), zeroDims_fixedLen]; exact Nat.zero_le _

/-- Beyond the last level every section is unused: width `0`. -/
theorem width_secLev_beyond (D : Dims) {ℓ : ℕ} (hℓ : D.top + 2 ≤ ℓ) (k : Mem) : D.width (secLev ℓ k) = 0 := by
  have hk : D.kind (secLev ℓ k) = .unused := by
    unfold Dims.kind secLev
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  unfold Dims.width
  rw [hk]

theorem count_width_beyond (D : Dims) {s : ℕ} (hs : D.nSec ≤ s) : D.count s * D.width s = 0 := by
  have hk : D.kind s = .unused := by
    unfold Dims.kind
    unfold Dims.nSec at hs
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  unfold Dims.count Dims.width
  rw [hk]
  rfl

theorem off_ge_nSec (D : Dims) : ∀ j, D.off (D.nSec + j) = D.fixedLen
  | 0 => rfl
  | j + 1 => by
    unfold Dims.off at *
    rw [← Nat.add_assoc, offAt, count_width_beyond D (Nat.le_add_right _ _), Nat.add_zero]
    exact off_ge_nSec D j

/-- Beyond the last level the offset of every section is `fixedLen`. -/
theorem off_secLev_beyond (D : Dims) {ℓ : ℕ} (hℓ : D.top + 2 ≤ ℓ) (k : Mem) : D.off (secLev ℓ k) = D.fixedLen := by
  have h : secLev ℓ k = D.nSec + (secLev ℓ k - D.nSec) := by
    unfold secLev Dims.nSec
    omega
  rw [h]
  exact off_ge_nSec D _

/-! ## Targets of the Sol prover P1-sol-fmt10 -/

/-- The genuine dims of Lemma P (the dims of `P1Int.P11.fixedDims` with `V := toOAI V`, `aM := 1`). -/
noncomputable abbrev genD {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) : ℕ → Dims :=
  fun n => SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias

/-- **Target F1**: the C10 format numbers of the cut genuine dims are polynomial-time in `(n, ℓ)` (binary). -/
def Fmt10CutTarget : Prop :=
  ∀ {k : Type} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias n₀ : ℕ),
    FmtHyp10 (cutDims n₀ (genD A Kc V aM a b d bigBias termBias))

/-- **Target F2**: the size measure of check C10 at the cut genuine dims is polylogarithmic in `n`. -/
def Size10CutTarget : Prop :=
  ∀ {k : Type} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias n₀ : ℕ),
    Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => c10Size (cutDims n₀ (genD A Kc V aM a b d bigBias termBias) n))

end P1C10

#print axioms P1C10.off_secLev_beyond
#print axioms P1C10.cutDims_fixedLen_le
