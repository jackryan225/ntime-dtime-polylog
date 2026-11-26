import P1ChkGreedy.Refresh
import P1ChkFinal.C10Bits
import P1P7.RefreshLocal

/-!
# P1ChkFinal.C7R: check C7 at a REFRESH block on the STORED fields (decision D15, fix A; lane P1-lean-greedy)

The paper's C7 checks every refresh block too ("resp. by the block widths, for a refresh"). The Prop `C7r` (Refresh.lean)
is the check on a true state. Here the check reads the witness `u` only:
* the term slot of block `(Y, key)` of level `ℓ` (key = number of the lane word `l`), field `0` = presence flag, fields
  `1 + j * dH + h` = the outer index (the convention of `P1ChkFinal.decR` and of the C10 refresh stage, hypothesis `hterm`);
* `C7Rchk bw D u ℓ Y key`: the flag is EXACTLY `1` and the stored vector passes OpenAI's integer admission test for the
  block demand widths `bw` (`C7r_iff_admit`). In the family, `bw` is the stored-field reader of the block demand widths
  (radius one: the base and its in-neighbours, P7 `demandOf`, C10's `tieCell`); here `bw` is a parameter.
LINK `C7Rchk_iff`: with `bw = blockW X (x, l)`, `C7Rchk .. (addr x) (bwNum l) ↔ C7r X (storedTm ..) (x, l)`.
TESTS (D15): T1/T2 `C7Rchk_flag`: any flag other than `1` (0 = the counterexample of GreedyRefreshGap, 2, ...) is rejected;
`C7Rchk_not_admitted`: a stored vector that is not admitted is rejected.
-/

namespace P1ChkFinal.C7R

open P1ChkGreedy
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

section C7R

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

variable (a dH) in
/-- The stored outer index of the term slot `(Y, key)` of level `ℓ`. -/
def storedVec (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ) : Fin (2 ^ a) × Fin dH → ℕ :=
  fun jh => P1Wit.rdTerms D u ℓ Y key (1 + ((jh.1 : ℕ) * dH + jh.2))

/-- **C7 (refresh) on the stored fields** at the term slot `(Y, key)` of level `ℓ`, for block demand widths `bw`. -/
def C7Rchk (bw : Tie (2 ^ a) → ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ) : Prop :=
  P1Wit.rdTerms D u ℓ Y key 0 = 1 ∧
    MotifAdmission.admit (Refresh.expanderMass (D := 2 ^ a) (2 ^ a₀)) (storedVec a dH D u ℓ Y key)
      (MotifConversion.repetitions F bw) F.scale F.radius = true

instance (bw : Tie (2 ^ a) → ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ) :
    Decidable (C7Rchk P hdH hconn F bw D u ℓ Y key) := by
  unfold C7Rchk; infer_instance

/-- The stored term table of a refresh state: `some` stored vector when the flag is `1`, else `none`. -/
def storedTm (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g)) :
    X.Base × BitWord g → Option (Fin (2 ^ a) × Fin dH → ℕ) :=
  fun s => if P1Wit.rdTerms D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) 0 = 1 then
    some (storedVec a dH D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2)) else none

/-- **Link**: the stored-field check equals `C7r` on the stored term table, at the true block widths. -/
theorem C7Rchk_iff (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g)) (s : X.Base × BitWord g) :
    C7Rchk P hdH hconn F (blockW X s) D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) ↔
      C7r P hdH hconn F X (storedTm D u ℓ X) s := by
  rw [C7r_iff_admit]
  unfold C7Rchk storedTm
  by_cases hf : P1Wit.rdTerms D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) 0 = 1
  · simp only [hf, if_true, true_and, Option.some.injEq, exists_eq_left']
  · simp only [hf, if_false, false_and, reduceCtorEq, exists_false]

/-- **T1/T2**: a flag other than `1` is rejected (0: the slot claims no term; 2 or more: no code of a tuple). -/
theorem C7Rchk_flag (bw : Tie (2 ^ a) → ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ)
    (h : P1Wit.rdTerms D u ℓ Y key 0 ≠ 1) : ¬ C7Rchk P hdH hconn F bw D u ℓ Y key :=
  fun hc => h hc.1

/-- **T2**: a stored vector that the admission test rejects is rejected. -/
theorem C7Rchk_not_admitted (bw : Tie (2 ^ a) → ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ)
    (h : MotifAdmission.admit (Refresh.expanderMass (D := 2 ^ a) (2 ^ a₀)) (storedVec a dH D u ℓ Y key)
      (MotifConversion.repetitions F bw) F.scale F.radius = false) : ¬ C7Rchk P hdH hconn F bw D u ℓ Y key :=
  fun hc => by rw [hc.2] at h; exact Bool.noConfusion h

/-- Soundness on a true table (T3 at the state level): if the stored terms are those of a refresh choice `c`, the check
holds at every block, at the true block widths. -/
theorem C7Rchk_true (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) (h : storedTm D u ℓ X = trueBlockTerms P hdH hconn F X c)
    (s : X.Base × BitWord g) :
    C7Rchk P hdH hconn F (blockW X s) D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) :=
  (C7Rchk_iff P hdH hconn F D u ℓ X s).mpr (h ▸ C7r_true P hdH hconn F X c s)

/-- Uniqueness (the refresh part of the greedy step): the check at every block gives exactly one refresh choice whose
terms are the stored ones. -/
theorem C7Rchk_unique (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (h : ∀ s : X.Base × BitWord g,
      C7Rchk P hdH hconn F (blockW X s) D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2)) :
    ∃! c : DyadicRefreshChoice X P hdH hconn F, storedTm D u ℓ X = trueBlockTerms P hdH hconn F X c :=
  C7r_unique P hdH hconn F X fun s => (C7Rchk_iff P hdH hconn F D u ℓ X s).mp (h s)

/-! ## The block demand widths read from the stored fields (radius one: the base and its in-neighbours) -/

variable (a) in
/-- The stored far slot of in-slot `s` of address `Y`, as a slot number (`mod 2^a`). -/
def inFarS (D : P1Wit.Dims) (u : List Bool) (ℓ Y : ℕ) (s : Fin (2 ^ a)) : Fin (2 ^ a) :=
  ⟨P1Wit.rdInFar D u ℓ Y s % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩

variable (a g) in
/-- **The stored-field block demand widths** of block `(Y, l)` of a refresh level: P7's `demandOf` on the stored
out-widths of `Y` and, per in-slot `s`, the stored far slot, displacement and out-widths of the stored in-neighbour. -/
def bwS (D : P1Wit.Dims) (u : List Bool) (ℓ Y : ℕ) (l : BitWord g) : Tie (2 ^ a) → ℕ :=
  P1P7.demandOf (fun k w => P1Wit.rdWidth D u ℓ Y (P1ChkFinal.bwNum w) k)
    (fun s => (inFarS a D u ℓ Y s, P1ChkFinal.bwOf (a + g) (P1Wit.rdInDisp D u ℓ Y s),
      fun k w => P1Wit.rdWidth D u ℓ (P1Wit.rdInAddr D u ℓ Y s) (P1ChkFinal.bwNum w) k)) l

/-- **The stored-field widths are the true block demand widths** when the stored panels of the level are the true ones. -/
theorem bwS_correct (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (hP : ∀ y, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X y) (P1P7.panel X y)) (x : X.Base) (l : BitWord g) :
    bwS a g D u ℓ (P1P7.addr X x) l = blockW X (x, l) := by
  rw [blockW, P1P7.demand_eq]
  unfold bwS
  congr 1
  · funext k w
    exact (hP x k).2.2.2.2.2.2 w
  · funext s
    obtain ⟨-, -, -, hA, hD, hF, -⟩ := hP x s
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Fin.ext
      change P1Wit.rdInFar D u ℓ (P1P7.addr X x) s % 2 ^ a = _
      rw [hF]
      exact Nat.mod_eq_of_lt (Fin.isLt _)
    · change P1ChkFinal.bwOf (a + g) (P1Wit.rdInDisp D u ℓ (P1P7.addr X x) s) = _
      rw [hD, P1ChkFinal.bwOf_bwNum]
      rfl
    · funext k w
      change P1Wit.rdWidth D u ℓ (P1Wit.rdInAddr D u ℓ (P1P7.addr X x) s) (P1ChkFinal.bwNum w) k = _
      rw [hA]
      exact (hP _ k).2.2.2.2.2.2 w

/-- **C7 (refresh) at the term slot `(Y, key)` on the stored fields only** (the decision of the family). -/
def C7Rat (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ) : Prop :=
  C7Rchk P hdH hconn F (bwS a g D u ℓ Y (P1ChkFinal.bwOf g key)) D u ℓ Y key

instance (D : P1Wit.Dims) (u : List Bool) (ℓ Y key : ℕ) : Decidable (C7Rat (g := g) P hdH hconn F D u ℓ Y key) := by
  unfold C7Rat; infer_instance

/-- **Link at the block level** (true panels): the stored-field check at `(addr x, bwNum l)` is `C7r` on the stored
term table. -/
theorem C7Rat_iff (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (hP : ∀ y, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X y) (P1P7.panel X y)) (s : X.Base × BitWord g) :
    C7Rat (g := g) P hdH hconn F D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2) ↔
      C7r P hdH hconn F X (storedTm D u ℓ X) s := by
  unfold C7Rat
  rw [P1ChkFinal.bwOf_bwNum, bwS_correct D u ℓ X hP]
  exact C7Rchk_iff P hdH hconn F D u ℓ X s

/-- **The refresh part of the greedy step, state level**: C7 (refresh) at every block of the level holds exactly when the
stored term table is the table of a (unique) refresh choice. -/
theorem C7Rat_all_iff (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (hP : ∀ y, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X y) (P1P7.panel X y)) :
    (∀ s : X.Base × BitWord g, C7Rat (g := g) P hdH hconn F D u ℓ (P1P7.addr X s.1) (P1ChkFinal.bwNum s.2)) ↔
      ∃ c : DyadicRefreshChoice X P hdH hconn F, storedTm D u ℓ X = trueBlockTerms P hdH hconn F X c := by
  rw [← C7r_iff P hdH hconn F X]
  exact forall_congr' fun s => C7Rat_iff P hdH hconn F D u ℓ X hP s

/-- The stored term table of a refresh choice gives C10's `hterm` (the stored vector entries are the choice's values). -/
theorem hterm_of_storedTm (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) (h : storedTm D u ℓ X = trueBlockTerms P hdH hconn F X c) :
    ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      P1Wit.rdTerms D u ℓ (P1P7.addr X y) (P1ChkFinal.bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh := by
  intro y l jh
  have hs := congrFun h (y, l)
  unfold storedTm trueBlockTerms at hs
  split at hs
  · exact congrFun (Option.some.inj hs) jh
  · exact absurd hs (by simp)

end C7R

end P1ChkFinal.C7R

#print axioms P1ChkFinal.C7R.C7Rchk_iff
#print axioms P1ChkFinal.C7R.C7Rchk_unique
#print axioms P1ChkFinal.C7R.bwS_correct
#print axioms P1ChkFinal.C7R.C7Rat_all_iff
#print axioms P1ChkFinal.C7R.hterm_of_storedTm
