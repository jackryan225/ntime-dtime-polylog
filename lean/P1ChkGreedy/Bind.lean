import P1ChkGreedy.Refresh
import P1Wit.Layout

/-!
# P1ChkGreedy.Bind: checks C5-C9 on the witness bits (P6 layout `P1Wit.Layout`)

Lane P1-lean-W2-chkgreedy. The checks of `P1ChkGreedy.Checks` (shrinking level) and `P1ChkGreedy.Refresh` (refresh
level) take tables over the bases; here the tables are READ from a witness `u : List Bool` with the readers of
`P1Wit.Layout` (lane P1-lean-W2-P6) at level `ℓ`, and each check also tests that the fields it reads are in range
and that unused parts are zero (paper: "Each check also verifies that the fields it reads are in range and that
their unused parts are zero"). Base `y` sits at address `P1P7.addr X y = X.baseIndex y`.

Codes (the P6 layout stores natural numbers; the integration and P6 must use these same codes):
* colour `c : Fin (2 * 2 ^ a + 1)` ↦ `c.val`; tag offset `t` ↦ `bitWordFinEquiv _ t` (as a number);
* energy prefix `E_l(y)` at index `c = eCode l`: `eCode true = 0` (paper `E_1`), `eCode false = 1` (paper `E_2`);
  so C9 "layout bit = decide (E true < E false)" is the paper's "layout 1 iff E_2 ≤ E_1";
* layout bit `b` ↦ `layoutCode b` (`false ↦ 0` = paper layout 1, `true ↦ 1`);
* shrink term slot of the old arc `e`: base = source base of `e`, key = `lane * 2^a + k` where
  `((y, k), lane) = (packingArcEquiv _ a g).symm e` (`lane` as the number `bitWordFinEquiv`); field `0` = presence flag,
  field `1 + termIdx v` = number `v` of the outer index, `termIdx (b, j) = 4 * b + j`; empty slot = all zero
  (`termCode`);
* refresh term slot of the block `(x, l)`: base `x`, key = `bitWordFinEquiv g l`, field `0` = presence flag (always 1),
  field `1 + (j * dH + h)` = number `(j, h)` of the outer index.

Main results: `level_u_iff` (shrinking level: all of C5-C9 pass on `u` iff the readers return the true colours,
offsets, and the term codes, energy prefixes and layout code of some admitted selection `s`), `level_u_sel_unique`
(that `s` is unique), and `refresh_u_iff`, `refresh_u_sel_unique` (refresh level).
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

noncomputable section

/-! ## Codes -/

/-- Index of energy group `l` in the energy fields of a base (`E_1` = group `true`, `E_2` = group `false`). -/
def eCode (l : Bool) : ℕ := if l then 0 else 1

/-- Code of the layout bit. -/
def layoutCode (b : Bool) : ℕ := if b then 1 else 0

theorem layout_iff (v : ℕ) (b : Bool) : (v < 2 ∧ decide (v = 1) = b) ↔ v = layoutCode b := by
  constructor
  · rintro ⟨h1, rfl⟩
    unfold layoutCode
    by_cases h : v = 1
    · rw [if_pos (decide_eq_true h)]
      exact h
    · rw [if_neg (by simpa using h)]
      omega
  · rintro rfl
    cases b <;> decide

/-- Position of number `(b, j)` of a shrink outer index (`Bool × Fin 4 → ℕ`) inside its term slot (after the flag). -/
def termIdx (p : Bool × Fin 4) : ℕ := (if p.1 then 4 else 0) + p.2

/-- A term slot as (presence flag, numbers): empty = `(0, 0)`, an index `v` = `(1, v)`. -/
def termCode {S : Type*} : Option (S → ℕ) → ℕ × (S → ℕ)
  | none => (0, fun _ => 0)
  | some v => (1, v)

/-- Decode a number below `n` into `Fin n` (`0` outside the range; the checks test the range). -/
def finOr0 (n : ℕ) [NeZero n] (v : ℕ) : Fin n := if h : v < n then ⟨v, h⟩ else 0

theorem finOr0_val {n : ℕ} [NeZero n] {v : ℕ} (h : v < n) : (finOr0 n v : ℕ) = v := by
  simp [finOr0, h]

theorem finOr0_eq_iff {n : ℕ} [NeZero n] (v : ℕ) (c : Fin n) : (v < n ∧ finOr0 n v = c) ↔ v = c := by
  constructor
  · rintro ⟨h, rfl⟩
    exact (finOr0_val h).symm
  · rintro rfl
    exact ⟨c.isLt, Fin.ext (finOr0_val c.isLt)⟩

/-! ## Shrinking level: C5 and C6 -/

section StateGreedyU

variable {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- The stored colours of level `ℓ`, decoded. -/
def colOf (X : State a (packingLaneBits a g)) (y : X.Base) : Fin (2 * 2 ^ a + 1) :=
  finOr0 _ (P1Wit.rdColour D u ℓ (P1P7.addr X y))

/-- The stored tag offsets of level `ℓ`, decoded (`bitWordFinEquiv`). -/
def offOf (X : State a (packingLaneBits a g)) (y : X.Base) : BitWord (packingTagBits (2 ^ a)) :=
  (bitWordFinEquiv (packingTagBits (2 ^ a))).symm (finOr0 _ (P1Wit.rdOffset D u ℓ (P1P7.addr X y)))

/-- **C5 on the witness** at base `y`: the stored colour is in range and passes C5. -/
abbrev C5u (X : State a (packingLaneBits a g)) (y : X.Base) : Prop :=
  P1Wit.rdColour D u ℓ (P1P7.addr X y) < 2 * 2 ^ a + 1 ∧ C5s X (colOf D u ℓ X) y

/-- **C6 on the witness** at base `y`: the stored offset is in range and passes C6. -/
abbrev C6u (X : State a (packingLaneBits a g)) (y : X.Base) : Prop :=
  P1Wit.rdOffset D u ℓ (P1P7.addr X y) < 2 ^ packingTagBits (2 ^ a) ∧ C6s X (offOf D u ℓ X) y

theorem C5u_iff (X : State a (packingLaneBits a g)) :
    (∀ y, C5u D u ℓ X y) ↔ ∀ y, P1Wit.rdColour D u ℓ (P1P7.addr X y) = (X.packingData.color y : ℕ) := by
  constructor
  · intro h y
    have hc := C5s_unique X fun z => (h z).2
    exact (finOr0_eq_iff _ _).mp ⟨(h y).1, congrFun hc y⟩
  · intro h
    have hc : colOf D u ℓ X = X.packingData.color := by
      funext y
      exact ((finOr0_eq_iff _ _).mpr (h y)).2
    intro y
    refine ⟨by rw [h y]; exact (X.packingData.color y).isLt, ?_⟩
    rw [hc]
    exact C5s_true X y

theorem C6u_iff (X : State a (packingLaneBits a g)) :
    (∀ y, C6u D u ℓ X y) ↔ ∀ y, P1Wit.rdOffset D u ℓ (P1P7.addr X y) =
      (bitWordFinEquiv (packingTagBits (2 ^ a)) (X.packingData.offset y) : ℕ) := by
  constructor
  · intro h y
    have hc := C6s_unique X fun z => (h z).2
    have hy : offOf D u ℓ X y = X.packingData.offset y := congrFun hc y
    unfold offOf at hy
    rw [Equiv.symm_apply_eq] at hy
    exact (finOr0_eq_iff _ _).mp ⟨(h y).1, hy⟩
  · intro h
    have hc : offOf D u ℓ X = X.packingData.offset := by
      funext y
      unfold offOf
      rw [Equiv.symm_apply_eq]
      exact ((finOr0_eq_iff _ _).mpr (h y)).2
    intro y
    refine ⟨by rw [h y]; exact Fin.isLt _, ?_⟩
    rw [hc]
    exact C6s_true X y

end StateGreedyU

/-! ## Shrinking level: C7, C8, C9 -/

section TermsU

attribute [local instance] P1P7.instDecEqBase

variable {a g : ℕ} {factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- Base, key of the term slot of an old arc (keyed at the wire's source base). -/
def arcKey (X : State a (packingLaneBits a g)) (e : OldArc X) : ℕ × ℕ :=
  let p := (packingArcEquiv X.Base a g).symm e
  (P1P7.addr X p.1.1, (bitWordFinEquiv (packingLaneBits a g) p.2 : ℕ) * 2 ^ a + (p.1.2 : ℕ))

/-- The stored term slot of an old arc: (presence flag, the eight numbers). -/
def rawOf (X : State a (packingLaneBits a g)) (e : OldArc X) : ℕ × (Bool × Fin 4 → ℕ) :=
  (P1Wit.rdTerms D u ℓ (arcKey X e).1 (arcKey X e).2 0,
    fun p => P1Wit.rdTerms D u ℓ (arcKey X e).1 (arcKey X e).2 (1 + termIdx p))

/-- The stored term table, decoded: an index iff the flag is `1`. -/
def tmOf (X : State a (packingLaneBits a g)) (e : OldArc X) : Option (Bool × Fin 4 → ℕ) :=
  if (rawOf D u ℓ X e).1 = 1 then some (rawOf D u ℓ X e).2 else none

/-- The stored energy prefixes, decoded. -/
def EOf (X : State a (packingLaneBits a g)) (y : X.Base) (l : Bool) : ℕ :=
  P1Wit.rdEnergy D u ℓ (P1P7.addr X y) (eCode l)

theorem tmOf_of_raw (X : State a (packingLaneBits a g)) (e : OldArc X) (o : Option (Bool × Fin 4 → ℕ))
    (h : rawOf D u ℓ X e = termCode o) : tmOf D u ℓ X e = o := by
  unfold tmOf
  cases o with
  | none =>
    rw [h]
    simp [termCode]
  | some v =>
    rw [h]
    simp [termCode]

/-- **C7 on the witness** at the term slot of the old arc `e`: a motif slot has flag `1` and an admitted index, any
other slot is all zero. -/
def C7u (X : State a (packingLaneBits a g)) (e : OldArc X) : Prop :=
  if h : IsMotif X e then (rawOf D u ℓ X e).1 = 1 ∧
      (rawOf D u ℓ X e).2 ∈ MotifConversion.outerIndices B (demandW X ⟨e, h⟩)
  else rawOf D u ℓ X e = (0, fun _ => 0)

theorem C7u_iff (X : State a (packingLaneBits a g)) (e : OldArc X) :
    C7u B D u ℓ X e ↔ C7 B X (tmOf D u ℓ X) e ∧ rawOf D u ℓ X e = termCode (tmOf D u ℓ X e) := by
  unfold C7u C7
  by_cases h : IsMotif X e
  · rw [dif_pos h, dif_pos h]
    constructor
    · rintro ⟨h1, h2⟩
      have ht : tmOf D u ℓ X e = some (rawOf D u ℓ X e).2 := by
        unfold tmOf
        rw [if_pos h1]
      refine ⟨⟨_, ht, h2⟩, ?_⟩
      rw [ht]
      exact Prod.ext h1 rfl
    · rintro ⟨⟨v, hv, hmem⟩, hraw⟩
      rw [hv, termCode] at hraw
      rw [hraw]
      exact ⟨rfl, hmem⟩
  · rw [dif_neg h, dif_neg h]
    constructor
    · intro hraw
      have ht : tmOf D u ℓ X e = none := tmOf_of_raw D u ℓ X e none hraw
      exact ⟨ht, by rw [ht]; exact hraw⟩
    · rintro ⟨ht, hraw⟩
      rw [hraw, ht]
      rfl

/-- **C8 on the witness** at base `y`. -/
def C8u (X : State a (packingLaneBits a g)) (y : X.Base) : Prop :=
  C8 X (storedWidths B X (tmOf D u ℓ X)) (EOf D u ℓ X) y

/-- **C9 on the witness** (one per shrinking level): the layout field is a bit and passes C9. -/
abbrev C9u (X : State a (packingLaneBits a g)) : Prop :=
  P1Wit.rdLayout D u ℓ < 2 ∧ C9 X (EOf D u ℓ X) (decide (P1Wit.rdLayout D u ℓ = 1))

theorem trueTerms_injective (X : State a (packingLaneBits a g)) : Function.Injective (trueTerms B X) := by
  intro s s' h
  funext m
  apply Subtype.ext
  have h1 := congrFun h m.val
  rw [trueTerms_motif, trueTerms_motif] at h1
  exact Option.some.inj h1

/-- **One shrinking level on the witness.** All of C5-C9 pass on `u` at level `ℓ` iff the readers return the true
colours and offsets, and the term codes, energy prefixes and layout code of an admitted selection `s`. -/
theorem level_u_iff (X : State a (packingLaneBits a g)) :
    ((∀ y, C5u D u ℓ X y) ∧ (∀ y, C6u D u ℓ X y) ∧ (∀ e, C7u B D u ℓ X e) ∧
        (∀ y, C8u B D u ℓ X y) ∧ C9u D u ℓ X) ↔
      (∀ y, P1Wit.rdColour D u ℓ (P1P7.addr X y) = (X.packingData.color y : ℕ)) ∧
      (∀ y, P1Wit.rdOffset D u ℓ (P1P7.addr X y) =
        (bitWordFinEquiv (packingTagBits (2 ^ a)) (X.packingData.offset y) : ℕ)) ∧
      ∃ s : X.ShrinkSelection B, (∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e)) ∧
        (∀ y l, P1Wit.rdEnergy D u ℓ (P1P7.addr X y) (eCode l) = truePrefix X (termW B X s) y l) ∧
        P1Wit.rdLayout D u ℓ = layoutCode (P1P7.layoutBit B X s) := by
  rw [C5u_iff, C6u_iff]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨h7, h8, h9⟩
    have h7' : ∀ e, C7 B X (tmOf D u ℓ X) e := fun e => ((C7u_iff B D u ℓ X e).mp (h7 e)).1
    obtain ⟨s, hs, -⟩ := C7_unique B X h7'
    have hE : EOf D u ℓ X = truePrefix X (termW B X s) := by
      apply C8_unique
      intro y
      have h8y := h8 y
      unfold C8u at h8y
      rwa [hs, storedWidths_trueTerms] at h8y
    refine ⟨s, fun e => ?_, fun y l => congrFun (congrFun hE y) l, ?_⟩
    · have := ((C7u_iff B D u ℓ X e).mp (h7 e)).2
      rwa [hs] at this
    · obtain ⟨hlt, h9'⟩ := h9
      rw [hE] at h9'
      exact (layout_iff _ _).mp ⟨hlt, (C9_unique B X s h9')⟩
  · rintro ⟨s, hterm, hE, hlay⟩
    have htm : tmOf D u ℓ X = trueTerms B X s := by
      funext e
      exact tmOf_of_raw D u ℓ X e _ (hterm e)
    have hE' : EOf D u ℓ X = truePrefix X (termW B X s) := by
      funext y l
      exact hE y l
    refine ⟨fun e => (C7u_iff B D u ℓ X e).mpr ⟨?_, ?_⟩, fun y => ?_, ?_⟩
    · rw [htm]
      exact C7_true B X s e
    · rw [htm]
      exact hterm e
    · unfold C8u
      rw [htm, storedWidths_trueTerms, hE']
      exact C8_true X _ y
    · obtain ⟨hlt, hdec⟩ := (layout_iff _ _).mpr hlay
      unfold C9u
      refine ⟨hlt, ?_⟩
      rw [hE', hdec]
      exact C9_true B X s

/-- The selection of `level_u_iff` is unique: the term codes determine it. -/
theorem level_u_sel_unique (X : State a (packingLaneBits a g)) {s s' : X.ShrinkSelection B}
    (h : ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e))
    (h' : ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s' e)) : s = s' := by
  apply trueTerms_injective B X
  funext e
  have h1 := (tmOf_of_raw D u ℓ X e _ (h e)).symm
  rw [tmOf_of_raw D u ℓ X e _ (h' e)] at h1
  exact h1

end TermsU

/-! ## Refresh level: C7 (refresh form) -/

section RefreshU

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
variable (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- The stored term slot of block `s = (x, l)` of a refresh level: (presence flag, the `2^a * dH` numbers). -/
def rawR (X : State a (a + g)) (s : X.Base × BitWord g) : ℕ × (Fin (2 ^ a) × Fin dH → ℕ) :=
  (P1Wit.rdTerms D u ℓ (P1P7.addr X s.1) (bitWordFinEquiv g s.2 : ℕ) 0,
    fun p => P1Wit.rdTerms D u ℓ (P1P7.addr X s.1) (bitWordFinEquiv g s.2 : ℕ) (1 + ((p.1 : ℕ) * dH + p.2)))

/-- The stored block terms, decoded. -/
def tmR (X : State a (a + g)) (s : X.Base × BitWord g) : Option (Fin (2 ^ a) × Fin dH → ℕ) :=
  if (rawR (dH := dH) D u ℓ X s).1 = 1 then some (rawR D u ℓ X s).2 else none

/-- **C7 (refresh form) on the witness** at block `s`: flag `1` and an admitted index. -/
abbrev C7ru (X : State a (a + g)) (s : X.Base × BitWord g) : Prop :=
  (rawR (dH := dH) D u ℓ X s).1 = 1 ∧
    (rawR D u ℓ X s).2 ∈ MotifConversion.outerIndices F (blockW X s)

theorem C7ru_iff (X : State a (a + g)) (s : X.Base × BitWord g) :
    C7ru P hdH hconn F D u ℓ X s ↔ C7r P hdH hconn F X (tmR D u ℓ X) s ∧
      rawR (dH := dH) D u ℓ X s = termCode (tmR D u ℓ X s) := by
  unfold C7ru C7r tmR
  constructor
  · rintro ⟨h1, h2⟩
    rw [if_pos h1]
    exact ⟨⟨_, rfl, h2⟩, Prod.ext h1 rfl⟩
  · rintro ⟨⟨v, hv, hmem⟩, hraw⟩
    by_cases h1 : (rawR (dH := dH) D u ℓ X s).1 = 1
    · rw [if_pos h1] at hv
      refine ⟨h1, ?_⟩
      rw [Option.some.inj hv]
      exact hmem
    · rw [if_neg h1] at hv
      cases hv

/-- **One refresh level on the witness.** C7 passes at every block iff the readers return the term codes of a
refresh choice `c` (`DyadicRefreshChoice`). -/
theorem refresh_u_iff (X : State a (a + g)) :
    (∀ s, C7ru P hdH hconn F D u ℓ X s) ↔
      ∃ c : DyadicRefreshChoice X P hdH hconn F,
        ∀ s, rawR D u ℓ X s = termCode (trueBlockTerms P hdH hconn F X c s) := by
  constructor
  · intro h
    have h' : ∀ s, C7r P hdH hconn F X (tmR D u ℓ X) s := fun s => ((C7ru_iff P hdH hconn F D u ℓ X s).mp (h s)).1
    obtain ⟨c, hc, -⟩ := C7r_unique P hdH hconn F X h'
    refine ⟨c, fun s => ?_⟩
    have := ((C7ru_iff P hdH hconn F D u ℓ X s).mp (h s)).2
    rwa [hc] at this
  · rintro ⟨c, hc⟩ s
    have hs : rawR D u ℓ X s = (1, (c s).val) := hc s
    unfold C7ru
    rw [hs]
    exact ⟨rfl, (c s).property⟩

/-- The refresh choice of `refresh_u_iff` is unique. -/
theorem refresh_u_sel_unique (X : State a (a + g)) {c c' : DyadicRefreshChoice X P hdH hconn F}
    (h : ∀ s, rawR D u ℓ X s = termCode (trueBlockTerms P hdH hconn F X c s))
    (h' : ∀ s, rawR D u ℓ X s = termCode (trueBlockTerms P hdH hconn F X c' s)) : c = c' := by
  funext s
  apply Subtype.ext
  have h1 : ((1 : ℕ), (c s).val) = (1, (c' s).val) := (h s).symm.trans (h' s)
  exact (Prod.mk.inj h1).2

end RefreshU

end

end P1ChkGreedy
