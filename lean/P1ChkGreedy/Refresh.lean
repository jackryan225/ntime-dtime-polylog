import P1ChkGreedy.Checks

/-!
# P1ChkGreedy.Refresh: check C7 at a REFRESH substep (the paper: "resp. by the block widths, for a refresh")

Lane P1-lean-W2-chkgreedy. At a refresh substep there are no colours, offsets, energy prefixes or layout bit
(C5, C6, C8, C9 are checks of shrinking levels only). The terms are OpenAI's `BlockChoices`
(DegreeRefreshConversion.lean:57, used by `DyadicRefreshChoice`, DegreeRefreshPass.lean:38): ONE admitted outer index
per block `s = (x, l)` (`x` an old base, `l` a remaining lane `BitWord g`), admitted for the block demand (tie) widths
`blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s`. Every block has a term (no empty slot).
An outer index is `Fin (2 ^ a) × Fin dH → ℕ`; admission is OpenAI's integer test `MotifAdmission.admit` with the fixed
rational masses `expanderMass (2 ^ a₀)` (`C7r_iff_admit`).
The block terms are keyed at the block's base `x` (the convention of `P1P7.refresh_panel_local`, hypothesis `hterm`).
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

section RefreshTerms

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

/-- The block demand (tie) widths of block `s` of a refresh substep (OpenAI `blockDemandWidths` on the split slots
and widths of the state, exactly the widths of `DyadicRefreshChoice`). -/
noncomputable abbrev blockW (X : State a (a + g)) (s : X.Base × BitWord g) :=
  blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s

/-- **C7, refresh form**, at block `s = (x, l)`: the term slot holds an outer index admitted for the block demand
widths of `s`. -/
def C7r (X : State a (a + g)) (tm : X.Base × BitWord g → Option (Fin (2 ^ a) × Fin dH → ℕ))
    (s : X.Base × BitWord g) : Prop :=
  ∃ v, tm s = some v ∧ v ∈ MotifConversion.outerIndices F (blockW X s)

/-- The masses of the refresh supply are positive (needed for the integer form of admission). -/
theorem expanderMass_pos (e : Fin (2 ^ a) × Fin dH) : 0 < Refresh.expanderMass (D := 2 ^ a) (2 ^ a₀) e := by
  unfold Refresh.expanderMass
  exact div_pos (Nat.cast_pos.mpr (Nat.two_pow_pos a)) (Nat.cast_pos.mpr (Nat.two_pow_pos a₀))

/-- C7 (refresh) with OpenAI's integer admission test: what the checker evaluates. -/
theorem C7r_iff_admit (X : State a (a + g)) (tm : X.Base × BitWord g → Option (Fin (2 ^ a) × Fin dH → ℕ))
    (s : X.Base × BitWord g) :
    C7r P hdH hconn F X tm s ↔
      ∃ v, tm s = some v ∧
        MotifAdmission.admit (Refresh.expanderMass (D := 2 ^ a) (2 ^ a₀)) v
          (MotifConversion.repetitions F (blockW X s)) F.scale F.radius = true := by
  unfold C7r
  simp only [MotifConversion.mem_outerIndices_iff F expanderMass_pos]

/-- The term table of a refresh choice `c` (one admitted index per block). -/
def trueBlockTerms (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (s : X.Base × BitWord g) : Option (Fin (2 ^ a) × Fin dH → ℕ) :=
  some (c s).val

theorem C7r_true (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (s : X.Base × BitWord g) :
    C7r P hdH hconn F X (trueBlockTerms P hdH hconn F X c) s :=
  ⟨_, rfl, (c s).property⟩

/-- C7 (refresh) at every block determines exactly one refresh choice. -/
theorem C7r_unique (X : State a (a + g)) {tm : X.Base × BitWord g → Option (Fin (2 ^ a) × Fin dH → ℕ)}
    (h : ∀ s, C7r P hdH hconn F X tm s) :
    ∃! c : DyadicRefreshChoice X P hdH hconn F, tm = trueBlockTerms P hdH hconn F X c := by
  unfold C7r at h
  choose v hv using h
  refine ⟨fun s => ⟨v s, (hv s).2⟩, ?_, ?_⟩
  · funext s
    exact (hv s).1
  · intro c' hc'
    funext s
    apply Subtype.ext
    have h2 := (hv s).1
    rw [hc'] at h2
    exact Option.some.inj h2

theorem C7r_iff (X : State a (a + g)) (tm : X.Base × BitWord g → Option (Fin (2 ^ a) × Fin dH → ℕ)) :
    (∀ s, C7r P hdH hconn F X tm s) ↔
      ∃ c : DyadicRefreshChoice X P hdH hconn F, tm = trueBlockTerms P hdH hconn F X c :=
  ⟨fun h => (C7r_unique P hdH hconn F X h).exists,
    fun ⟨c, hc⟩ => hc ▸ C7r_true P hdH hconn F X c⟩

theorem trueBlockTerms_injective (X : State a (a + g)) :
    Function.Injective (trueBlockTerms P hdH hconn F X) := by
  intro c c' h
  funext s
  apply Subtype.ext
  exact Option.some.inj (congrFun h s)

end RefreshTerms

end P1ChkGreedy
