import P1ChkFinal.C10Bits

/-!
# P1, check C10 with an EXPLICIT recomputation `rc` (decision D10 of G3-chief; lane P1-lean-c10)

Defect found by P1-lean-oaireuse (board line 1724): `P1ChkFinal.C10sU` / `C10rU` use `recompShrink` / `recompRefresh`,
which are `Function.extend key out (fun _ => none)`. They return a panel only on the key of SOME global state, so no
program can decide them on a malformed witness (it would have to decide whether a stored ball belongs to a state).

Fix (D10): the check takes the recomputation `rc` as a PARAMETER. The stage lemmas hold under a correctness
hypothesis on `rc`. The program lane then supplies ONE explicit `rc` with that hypothesis.

* `ShrinkRc a b g`, `RefreshRc a a₀ g dH`: the types of a recomputation. A REFRESH recomputation has NO layout
  argument (a refresh substep stores no layout bit; research/p1/sec7/VERDICT.md row 1).
* `C10sRc rc D u ℓ Y`, `C10rRc rc D u ℓ Y`: check C10 on the bits at the level-`ℓ+1` address `Y`.
  They do not mention the fixed block, the state or `Function.extend`.
* `ShrinkRcAt B ready rc X s` / `RefreshRcAt .. rc X c`: `rc` is right on the true data of ONE state (weak form,
  the only thing the stage lemmas use). `ShrinkRcOK` / `RefreshRcOK`: right on every instance (D10's `hrc`).
* `C10sRc_stage`, `C10rRc_stage`: the stage lemmas (text of `P1ChkFinal.C10sU_stage` / `C10rU_stage` plus `hrc`).
* `C10sU_iff_rc`, `C10rU_iff_rc`, `shrinkRcOK_recomp`, `refreshRcOK_recomp`: the earlier forms are the instance
  `rc := recompShrink` / `recompRefresh`, and that instance satisfies `hrc`. So `hrc` is satisfiable for all parameters.
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open P1P7 P1Wit P1ChkFinal

/-! ## Shrinking substep -/

/-- A recomputation for a shrinking substep: parent address, stored level-`ℓ` data of the ball by address,
layout bit, child index; the result is the panel of the child, or `none`. -/
abbrev ShrinkRc (a b g : ℕ) : Type :=
  ℕ → (ℕ → Option (ShrinkDatum a g)) → Bool → ℕ → Option (PanelT b g)

/-- **Check C10 on the bits, shrinking substep `ℓ → ℓ + 1`, with the recomputation `rc`**, at the level-`ℓ+1`
address `Y`: `rc` returns a panel on the decoded data of the ball of radius 6 of the parent `Y / J` (walked by the
stored addresses), the decoded layout bit and the child index `Y % J`, and the stored level-`ℓ+1` numbers at `Y`
are the codes of that panel. -/
def C10sRc {a b g : ℕ} (rc : ShrinkRc a b g) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  ∃ p, rc (Y / shrinkJ a)
      (ballMap (nbOf shrinkNbrs (decS a g D u ℓ)) (decS a g D u ℓ) (Y / shrinkJ a) 6) (layoutOf D u ℓ)
      (Y % shrinkJ a) = some p ∧ PanelMatch D u (ℓ + 1) Y p

section Shrink

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- `rc` is right on the true data of the state `X` with the selection `s`: at every base `x` and tag `j` it
returns the panel of the child `(x, j)` in OpenAI's next state. -/
def ShrinkRcAt (rc : ShrinkRc a b g) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) : Prop :=
  ∀ (x : X.Base) (j : BitWord (packingTagBits (2 ^ a))),
    rc (addr X x) (ballMap (nbOf shrinkNbrs (shrinkOld B X s)) (shrinkOld B X s) (addr X x) 6)
      (layoutBit B X s) (bwNum j) = some (panel (X.shrinkNext B ready s) (x, j))

/-- D10's `hrc`: `rc` is right on every instance (every state, selection, base and tag). -/
def ShrinkRcOK (rc : ShrinkRc a b g) : Prop :=
  ∀ i : ShrinkInst a g B,
    rc (shrinkKey B i).1 (shrinkKey B i).2.1 (shrinkKey B i).2.2.1 (shrinkKey B i).2.2.2 = shrinkOut B ready i

theorem ShrinkRcOK.at {rc : ShrinkRc a b g} (h : ShrinkRcOK B ready rc) (X : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) : ShrinkRcAt B ready rc X s :=
  fun x j => h ⟨X, s, x, j⟩

/-- The earlier canonical recomputation satisfies `hrc` (so `hrc` is satisfiable for all parameters). -/
theorem shrinkRcOK_recomp : ShrinkRcOK B ready (recompShrink (g := g) B ready) :=
  fun i => (shrinkOut_factors (g := g) B ready).extend_apply (fun _ => none) i

/-- The earlier check is the instance `rc := recompShrink`. -/
theorem C10sU_iff_rc (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    C10sU (g := g) B ready D u ℓ Y ↔ C10sRc (recompShrink (g := g) B ready) D u ℓ Y :=
  Iff.rfl

/-- **C10 on the bits with `rc`, stage form (shrink).** Text of `P1ChkFinal.C10sU_stage` plus `hrc`. -/
theorem C10sRc_stage (rc : ShrinkRc a b g) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hrc : ShrinkRcAt B ready rc X s)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout D u ℓ = if layoutBit B X s then 1 else 0) :
    (∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sRc rc D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) := by
  have hd := decS_eq B D u ℓ X s hN hP hcol hoff hterm
  have hl := layoutOf_eq D u ℓ hlay
  have key : ∀ y, C10sRc rc D u ℓ (addr (X.shrinkNext B ready s) y) ↔
      PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) := by
    intro y
    obtain ⟨x, j⟩ := y
    have hlt : bwNum j < shrinkJ a := (bitWordFinEquiv _ j).isLt
    obtain ⟨hdiv, hmod⟩ := div_mod_prod (x := addr X x) hlt
    have haddr : addr (X.shrinkNext B ready s) (x, j) = shrinkJ a * addr X x + bwNum j :=
      shrink_addr B ready X s x j
    have hr := hrc x j
    unfold C10sRc
    rw [hd, hl, haddr, hdiv, hmod, hr]
    constructor
    · rintro ⟨p, hp, hm⟩
      cases hp
      exact hm
    · intro hm
      exact ⟨_, rfl, hm⟩
  constructor
  · intro h y
    exact (key y).mp (h _ (addr_lt _ y))
  · intro h Y hY
    obtain ⟨y, rfl⟩ := exists_addr_eq _ hY
    exact (key y).mpr (h y)

/-- The stage lemma under D10's `hrc` (right on every instance). -/
theorem C10sRc_stage_of_ok (rc : ShrinkRc a b g) (hrc : ShrinkRcOK B ready rc) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout D u ℓ = if layoutBit B X s then 1 else 0) :
    (∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sRc rc D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) :=
  C10sRc_stage B ready rc D u ℓ X s (hrc.at B ready X s) hN hP hcol hoff hterm hlay

end Shrink

/-! ## Refresh substep -/

/-- A recomputation for a refresh substep: parent address, stored level-`ℓ` data of the ball by address, child
index. NO layout bit. -/
abbrev RefreshRc (a a₀ g dH : ℕ) : Type :=
  ℕ → (ℕ → Option (RefreshDatum a g dH)) → ℕ → Option (PanelT a₀ g)

/-- **Check C10 on the bits, refresh substep `ℓ → ℓ + 1`, with the recomputation `rc`** (radius 1; no layout
bit is read). -/
def C10rRc {a a₀ g dH : ℕ} (rc : RefreshRc a a₀ g dH) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  ∃ p, rc (Y / 2 ^ a)
      (ballMap (nbOf refreshNbrs (decR a g dH D u ℓ)) (decR a g dH D u ℓ) (Y / 2 ^ a) 1)
      (Y % 2 ^ a) = some p ∧ PanelMatch D u (ℓ + 1) Y p

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- `rc` is right on the true data of the state `X` with the block terms `c`. -/
def RefreshRcAt (rc : RefreshRc a a₀ g dH) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) :
    Prop :=
  ∀ (x : X.Base) (j : Fin (2 ^ a)),
    rc (addr X x)
      (ballMap (nbOf refreshNbrs (refreshOld P hdH hconn F X c)) (refreshOld P hdH hconn F X c) (addr X x) 1)
      (j : ℕ) = some (panel (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j))

/-- D10's `hrc` for a refresh: `rc` is right on every instance. -/
def RefreshRcOK (rc : RefreshRc a a₀ g dH) : Prop :=
  ∀ i : RefreshInst a g P hdH hconn F,
    rc (refreshKey P hdH hconn F i).1 (refreshKey P hdH hconn F i).2.1 (refreshKey P hdH hconn F i).2.2 =
      refreshOut P hdH hconn F hD hd i

theorem RefreshRcOK.at {rc : RefreshRc a a₀ g dH} (h : RefreshRcOK P hdH hconn F hD hd rc) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F) : RefreshRcAt P hdH hconn F hD hd rc X c :=
  fun x j => h ⟨X, c, x, j⟩

/-- The earlier canonical recomputation, without its unused layout argument, satisfies `hrc`. -/
theorem refreshRcOK_recomp :
    RefreshRcOK P hdH hconn F hD hd (fun x Dt j => recompRefresh (g := g) P hdH hconn F hD hd x Dt false j) :=
  fun i => (refreshOut_factors (g := g) P hdH hconn F hD hd).extend_apply (fun _ => none) i

/-- The earlier check is the instance `rc := recompRefresh` (its layout argument was the constant `false`). -/
theorem C10rU_iff_rc (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    C10rU (g := g) P hdH hconn F hD hd D u ℓ Y ↔
      C10rRc (fun x Dt j => recompRefresh (g := g) P hdH hconn F hD hd x Dt false j) D u ℓ Y :=
  Iff.rfl

/-- **C10 on the bits with `rc`, stage form (refresh).** Text of `P1ChkFinal.C10rU_stage` plus `hrc`. -/
theorem C10rRc_stage (rc : RefreshRc a a₀ g dH) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F)
    (hrc : RefreshRcAt P hdH hconn F hD hd rc X c)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    (∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base, C10rRc rc D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
  have hdr := decR_eq P hdH hconn F D u ℓ X c hN hP hterm
  have key : ∀ y, C10rRc rc D u ℓ (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y) ↔
      PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
    intro y
    obtain ⟨x, j⟩ := y
    obtain ⟨hdiv, hmod⟩ := div_mod_prod (x := addr X x) j.isLt
    have haddr := refresh_addr P hdH hconn F hD hd X c x j
    have hr := hrc x j
    unfold C10rRc
    rw [hdr, haddr, hdiv, hmod, hr]
    constructor
    · rintro ⟨p, hp, hm⟩
      cases hp
      exact hm
    · intro hm
      exact ⟨_, rfl, hm⟩
  constructor
  · intro h y
    exact (key y).mp (h _ (addr_lt _ y))
  · intro h Y hY
    obtain ⟨y, rfl⟩ := exists_addr_eq _ hY
    exact (key y).mpr (h y)

/-- The stage lemma under D10's `hrc` (right on every instance). -/
theorem C10rRc_stage_of_ok (rc : RefreshRc a a₀ g dH) (hrc : RefreshRcOK P hdH hconn F hD hd rc) (D : Dims)
    (u : List Bool) (ℓ : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    (∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base, C10rRc rc D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) :=
  C10rRc_stage P hdH hconn F hD hd rc D u ℓ X c (hrc.at P hdH hconn F hD hd X c) hN hP hterm

end Refresh

end P1C10
