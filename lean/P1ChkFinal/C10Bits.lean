import P1ChkFinal.C10
import P1Wit.Layout

/-!
# P1, wave 2: check C10 on the witness bits (lane P1-lean-W2-chkfinal)

The stored numbers are read with the P6 readers of `P1Wit.Layout`. Codes (shared with C4 of the directory lane and
C5-C9 of the greedy lane, `P1ChkGreedy.Bind`):
* panel (P1)+(P2) of base `Y` at level `ℓ`, `PanelMatch`: out-slot `k`: `rdOutAddr` = head address,
  `rdOutDisp` = the displacement as the number `bitWordFinEquiv`, `rdOutFar` = far in-slot number; in-slots alike;
  `rdWidth ℓ Y (number of lane l) k` = width of out-slot `k` at lane `l`;
* colour = `Fin` value; tag offset = number `bitWordFinEquiv`; layout bit `b` = `if b then 1 else 0`;
* shrink term slot of the old arc `(((y, (t, l)), i), (u, h))`: base `y`, key = `lane * 2^a + i` with
  `lane` = the number of `(packingFields a g).symm (u, h, (t, l))` (= `P1ChkGreedy.arcKey`), field `0` = presence
  flag, field `1 + tIdx p` = number `p` (`tIdx (b, j) = 4 b + j`);
* refresh block term of `(x, l)`: base `x`, key = number of `l`, field `1 + (j * dH + h)` = number `(j, h)`.

`C10sU` / `C10rU`: the check at level-`ℓ+1` address `Y`: the panel recomputed (by `recompShrink` / `recompRefresh`)
from the DECODED level-`ℓ` data of the ball of the parent exists and the stored level-`ℓ+1` numbers at `Y` match
it. At a refresh no layout bit is read (G3-chief rule (2), 11:00Z).

`C10sU_stage` / `C10rU_stage` (stage form for `P1Count.stages_iff`): if the stored level-`ℓ` data are the codes of
the true data of `X` (and, for a shrink, of the selection `s` and its layout bit), then C10 passes at every address
of level `ℓ+1` iff the stored level-`ℓ+1` panels are the codes of the true panels of the next state.
-/

namespace P1ChkFinal

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open P1P7 P1Wit

/-! ## Number codes -/

/-- A bit word as a number. -/
def bwNum {G : ℕ} (w : BitWord G) : ℕ := (bitWordFinEquiv G w : ℕ)

/-- A number as a bit word (`0` if out of range). -/
def bwOf (G n : ℕ) : BitWord G :=
  (bitWordFinEquiv G).symm (if h : n < 2 ^ G then ⟨n, h⟩ else ⟨0, Nat.two_pow_pos G⟩)

theorem bwOf_bwNum {G : ℕ} (w : BitWord G) : bwOf G (bwNum w) = w := by
  unfold bwOf bwNum
  rw [dif_pos (bitWordFinEquiv G w).isLt]
  exact (bitWordFinEquiv G).symm_apply_apply w

/-- A number as a `Fin c` value (`0` if out of range; `c = 2 * 2^a + 1 > 0`). -/
def finOf (c : ℕ) (hc : 0 < c) (n : ℕ) : Fin c := if h : n < c then ⟨n, h⟩ else ⟨0, hc⟩

theorem finOf_val {c : ℕ} (hc : 0 < c) (v : Fin c) : finOf c hc (v : ℕ) = v := by
  unfold finOf
  rw [dif_pos v.isLt]

/-! ## Panels on the bits -/

/-- The stored numbers of the panel of address `Y` at level `ℓ` are the codes of `p`. -/
def PanelMatch (D : Dims) (u : List Bool) (ℓ Y : ℕ) {a g : ℕ} (p : PanelT a g) : Prop :=
  ∀ k : Fin (2 ^ a),
    rdOutAddr D u ℓ Y k = (p.1 k).1 ∧ rdOutDisp D u ℓ Y k = bwNum (p.1 k).2 ∧
    rdOutFar D u ℓ Y k = p.2.1 k ∧ rdInAddr D u ℓ Y k = (p.2.2.1 k).1 ∧
    rdInDisp D u ℓ Y k = bwNum (p.2.2.1 k).2 ∧ rdInFar D u ℓ Y k = p.2.2.2.1 k ∧
    ∀ l : BitWord g, rdWidth D u ℓ Y (bwNum l) k = p.2.2.2.2 k l

/-- The panel decoded from the stored numbers. -/
def decPanel (D : Dims) (u : List Bool) (ℓ Y a g : ℕ) : PanelT a g :=
  (fun k => (rdOutAddr D u ℓ Y k, bwOf g (rdOutDisp D u ℓ Y k)), fun k => rdOutFar D u ℓ Y k,
    fun k => (rdInAddr D u ℓ Y k, bwOf g (rdInDisp D u ℓ Y k)), fun k => rdInFar D u ℓ Y k,
    fun k l => rdWidth D u ℓ Y (bwNum l) k)

theorem decPanel_of_match {D : Dims} {u : List Bool} {ℓ Y a g : ℕ} {p : PanelT a g}
    (h : PanelMatch D u ℓ Y p) : decPanel D u ℓ Y a g = p := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := p
  unfold decPanel
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext k
    obtain ⟨h1, h2, -⟩ := h k
    refine Prod.ext h1 ?_
    show bwOf g (rdOutDisp D u ℓ Y k) = (p1 k).2
    rw [h2, bwOf_bwNum]
  · funext k
    exact (h k).2.2.1
  · funext k
    obtain ⟨-, -, -, h4, h5, -⟩ := h k
    refine Prod.ext h4 ?_
    show bwOf g (rdInDisp D u ℓ Y k) = (p3 k).2
    rw [h5, bwOf_bwNum]
  · funext k
    exact (h k).2.2.2.2.2.1
  · funext k l
    exact (h k).2.2.2.2.2.2 l

/-- The true panels by address, through `panelsOf`. -/
theorem panelsOf_addr {a g : ℕ} (X : State a g) (y : X.Base) : panelsOf X (addr X y) = some (panel X y) := by
  unfold panelsOf
  rw [baseAt_addr]
  rfl

/-- Every address below the number of bases is the address of a base. -/
theorem exists_addr_eq {a g : ℕ} (X : State a g) {Y : ℕ} (hY : Y < Fintype.card X.Base) : ∃ y, addr X y = Y :=
  ⟨X.baseIndex.symm ⟨Y, hY⟩, by simp [addr]⟩

/-! ## Shrinking substep -/

section Shrink

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- Index of the number `p` of an outer index inside a term slot (= `P1ChkGreedy.termIdx`). -/
def tIdx (p : Bool × Fin 4) : ℕ := (if p.1 then 4 else 0) + p.2

/-- The stored term data of the base with address `α`, decoded (keys as in `P1ChkGreedy.arcKey`). -/
def termsDec (D : Dims) (u : List Bool) (ℓ α : ℕ) :
    Fin (2 ^ a) → BitWord (packingTagBits (2 ^ a)) → BitWord g → BitWord (2 * 2 ^ a + 1) → BitWord a →
      Option (Bool × Fin 4 → ℕ) :=
  fun i t l w h =>
    if rdTerms D u ℓ α (bwNum ((packingFields a g).symm (w, h, (t, l))) * 2 ^ a + i) 0 = 1 then
      some (fun p => rdTerms D u ℓ α (bwNum ((packingFields a g).symm (w, h, (t, l))) * 2 ^ a + i) (1 + tIdx p))
    else none

variable (a g) in
/-- The decoded level-`ℓ` data of a shrinking substep by address (`none` from the number of bases on). -/
def decS (D : Dims) (u : List Bool) (ℓ : ℕ) : ℕ → Option (ShrinkDatum a g) :=
  fun α => if α < (D.lv ℓ).bases then
    some (decPanel D u ℓ α a (packingLaneBits a g), finOf (2 * 2 ^ a + 1) (by omega) (rdColour D u ℓ α),
      bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ α), termsDec D u ℓ α)
  else none

/-- The decoded layout bit. -/
def layoutOf (D : Dims) (u : List Bool) (ℓ : ℕ) : Bool := decide (rdLayout D u ℓ = 1)

/-- **Check C10 on the bits, shrinking substep `ℓ → ℓ + 1`**, at the level-`ℓ+1` address `Y`. -/
def C10sU (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  ∃ p, recompShrink (g := g) B ready (Y / shrinkJ a)
      (ballMap (nbOf shrinkNbrs (decS a g D u ℓ)) (decS a g D u ℓ) (Y / shrinkJ a) 6) (layoutOf D u ℓ)
      (Y % shrinkJ a) = some p ∧ PanelMatch D u (ℓ + 1) Y p

/-- The decoded data are the true data when the stored numbers are the codes of the true data. -/
theorem decS_eq (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y) :
    decS a g D u ℓ = shrinkOld B X s := by
  funext α
  by_cases hα : α < Fintype.card X.Base
  · obtain ⟨y, rfl⟩ := exists_addr_eq X hα
    rw [shrinkOld_addr]
    unfold decS
    rw [if_pos (by rw [hN]; exact hα), decPanel_of_match (hP y), hcol y, finOf_val, hoff y, bwOf_bwNum, hterm y]
    rfl
  · have h1 : decS a g D u ℓ α = none := by
      unfold decS
      rw [if_neg (by rw [hN]; exact hα)]
    have h2 : shrinkOld B X s α = none := by
      unfold shrinkOld
      rw [baseAt_eq_none.mpr (not_lt.mp hα)]
      rfl
    rw [h1, h2]

theorem layoutOf_eq (D : Dims) (u : List Bool) (ℓ : ℕ) {L : Bool} (h : rdLayout D u ℓ = if L then 1 else 0) :
    layoutOf D u ℓ = L := by
  unfold layoutOf
  rw [h]
  cases L <;> decide

/-- **C10 on the bits, stage form (shrink).** -/
theorem C10sU_stage (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hcol : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ))
    (hoff : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hterm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hlay : rdLayout D u ℓ = if layoutBit B X s then 1 else 0) :
    (∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sU (g := g) B ready D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) := by
  have hd := decS_eq B D u ℓ X s hN hP hcol hoff hterm
  have hl := layoutOf_eq D u ℓ hlay
  have key : ∀ y, C10sU (g := g) B ready D u ℓ (addr (X.shrinkNext B ready s) y) ↔
      PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y) (panel (X.shrinkNext B ready s) y) := by
    intro y
    have ht := C10_true_shrink B ready X s (addr (X.shrinkNext B ready s) y) (addr_lt _ y)
    unfold C10 at ht
    rw [panelsOf_addr] at ht
    unfold C10sU
    rw [hd, hl, ← ht]
    constructor
    · rintro ⟨p, hp, hm⟩
      rw [Option.some.inj hp]
      exact hm
    · intro hm
      exact ⟨_, rfl, hm⟩
  constructor
  · intro h y
    exact (key y).mp (h _ (addr_lt _ y))
  · intro h Y hY
    obtain ⟨y, rfl⟩ := exists_addr_eq _ hY
    exact (key y).mpr (h y)

end Shrink

/-! ## Refresh substep -/

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

variable (a g dH) in
/-- The decoded level-`ℓ` data of a refresh substep by address. -/
def decR (D : Dims) (u : List Bool) (ℓ : ℕ) : ℕ → Option (RefreshDatum a g dH) :=
  fun α => if α < (D.lv ℓ).bases then
    some (decPanel D u ℓ α a (a + g),
      fun l jh => rdTerms D u ℓ α (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)))
  else none

/-- **Check C10 on the bits, refresh substep `ℓ → ℓ + 1`** (no layout bit is read). -/
def C10rU (D : Dims) (u : List Bool) (ℓ Y : ℕ) : Prop :=
  ∃ p, recompRefresh (g := g) P hdH hconn F hD hd (Y / 2 ^ a)
      (ballMap (nbOf refreshNbrs (decR a g dH D u ℓ)) (decR a g dH D u ℓ) (Y / 2 ^ a) 1) false
      (Y % 2 ^ a) = some p ∧ PanelMatch D u (ℓ + 1) Y p

theorem decR_eq (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    decR a g dH D u ℓ = refreshOld P hdH hconn F X c := by
  funext α
  by_cases hα : α < Fintype.card X.Base
  · obtain ⟨y, rfl⟩ := exists_addr_eq X hα
    rw [refreshOld_addr]
    unfold decR
    rw [if_pos (by rw [hN]; exact hα), decPanel_of_match (hP y)]
    refine congrArg some (Prod.ext rfl ?_)
    funext l jh
    exact hterm y l jh
  · have h1 : decR a g dH D u ℓ α = none := by
      unfold decR
      rw [if_neg (by rw [hN]; exact hα)]
    have h2 : refreshOld P hdH hconn F X c α = none := by
      unfold refreshOld
      rw [baseAt_eq_none.mpr (not_lt.mp hα)]
      rfl
    rw [h1, h2]

/-- **C10 on the bits, stage form (refresh).** -/
theorem C10rU_stage (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
    (c : DyadicRefreshChoice X P hdH hconn F)
    (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hP : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hterm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) :
    (∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base, C10rU (g := g) P hdH hconn F hD hd D u ℓ Y) ↔
      ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
  have hdr := decR_eq P hdH hconn F D u ℓ X c hN hP hterm
  have key : ∀ y, C10rU (g := g) P hdH hconn F hD hd D u ℓ (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y) ↔
      PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
        (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y) := by
    intro y
    have ht := C10_true_refresh P hdH hconn F hD hd X c false (addr _ y) (addr_lt _ y)
    unfold C10 at ht
    rw [panelsOf_addr] at ht
    unfold C10rU
    rw [hdr, ← ht]
    constructor
    · rintro ⟨p, hp, hm⟩
      rw [Option.some.inj hp]
      exact hm
    · intro hm
      exact ⟨_, rfl, hm⟩
  constructor
  · intro h y
    exact (key y).mp (h _ (addr_lt _ y))
  · intro h Y hY
    obtain ⟨y, rfl⟩ := exists_addr_eq _ hY
    exact (key y).mpr (h y)

end Refresh

end P1ChkFinal
