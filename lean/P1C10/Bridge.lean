import P1C10.Targets

/-!
# P1, check C10: from a recomputation on CODES to the recomputation `rc` of decision D10 (lane P1-lean-c10)

* `bfs_ballMap`, `ballList_ballMap`: the ball list read from the ball data `ballMap ..` (all that check C10 passes
  on) is the ball list of the stored data.
* `uncodePanel`: the panel with a given code (`none` if the list is not the code of a panel).
* `refreshRcOf a₀ g rcC`, `shrinkRcOf b g rcC`: the D10 recomputation on panels made from a recomputation on codes.
* `refreshRcOK_of_code`, `shrinkRcOK_of_code`: if `rcC` is right on the codes of true data (`RefreshCodeOK`,
  `ShrinkCodeOK`, the prover's targets), these satisfy D10's `hrc` (`RefreshRcOK`, `ShrinkRcOK`) for every `g`.
* `refresh_stage_of_program`, `shrink_stage_of_program`: so a proof of `RefreshProgram` / `ShrinkProgram` gives a
  recomputation on codes for which the stage lemmas hold with NO hypothesis on `rc` left.
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
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-! ## The ball list of the ball data -/

theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem mem_bfs_mono {nb : ℕ → List ℕ} {x y r ρ : ℕ} (h : r ≤ ρ) (hy : y ∈ bfs nb x r) : y ∈ bfs nb x ρ := by
  induction h with
  | refl => exact hy
  | step _ ih => exact mem_bfs_succ.mpr (Or.inl ih)

theorem ballMap_of_mem {Δ : Type*} {nb : ℕ → List ℕ} {old : ℕ → Option Δ} {x ρ y : ℕ}
    (hy : y ∈ bfs nb x ρ) : ballMap nb old x ρ y = old y :=
  if_pos hy

/-- Walking by the neighbour lists of the ball data gives the same list as walking by the stored data. -/
theorem bfs_ballMap {Δ : Type*} (f : Δ → List ℕ) (old : ℕ → Option Δ) (x ρ : ℕ) :
    ∀ r, r ≤ ρ → bfs (nbOf f (ballMap (nbOf f old) old x ρ)) x r = bfs (nbOf f old) x r
  | 0, _ => rfl
  | r + 1, h => by
    have ih := bfs_ballMap f old x ρ r (Nat.le_of_succ_le h)
    simp only [bfs]
    rw [ih]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    have hy' : y ∈ bfs (nbOf f old) x ρ := mem_bfs_mono (Nat.le_of_succ_le h) hy
    show (ballMap (nbOf f old) old x ρ y).elim [] f = (old y).elim [] f
    rw [ballMap_of_mem hy']

theorem ballList_ballMap {Δ : Type} {T : Type} (f : Δ → List ℕ) (old : ℕ → Option Δ) (code : Δ → T)
    (x ρ : ℕ) :
    ballList (nbOf f (ballMap (nbOf f old) old x ρ))
        (fun y => (ballMap (nbOf f old) old x ρ y).map code) x ρ =
      ballList (nbOf f old) (fun y => (old y).map code) x ρ := by
  unfold ballList
  rw [bfs_ballMap f old x ρ ρ (le_refl _)]
  apply List.map_congr_left
  intro y hy
  show (y, (ballMap (nbOf f old) old x ρ y).map code) = (y, (old y).map code)
  rw [ballMap_of_mem hy]

/-! ## Panels from codes -/

open Classical in
/-- The panel whose code is `c` (`none` if `c` is not the code of a panel of this shape). -/
noncomputable def uncodePanel (a g : ℕ) (c : PanelCode) : Option (PanelT a g) :=
  if h : ∃ p : PanelT a g, codePanel p = c then some (Classical.choose h) else none

theorem uncodePanel_code {a g : ℕ} (p : PanelT a g) : uncodePanel a g (codePanel p) = some p := by
  have h : ∃ q : PanelT a g, codePanel q = codePanel p := ⟨p, rfl⟩
  unfold uncodePanel
  rw [dif_pos h]
  exact congrArg some (codePanel_injective (Classical.choose_spec h))

theorem uncodePanel_eq_some {a g : ℕ} {c : PanelCode} {p : PanelT a g} :
    uncodePanel a g c = some p ↔ codePanel p = c := by
  constructor
  · intro h
    by_cases hex : ∃ q : PanelT a g, codePanel q = c
    · obtain ⟨q, rfl⟩ := hex
      rw [uncodePanel_code] at h
      rw [Option.some.inj h]
    · unfold uncodePanel at h
      rw [dif_neg hex] at h
      exact (Option.some_ne_none p h.symm).elim
  · rintro rfl
    exact uncodePanel_code p

/-! ## Shrinking substep -/

/-- The D10 recomputation of a shrinking substep made from a recomputation on codes. -/
noncomputable def shrinkRcOf {a : ℕ} (b g : ℕ) (rcC : ShrinkIn → Option PanelCode) : ShrinkRc a b g :=
  fun x Dt l j =>
    (rcC (((x, ballList (nbOf shrinkNbrs Dt) (fun y => (Dt y).map codeShrinkDatum) x 6), l), j)).bind
      (uncodePanel b g)

section Shrink

variable {a b : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

theorem shrinkRcOf_true {rcC : ShrinkIn → Option PanelCode} (h : ShrinkCodeOK B ready rcC) (g : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    ShrinkRcAt B ready (shrinkRcOf b g rcC) X s := by
  intro x j
  unfold shrinkRcOf
  rw [ballList_ballMap shrinkNbrs (shrinkOld B X s) codeShrinkDatum (addr X x) 6, nbOf_shrinkOld B X s,
    h g X s x j]
  exact uncodePanel_code _

/-- A recomputation that is right on codes gives D10's `hrc` for every `g`. -/
theorem shrinkRcOK_of_code {rcC : ShrinkIn → Option PanelCode} (h : ShrinkCodeOK B ready rcC) (g : ℕ) :
    ShrinkRcOK B ready (shrinkRcOf (a := a) b g rcC) :=
  fun ⟨X, s, x, j⟩ => shrinkRcOf_true B ready h g X s x j

/-- From the program target: the stage lemma of a shrinking substep with no hypothesis on `rc` left. -/
theorem shrink_stage_of_program (hprog : ShrinkProgram B ready) :
    ∃ rcC : ShrinkIn → Option PanelCode, Poly rcC ∧
      ∀ (g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
        (s : X.ShrinkSelection B),
        (D.lv ℓ).bases = Fintype.card X.Base →
        (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) →
        (∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ)) →
        (∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y)) →
        (∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y) →
        (rdLayout D u ℓ = if layoutBit B X s then 1 else 0) →
        ((∀ Y < Fintype.card (X.shrinkNext B ready s).Base, C10sRc (shrinkRcOf (a := a) b g rcC) D u ℓ Y) ↔
          ∀ y, PanelMatch D u (ℓ + 1) (addr (X.shrinkNext B ready s) y)
            (panel (X.shrinkNext B ready s) y)) := by
  obtain ⟨rcC, hpoly, hok⟩ := hprog
  refine ⟨rcC, hpoly, ?_⟩
  intro g D u ℓ X s hN hP hcol hoff hterm hlay
  exact C10sRc_stage B ready _ D u ℓ X s (shrinkRcOf_true B ready hok g X s) hN hP hcol hoff hterm hlay

end Shrink

/-! ## Refresh substep -/

/-- The D10 recomputation of a refresh substep made from a recomputation on codes. -/
noncomputable def refreshRcOf {a dH : ℕ} (a₀ g : ℕ) (rcC : RefreshIn → Option PanelCode) :
    RefreshRc a a₀ g dH :=
  fun x Dt j =>
    (rcC ((x, ballList (nbOf refreshNbrs Dt) (fun y => (Dt y).map codeRefreshDatum) x 1), j)).bind
      (uncodePanel a₀ g)

section Refresh

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

theorem refreshRcOf_true {rcC : RefreshIn → Option PanelCode} (h : RefreshCodeOK P hdH hconn F hD hd rcC)
    (g : ℕ) (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) :
    RefreshRcAt P hdH hconn F hD hd (refreshRcOf a₀ g rcC) X c := by
  intro x j
  unfold refreshRcOf
  rw [ballList_ballMap refreshNbrs (refreshOld P hdH hconn F X c) codeRefreshDatum (addr X x) 1,
    nbOf_refreshOld P hdH hconn F X c, h g X c x j]
  exact uncodePanel_code _

/-- A recomputation that is right on codes gives D10's `hrc` for every `g`. -/
theorem refreshRcOK_of_code {rcC : RefreshIn → Option PanelCode} (h : RefreshCodeOK P hdH hconn F hD hd rcC)
    (g : ℕ) : RefreshRcOK P hdH hconn F hD hd (refreshRcOf (a := a) (dH := dH) a₀ g rcC) :=
  fun ⟨X, c, x, j⟩ => refreshRcOf_true P hdH hconn F hD hd h g X c x j

/-- From the program target: the stage lemma of a refresh substep with no hypothesis on `rc` left. -/
theorem refresh_stage_of_program (hprog : RefreshProgram P hdH hconn F hD hd) :
    ∃ rcC : RefreshIn → Option PanelCode, Poly rcC ∧
      ∀ (g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (a + g))
        (c : DyadicRefreshChoice X P hdH hconn F),
        (D.lv ℓ).bases = Fintype.card X.Base →
        (∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) →
        (∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
          rdTerms D u ℓ (addr X y) (bwNum l) (1 + ((jh.1 : ℕ) * dH + jh.2)) = (c (y, l)).val jh) →
        ((∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base,
            C10rRc (refreshRcOf (a := a) (dH := dH) a₀ g rcC) D u ℓ Y) ↔
          ∀ y, PanelMatch D u (ℓ + 1) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) y)
            (panel (dyadicRefreshNext X P hdH hconn F hD hd c) y)) := by
  obtain ⟨rcC, hpoly, hok⟩ := hprog
  refine ⟨rcC, hpoly, ?_⟩
  intro g D u ℓ X c hN hP hterm
  exact C10rRc_stage P hdH hconn F hD hd _ D u ℓ X c (refreshRcOf_true P hdH hconn F hD hd hok g X c) hN hP hterm

end Refresh

end P1C10
