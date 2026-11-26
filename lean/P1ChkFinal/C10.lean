import P1ChkFinal.Ball
import P1P7.ShrinkPanel
import P1P7.RefreshLocal

/-!
# P1, wave 2, check C10 (lane P1-lean-W2-chkfinal)

Paper `research/papers/ntime-dtime-polylog.tex` l.1052: "(one per base X of each level l+1 <= Lambda) The panel entries
(P1), (P2) of X equal the values computed by Lemma locality from the level-l panels of Ball_l(parent(X), 6) and the
layout bit."

* `C10`: the check, on STORED data only. The verifier walks the ball by the stored neighbour addresses (`bfs`,
  rem:G1) and passes the stored data of the ball, keyed by address, to a recomputation function `recomp`.
* Shrinking substep: `recompShrink`, the canonical recomputation, is well defined by P7's congruence lemma
  `P1P7.shrink_panel_local'` (radius 6, PROVED by P1-lean-P7shrink) and the ball lemma `mem_bfs_iff`.
  `C10_true_shrink`: the true data pass C10 at every base of the next level.
  `C10_unique_shrink`: if the level-l data and the layout bit are the true ones and C10 holds at every base of level
  l+1, the stored level-(l+1) panels are the true ones.
* Refresh substep: the same with `P1P7.refresh_panel_local'` (radius 1, block terms at the parent).

Lean key (PLAN.md section 9, 10:15Z): the true panels are OpenAI's own `shrinkNext` / `dyadicRefreshNext` panels, so
slot numbers follow OpenAI's lane-0 mixed-radix key; the term data are P7's `choiceAt`, keyed at the wire's source
base (the Lean convention).
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
open P1P7

/-! ## The check (stored data only) -/

/-- **Check C10** at the base with address `Y` of level `ℓ+1`: the stored panel `new Y` equals the panel recomputed
by `recomp` from the parent address `Y / J`, the stored level-`ℓ` data of the ball of radius `ρ` around the parent
(walked by the stored neighbour addresses, decoded by `nbrsOf`), the stored layout bit `lay`, and the child index
`Y % J`. Product addresses (rem:G1): the children of the base with address `x` have the addresses `J x + j`,
`j < J`. `none` stands for "not decodable / not an address". -/
def C10 {Δ Pan : Type*} (nbrsOf : Δ → List ℕ) (ρ J : ℕ)
    (recomp : ℕ → (ℕ → Option Δ) → Bool → ℕ → Option Pan)
    (old : ℕ → Option Δ) (new : ℕ → Option Pan) (lay : Bool) (Y : ℕ) : Prop :=
  new Y = recomp (Y / J) (ballMap (nbOf nbrsOf old) old (Y / J) ρ) lay (Y % J)

/-! ## Panels by address -/

/-- The type of a panel (P1)+(P2), i.e. of `P1P7.panel X y`, for a state of degree exponent `a`, `g` lane bits. -/
abbrev PanelT (a g : ℕ) : Type :=
  (Fin (2 ^ a) → ℕ × BitWord g) × (Fin (2 ^ a) → ℕ) × (Fin (2 ^ a) → ℕ × BitWord g) × (Fin (2 ^ a) → ℕ) ×
    (Fin (2 ^ a) → BitWord g → ℕ)

/-- The neighbour addresses listed in a panel: heads of the out-slots, then tails of the in-slots. -/
def panelNbrs {a g : ℕ} (p : PanelT a g) : List ℕ :=
  List.ofFn (fun k => (p.1 k).1) ++ List.ofFn (fun k => (p.2.2.1 k).1)

/-- The true panels of a state, by address (`none` off the address range). -/
def panelsOf {a g : ℕ} (X : State a g) : ℕ → Option (PanelT a g) :=
  fun Y => (baseAt X Y).map (panel X)

theorem panelNbrs_panel {a g : ℕ} (X : State a g) (y : X.Base) : panelNbrs (panel X y) = nbrAddrs X y := rfl

/-- The type of `P1P7.shrinkData`: panel, greedy colour, greedy tag offset, term data (P7's `choiceAt`). -/
abbrev ShrinkDatum (a g : ℕ) : Type :=
  PanelT a (packingLaneBits a g) × Fin (2 * 2 ^ a + 1) × BitWord (packingTagBits (2 ^ a)) ×
    (Fin (2 ^ a) → BitWord (packingTagBits (2 ^ a)) → BitWord g → BitWord (2 * 2 ^ a + 1) → BitWord a →
      Option (Bool × Fin 4 → ℕ))

/-- Neighbour addresses of a shrink datum (from its panel). -/
def shrinkNbrs {a g : ℕ} (d : ShrinkDatum a g) : List ℕ := panelNbrs d.1

/-- Product addresses: `(J x + j) / J = x` and `(J x + j) % J = j` for `j < J`. -/
theorem div_mod_prod {J x j : ℕ} (hj : j < J) : (J * x + j) / J = x ∧ (J * x + j) % J = j := by
  have hJ : 0 < J := lt_of_le_of_lt (Nat.zero_le j) hj
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hJ, Nat.div_eq_of_lt hj, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-! ## Shrinking substep -/

section Shrink

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- The true level-`ℓ` data of a shrinking substep by address: `P1P7.shrinkData` of the base with that address. -/
noncomputable def shrinkOld (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    ℕ → Option (ShrinkDatum a g) :=
  fun α => (baseAt X α).map (shrinkData B X s)

theorem shrinkOld_addr (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (y : X.Base) :
    shrinkOld B X s (addr X y) = some (shrinkData B X s y) := by
  simp [shrinkOld, baseAt_addr]

/-- The neighbour lists that the verifier reads from the true data are the true ones. -/
theorem nbOf_shrinkOld (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    nbOf shrinkNbrs (shrinkOld B X s) = nbrAt X := by
  funext α
  unfold nbOf shrinkOld nbrAt
  cases baseAt X α <;> rfl

variable (a g) in
/-- The instances of the shrink locality statement: a state, a selection, a parent base, a tag. -/
abbrev ShrinkInst :=
  Σ X : State a (packingLaneBits a g), X.ShrinkSelection B × X.Base × BitWord (packingTagBits (2 ^ a))

/-- What C10 passes to the recomputation for the true data of an instance: parent address, ball data of radius 6
(walked by the stored addresses), layout bit, child index (the number of the tag). -/
noncomputable def shrinkKey (i : ShrinkInst a g B) : ℕ × (ℕ → Option (ShrinkDatum a g)) × Bool × ℕ :=
  (addr i.1 i.2.2.1,
    ballMap (nbOf shrinkNbrs (shrinkOld B i.1 i.2.1)) (shrinkOld B i.1 i.2.1) (addr i.1 i.2.2.1) 6,
    layoutBit B i.1 i.2.1, (bitWordFinEquiv (packingTagBits (2 ^ a)) i.2.2.2 : ℕ))

/-- The true child panel of an instance. -/
noncomputable def shrinkOut (i : ShrinkInst a g B) : Option (PanelT b g) :=
  some (panel (i.1.shrinkNext B ready i.2.1) (i.2.2.1, i.2.2.2))

/-- Locality in function form: equal C10 keys give equal child panels (from `P1P7.shrink_panel_local'`). -/
theorem shrinkOut_factors : Function.FactorsThrough (shrinkOut (g := g) B ready) (shrinkKey (g := g) B) := by
  rintro ⟨X, s, x, j⟩ ⟨X', s', x', j'⟩ h
  simp only [shrinkKey, Prod.mk.injEq] at h
  obtain ⟨hx, hball, hlay, hj⟩ := h
  have hjj : j = j' := (bitWordFinEquiv _).injective (Fin.ext hj)
  subst hjj
  simp only [shrinkOut]
  congr 1
  refine shrink_panel_local' B ready X X' s s' x x' hx ?_ hlay j
  intro y y' hyy' hd
  have hmem : addr X y ∈ bfs (nbOf shrinkNbrs (shrinkOld B X s)) (addr X x) 6 := by
    rw [nbOf_shrinkOld]
    exact (mem_bfs_iff X x 6 _).mpr ⟨y, rfl, by exact_mod_cast hd⟩
  have h1 := congrFun hball (addr X y)
  unfold ballMap at h1
  rw [if_pos hmem, shrinkOld_addr] at h1
  by_cases hm' : addr X y ∈ bfs (nbOf shrinkNbrs (shrinkOld B X' s')) (addr X' x') 6
  · rw [if_pos hm', hyy', shrinkOld_addr] at h1
    exact Option.some.inj h1
  · rw [if_neg hm'] at h1
    exact absurd h1 (by simp)

/-- **The canonical recomputation** of a shrinking substep: the child panel of any instance with the given C10 key
(well defined by `shrinkOut_factors`); `none` for keys of no instance. -/
noncomputable def recompShrink (x : ℕ) (D : ℕ → Option (ShrinkDatum a g)) (l : Bool) (j : ℕ) :
    Option (PanelT b g) :=
  Function.extend (shrinkKey (g := g) B) (shrinkOut (g := g) B ready) (fun _ => none) (x, D, l, j)

/-- The number of children of a base in a shrinking substep (`J`). -/
abbrev shrinkJ (a : ℕ) : ℕ := 2 ^ packingTagBits (2 ^ a)

/-- **C10, soundness (shrink).** The true data pass C10 at every base of the next level. -/
theorem C10_true_shrink (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (Y : ℕ)
    (hY : Y < Fintype.card (X.shrinkNext B ready s).Base) :
    C10 shrinkNbrs 6 (shrinkJ a) (recompShrink (g := g) B ready) (shrinkOld B X s) (panelsOf (X.shrinkNext B ready s))
      (layoutBit B X s) Y := by
  obtain ⟨p, rfl⟩ : ∃ p, addr (X.shrinkNext B ready s) p = Y :=
    ⟨(X.shrinkNext B ready s).baseIndex.symm ⟨Y, hY⟩, by simp [addr]⟩
  have hp : panelsOf (X.shrinkNext B ready s) (addr (X.shrinkNext B ready s) p) =
      some (panel (X.shrinkNext B ready s) p) := by
    unfold panelsOf
    rw [baseAt_addr]
    rfl
  unfold C10
  rw [hp]
  obtain ⟨x, j⟩ := p
  have hlt : (bitWordFinEquiv (packingTagBits (2 ^ a)) j : ℕ) < shrinkJ a := (bitWordFinEquiv _ j).isLt
  obtain ⟨hdiv, hmod⟩ := div_mod_prod (x := addr X x) hlt
  rw [shrink_addr B ready X s x j, hdiv, hmod]
  exact ((shrinkOut_factors (g := g) B ready).extend_apply (fun _ => none) ⟨X, s, x, j⟩).symm

/-- **C10, uniqueness (shrink).** If the stored level-`ℓ` data and layout bit are the true ones and C10 holds at
every base of level `ℓ+1`, then every stored level-`ℓ+1` panel is the true one. -/
theorem C10_unique_shrink (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (old : ℕ → Option (ShrinkDatum a g)) (new : ℕ → Option (PanelT b g)) (lay : Bool)
    (hold : old = shrinkOld B X s) (hlay : lay = layoutBit B X s)
    (hC10 : ∀ Y < Fintype.card (X.shrinkNext B ready s).Base,
      C10 shrinkNbrs 6 (shrinkJ a) (recompShrink (g := g) B ready) old new lay Y) :
    ∀ Y < Fintype.card (X.shrinkNext B ready s).Base, new Y = panelsOf (X.shrinkNext B ready s) Y := by
  intro Y hY
  subst hold hlay
  exact (hC10 Y hY).trans (C10_true_shrink B ready X s Y hY).symm

end Shrink

/-! ## Refresh substep -/

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- The level-`ℓ` datum of a base in a refresh substep: its panel and its block terms (one per remaining lane). -/
abbrev RefreshDatum (a g dH : ℕ) : Type :=
  PanelT a (a + g) × (BitWord g → Fin (2 ^ a) × Fin dH → ℕ)

/-- Neighbour addresses of a refresh datum (from its panel). -/
def refreshNbrs {a g dH : ℕ} (d : RefreshDatum a g dH) : List ℕ := panelNbrs d.1

/-- The true level-`ℓ` data of a refresh substep by address. -/
noncomputable def refreshOld (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) :
    ℕ → Option (RefreshDatum a g dH) :=
  fun α => (baseAt X α).map (fun y => (panel X y, fun l => (c (y, l)).val))

theorem refreshOld_addr (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (y : X.Base) :
    refreshOld P hdH hconn F X c (addr X y) = some (panel X y, fun l => (c (y, l)).val) := by
  simp [refreshOld, baseAt_addr]

theorem nbOf_refreshOld (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) :
    nbOf refreshNbrs (refreshOld P hdH hconn F X c) = nbrAt X := by
  funext α
  unfold nbOf refreshOld nbrAt
  cases baseAt X α <;> rfl

variable (a g) in
/-- The instances of the refresh locality statement: a state, a choice of block terms, a parent base, a port. -/
abbrev RefreshInst := Σ X : State a (a + g), DyadicRefreshChoice X P hdH hconn F × X.Base × Fin (2 ^ a)

/-- What C10 passes to the recomputation for the true data of a refresh instance (radius 1). -/
noncomputable def refreshKey (i : RefreshInst a g P hdH hconn F) : ℕ × (ℕ → Option (RefreshDatum a g dH)) × ℕ :=
  (addr i.1 i.2.2.1,
    ballMap (nbOf refreshNbrs (refreshOld P hdH hconn F i.1 i.2.1)) (refreshOld P hdH hconn F i.1 i.2.1)
      (addr i.1 i.2.2.1) 1,
    (i.2.2.2 : ℕ))

/-- The true child panel of a refresh instance. -/
noncomputable def refreshOut (i : RefreshInst a g P hdH hconn F) : Option (PanelT a₀ g) :=
  some (panel (dyadicRefreshNext i.1 P hdH hconn F hD hd i.2.1) (i.2.2.1, i.2.2.2))

/-- Locality in function form for a refresh (from `P1P7.refresh_panel_local'`). -/
theorem refreshOut_factors : Function.FactorsThrough (refreshOut (g := g) P hdH hconn F hD hd) (refreshKey (g := g) P hdH hconn F) := by
  rintro ⟨X, c, x, j⟩ ⟨X', c', x', j'⟩ h
  simp only [refreshKey, Prod.mk.injEq] at h
  obtain ⟨hx, hball, hj⟩ := h
  have hjj : j = j' := Fin.ext hj
  subst hjj
  simp only [refreshOut]
  congr 1
  -- the data at every address of the ball of `x` agree
  have hdata : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 1 →
      (panel X y, fun l => (c (y, l)).val) = (panel X' y', fun l => (c' (y', l)).val) := by
    intro y y' hyy' hd1
    have hmem : addr X y ∈ bfs (nbOf refreshNbrs (refreshOld P hdH hconn F X c)) (addr X x) 1 := by
      rw [nbOf_refreshOld]
      exact (mem_bfs_iff X x 1 _).mpr ⟨y, rfl, by exact_mod_cast hd1⟩
    have h1 := congrFun hball (addr X y)
    unfold ballMap at h1
    rw [if_pos hmem, refreshOld_addr] at h1
    by_cases hm' : addr X y ∈ bfs (nbOf refreshNbrs (refreshOld P hdH hconn F X' c')) (addr X' x') 1
    · rw [if_pos hm', hyy', refreshOld_addr] at h1
      exact Option.some.inj h1
    · rw [if_neg hm'] at h1
      exact absurd h1 (by simp)
  refine refresh_panel_local' P hdH hconn F hD hd X X' c c' x x' hx
    (fun y y' hyy' hd1 => congrArg Prod.fst (hdata y y' hyy' hd1)) ?_ j
  intro l
  have hxx := congrArg Prod.snd (hdata x x' hx (by simp))
  exact congrFun hxx l

/-- **The canonical recomputation** of a refresh substep (the layout bit is not used). -/
noncomputable def recompRefresh (x : ℕ) (D : ℕ → Option (RefreshDatum a g dH)) (_l : Bool) (j : ℕ) :
    Option (PanelT a₀ g) :=
  Function.extend (refreshKey (g := g) P hdH hconn F) (refreshOut (g := g) P hdH hconn F hD hd) (fun _ => none) (x, D, j)

/-- **C10, soundness (refresh).** The true data pass C10 at every base of the next level, for every value of the
(unused) layout bit. -/
theorem C10_true_refresh (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (lay : Bool) (Y : ℕ)
    (hY : Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base) :
    C10 refreshNbrs 1 (2 ^ a) (recompRefresh (g := g) P hdH hconn F hD hd) (refreshOld P hdH hconn F X c)
      (panelsOf (dyadicRefreshNext X P hdH hconn F hD hd c)) lay Y := by
  obtain ⟨p, rfl⟩ : ∃ p, addr (dyadicRefreshNext X P hdH hconn F hD hd c) p = Y :=
    ⟨(dyadicRefreshNext X P hdH hconn F hD hd c).baseIndex.symm ⟨Y, hY⟩, by simp [addr]⟩
  have hp : panelsOf (dyadicRefreshNext X P hdH hconn F hD hd c) (addr (dyadicRefreshNext X P hdH hconn F hD hd c) p) =
      some (panel (dyadicRefreshNext X P hdH hconn F hD hd c) p) := by
    unfold panelsOf
    rw [baseAt_addr]
    rfl
  unfold C10
  rw [hp]
  obtain ⟨x, j⟩ := p
  obtain ⟨hdiv, hmod⟩ := div_mod_prod (x := addr X x) j.isLt
  rw [refresh_addr P hdH hconn F hD hd X c x j, hdiv, hmod]
  exact ((refreshOut_factors (g := g) P hdH hconn F hD hd).extend_apply (fun _ => none) ⟨X, c, x, j⟩).symm

/-- **C10, uniqueness (refresh).** -/
theorem C10_unique_refresh (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F)
    (old : ℕ → Option (RefreshDatum a g dH)) (new : ℕ → Option (PanelT a₀ g)) (lay : Bool)
    (hold : old = refreshOld P hdH hconn F X c)
    (hC10 : ∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base,
      C10 refreshNbrs 1 (2 ^ a) (recompRefresh (g := g) P hdH hconn F hD hd) old new lay Y) :
    ∀ Y < Fintype.card (dyadicRefreshNext X P hdH hconn F hD hd c).Base,
      new Y = panelsOf (dyadicRefreshNext X P hdH hconn F hD hd c) Y := by
  intro Y hY
  subst hold
  exact (hC10 Y hY).trans (C10_true_refresh P hdH hconn F hD hd X c lay Y hY).symm

end Refresh

end P1ChkFinal
