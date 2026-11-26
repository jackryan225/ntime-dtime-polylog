import Mathlib

/-!
# The looping colouring (lane P1-lean-benes, PLAN.md task P2)

`X` is a finite linearly ordered set (the item labels). `σ` pairs the two items of an input switch,
`τ` the two items of an output switch; both are involutions without fixed points. In the graph whose
vertices are the switches and whose edges are the items, every vertex has degree 2, so the graph is a
union of even cycles. The item set of the cycle of `x` is `orbit x ∪ orbit (σ x)`, where `orbit` is the
orbit of `ρ = τ ∘ σ` (one step along the cycle). A colouring that alternates along every cycle is a
`c : X → Bool` with `c (σ x) = !c x` and `c (τ x) = !c x`.

`colour σ τ` is the canonical one: the least label of every cycle gets the colour `false`
(`colour_least`), and it is the only alternating colouring with this property (`colour_unique`).
-/

namespace P1Benes
namespace Loop

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]

/-- `ρ = τ ∘ σ`: one step along a cycle (input partner, then output partner). -/
def rho (σ τ : Perm X) : Perm X := σ.trans τ

@[simp] theorem rho_apply (σ τ : Perm X) (x : X) : rho σ τ x = τ (σ x) := rfl

/-- The `ρ`-orbit of `y`. -/
def orbit (ρ : Perm X) (y : X) : Finset X := Finset.univ.filter fun z => ρ.SameCycle y z

theorem mem_orbit {ρ : Perm X} {y z : X} : z ∈ orbit ρ y ↔ ρ.SameCycle y z := by
  simp [orbit]

theorem orbit_nonempty (ρ : Perm X) (y : X) : (orbit ρ y).Nonempty :=
  ⟨y, mem_orbit.2 (SameCycle.refl _ _)⟩

/-- The least label in the `ρ`-orbit of `y`. -/
def orbMin (ρ : Perm X) (y : X) : X := (orbit ρ y).min' (orbit_nonempty ρ y)

theorem sameCycle_orbMin (ρ : Perm X) (y : X) : ρ.SameCycle y (orbMin ρ y) :=
  mem_orbit.1 (Finset.min'_mem _ _)

theorem orbMin_le {ρ : Perm X} {y z : X} (h : ρ.SameCycle y z) : orbMin ρ y ≤ z :=
  Finset.min'_le _ _ (mem_orbit.2 h)

theorem orbMin_eq {ρ : Perm X} {y y' : X} (h : ρ.SameCycle y y') : orbMin ρ y = orbMin ρ y' :=
  le_antisymm (orbMin_le (h.trans (sameCycle_orbMin ρ y')))
    (orbMin_le (h.symm.trans (sameCycle_orbMin ρ y)))

/-- The canonical colour: `false` iff the least label of the cycle of `x` lies in the `ρ`-orbit
of `x` (the two orbits of a cycle are `orbit x` and `orbit (σ x)`). -/
def colour (σ τ : Perm X) (x : X) : Bool :=
  decide (orbMin (rho σ τ) (σ x) < orbMin (rho σ τ) x)

/-- `σ ∘ ρ^a = ρ^(-a) ∘ σ`. -/
theorem sigma_zpow (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (a : ℤ)
    (y : X) : σ ((rho σ τ ^ a) y) = (rho σ τ ^ (-a)) (σ y) := by
  have hσσ : σ * σ = 1 := Equiv.ext fun x => by simp [Perm.mul_apply, hσ]
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hconj : σ * rho σ τ * σ⁻¹ = (rho σ τ)⁻¹ := by
    rw [hσi]
    ext x
    rw [eq_comm, Perm.inv_eq_iff_eq]
    simp [Perm.mul_apply, hσ, hτ]
  have hza : σ * rho σ τ ^ a * σ⁻¹ = rho σ τ ^ (-a) := by
    rw [← conj_zpow, hconj, inv_zpow']
  have hzb : σ * rho σ τ ^ a = rho σ τ ^ (-a) * σ := by
    rw [← hza, hσi, mul_assoc, hσσ, mul_one]
  have := congrArg (fun f : Perm X => f y) hzb
  simpa [Perm.mul_apply] using this

/-- The two `ρ`-orbits of a cycle are different. -/
theorem not_sameCycle (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (x : X) : ¬ (rho σ τ).SameCycle x (σ x) := by
  rintro ⟨i, hi⟩
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' i
  · apply hσ' ((rho σ τ ^ a) x)
    rw [sigma_zpow σ τ hσ hτ, ← hi, ← Perm.mul_apply, ← zpow_add,
      show -a + 2 * a = a by ring]
  · apply hτ' (σ ((rho σ τ ^ a) x))
    have e1 : τ (σ ((rho σ τ ^ a) x)) = (rho σ τ ^ (1 + a)) x := by
      rw [zpow_one_add, Perm.mul_apply, rho_apply]
    rw [e1, sigma_zpow σ τ hσ hτ, ← hi, ← Perm.mul_apply, ← zpow_add,
      show -a + (2 * a + 1) = 1 + a by ring]

theorem orbMin_sigma_ne (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (x : X) :
    orbMin (rho σ τ) (σ x) ≠ orbMin (rho σ τ) x := by
  intro h
  apply not_sameCycle σ τ hσ hτ hσ' hτ' x
  have h1 := sameCycle_orbMin (rho σ τ) x
  have h2 := sameCycle_orbMin (rho σ τ) (σ x)
  rw [h] at h2
  exact h1.trans h2.symm

/-- The colour alternates at every input switch. -/
theorem colour_sigma (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (x : X) :
    colour σ τ (σ x) = !colour σ τ x := by
  unfold colour
  rw [hσ x]
  rcases lt_or_gt_of_ne (orbMin_sigma_ne σ τ hσ hτ hσ' hτ' x) with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

/-- The colour alternates at every output switch. -/
theorem colour_tau (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (x : X) :
    colour σ τ (τ x) = !colour σ τ x := by
  have e1 : orbMin (rho σ τ) (τ x) = orbMin (rho σ τ) (σ x) := by
    apply orbMin_eq
    refine ⟨-1, ?_⟩
    rw [zpow_neg, zpow_one, Perm.inv_eq_iff_eq, rho_apply, hσ]
  have e2 : orbMin (rho σ τ) (σ (τ x)) = orbMin (rho σ τ) x := by
    apply orbMin_eq
    refine ⟨1, ?_⟩
    rw [zpow_one, rho_apply, hσ, hτ]
  have := colour_sigma σ τ hσ hτ hσ' hτ' x
  unfold colour at this ⊢
  rw [hσ x] at this
  rw [e1, e2, this]

/-- The least label of every cycle gets the colour `false` ("first colour"). -/
theorem colour_least (σ τ : Perm X) (x : X)
    (hx : ∀ y, (rho σ τ).SameCycle x y ∨ (rho σ τ).SameCycle (σ x) y → x ≤ y) :
    colour σ τ x = false := by
  unfold colour
  have h1 : orbMin (rho σ τ) x = x :=
    le_antisymm (orbMin_le (SameCycle.refl _ _)) (hx _ (Or.inl (sameCycle_orbMin _ x)))
  have h2 : x ≤ orbMin (rho σ τ) (σ x) := hx _ (Or.inr (sameCycle_orbMin _ _))
  rw [h1]
  simp [not_lt.2 h2]

/-- An alternating colouring is constant on `ρ`-orbits. -/
theorem const_of_alternating (σ τ : Perm X) (c : X → Bool) (h1 : ∀ x, c (σ x) = !c x)
    (h2 : ∀ x, c (τ x) = !c x) {x y : X} (hxy : (rho σ τ).SameCycle x y) : c x = c y := by
  have step : ∀ z, c (rho σ τ z) = c z := fun z => by simp [h1, h2]
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction i with
  | zero => simp
  | succ k ih => rw [ih, pow_succ', Perm.mul_apply, step]

theorem sameCycle_sigma (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    {x y : X} (h : (rho σ τ).SameCycle x y) : (rho σ τ).SameCycle (σ x) (σ y) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨-i, (sigma_zpow σ τ hσ hτ i x).symm⟩

/-- The least label of the cycle of `x` (the cycle is `orbit x ∪ orbit (σ x)`). -/
def cycMin (σ τ : Perm X) (x : X) : X := min (orbMin (rho σ τ) x) (orbMin (rho σ τ) (σ x))

theorem cycMin_le (σ τ : Perm X) {x y : X}
    (h : (rho σ τ).SameCycle x y ∨ (rho σ τ).SameCycle (σ x) y) : cycMin σ τ x ≤ y := by
  rcases h with h | h
  · exact (min_le_left _ _).trans (orbMin_le h)
  · exact (min_le_right _ _).trans (orbMin_le h)

theorem cycMin_mem (σ τ : Perm X) (x : X) :
    (rho σ τ).SameCycle x (cycMin σ τ x) ∨ (rho σ τ).SameCycle (σ x) (cycMin σ τ x) := by
  unfold cycMin
  rcases le_total (orbMin (rho σ τ) x) (orbMin (rho σ τ) (σ x)) with h | h
  · rw [min_eq_left h]; exact Or.inl (sameCycle_orbMin _ _)
  · rw [min_eq_right h]; exact Or.inr (sameCycle_orbMin _ _)

/-- `cycMin σ τ x` is the least label of its own cycle. -/
theorem cycMin_least (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (x : X) :
    ∀ y, (rho σ τ).SameCycle (cycMin σ τ x) y ∨ (rho σ τ).SameCycle (σ (cycMin σ τ x)) y →
      cycMin σ τ x ≤ y := by
  intro y hy
  apply cycMin_le
  rcases cycMin_mem σ τ x with hm | hm
  · rcases hy with hy | hy
    · exact Or.inl (hm.trans hy)
    · exact Or.inr ((sameCycle_sigma σ τ hσ hτ hm).trans hy)
  · rcases hy with hy | hy
    · exact Or.inr (hm.trans hy)
    · have := (sameCycle_sigma σ τ hσ hτ hm).trans hy
      rw [hσ] at this
      exact Or.inl this

/-- Every alternating colouring that colours the least label of each cycle `false` is given by
the position of that least label. -/
theorem eval_alternating (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (d : X → Bool) (d1 : ∀ x, d (σ x) = !d x)
    (d2 : ∀ x, d (τ x) = !d x)
    (d3 : ∀ x, (∀ y, (rho σ τ).SameCycle x y ∨ (rho σ τ).SameCycle (σ x) y → x ≤ y) →
      d x = false) (x : X) :
    d x = decide ((rho σ τ).SameCycle (σ x) (cycMin σ τ x)) := by
  have hdm : d (cycMin σ τ x) = false := d3 _ (cycMin_least σ τ hσ hτ x)
  rcases cycMin_mem σ τ x with hm | hm
  · have hn : ¬ (rho σ τ).SameCycle (σ x) (cycMin σ τ x) := fun h =>
      not_sameCycle σ τ hσ hτ hσ' hτ' x (hm.trans h.symm)
    rw [const_of_alternating σ τ d d1 d2 hm, hdm]
    simp [hn]
  · have h1 := const_of_alternating σ τ d d1 d2 hm
    rw [hdm, d1] at h1
    simp only [Bool.not_eq_false'] at h1
    simp [hm, h1]

/-- Uniqueness: `colour σ τ` is the only alternating colouring that gives the least label of every
cycle the colour `false`. So `colour` is exactly the canonical looping rule. -/
theorem colour_unique (σ τ : Perm X) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ' : ∀ x, σ x ≠ x) (hτ' : ∀ x, τ x ≠ x) (c : X → Bool) (h1 : ∀ x, c (σ x) = !c x)
    (h2 : ∀ x, c (τ x) = !c x)
    (h3 : ∀ x, (∀ y, (rho σ τ).SameCycle x y ∨ (rho σ τ).SameCycle (σ x) y → x ≤ y) →
      c x = false) :
    c = colour σ τ := by
  funext x
  rw [eval_alternating σ τ hσ hτ hσ' hτ' c h1 h2 h3 x,
    eval_alternating σ τ hσ hτ hσ' hτ' (colour σ τ) (colour_sigma σ τ hσ hτ hσ' hτ')
      (colour_tau σ τ hσ hτ hσ' hτ') (colour_least σ τ) x]

end Loop
end P1Benes
