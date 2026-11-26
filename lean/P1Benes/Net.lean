import P1Benes.Loop

/-!
# The Beneš network on `2^(n+1)` items and its canonical settings (lane P1-lean-benes)

Addresses are `Fin (2^(n+1))`; the label of an item is its address (a natural number).
`splitLow n x = (x % 2 = 1, x / 2)` splits off the lowest bit.

Recursive form. `Settings 0` is one switch (2 items). `Settings (n+1)` is a first stage on the lowest
bit (`first l` = setting of the switch of the pair `{2l, 2l+1}`), two inner networks `inner false`,
`inner true` on the other `n+1` bits (the inner network `b` carries the items whose lowest bit is `b`
after the first stage), and a last stage on the lowest bit. `routeRec s` is the permutation realized.

Canonical settings (`settings n π`, the looping rule). The items are the edges of the graph whose
vertices are the input switches and the output switches; the canonical colouring of
`Loop.colour` alternates along every cycle and gives the least label of each cycle colour `false`
(`P1Benes.Loop.colour_unique`). An item of colour `b` goes through the inner network `b`; recursion on
the two induced permutations of the halves. Theorem `routeRec_settings : routeRec (settings n π) = π`.

Flat form (paper network (d), butterfly form). Stage `κ = 0, …, 2n` switches the address bit
`stageBit n κ` (`0, 1, …, n, …, 1, 0`); `cross s κ a` is the setting of the switch of stage `κ` that
contains the address `a` (`true` = cross: `a ↦ flipBit n (stageBit n κ) a`). `flatRoute s` is the
composition of the stages `0, 1, …, 2n` in this order, and `flatRoute s = routeRec s`.
-/

namespace P1Benes
namespace Net

open Equiv Equiv.Perm

/-- Split off the lowest address bit: `x ↦ (x % 2 = 1, x / 2)`; inverse `(b, l) ↦ 2 l + b`. -/
def splitLow (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Bool × Fin (2 ^ n) where
  toFun x := (decide (x.val % 2 = 1), ⟨x.val / 2, by
    have h : x.val < 2 ^ n * 2 := lt_of_lt_of_eq x.isLt (pow_succ 2 n); omega⟩)
  invFun p := ⟨2 * p.2.val + (if p.1 then 1 else 0), by
    have h := p.2.isLt; rw [pow_succ]; cases p.1 <;> simp <;> omega⟩
  left_inv x := by
    apply Fin.ext
    by_cases h : x.val % 2 = 1 <;> simp [h] <;> omega
  right_inv p := by
    obtain ⟨b, l⟩ := p
    cases b <;> simp [Prod.ext_iff, Fin.ext_iff] <;> omega

theorem splitLow_val_fst (n : ℕ) (x : Fin (2 ^ (n + 1))) :
    (splitLow n x).1 = decide (x.val % 2 = 1) := rfl

theorem splitLow_val_snd (n : ℕ) (x : Fin (2 ^ (n + 1))) :
    ((splitLow n x).2 : ℕ) = x.val / 2 := rfl

theorem splitLow_symm_val (n : ℕ) (p : Bool × Fin (2 ^ n)) :
    (((splitLow n).symm p : Fin (2 ^ (n + 1))) : ℕ) = 2 * p.2.val + (if p.1 then 1 else 0) := rfl

theorem exists_splitLow (n : ℕ) (x : Fin (2 ^ (n + 1))) : ∃ p, x = (splitLow n).symm p :=
  ⟨splitLow n x, by simp⟩

/-- A switch stage on the lowest bit: the switch of the pair `{2l, 2l+1}` is crossed iff `f l`. -/
def lowStage (n : ℕ) (f : Fin (2 ^ n) → Bool) : Perm (Fin (2 ^ (n + 1))) where
  toFun x := (splitLow n).symm (xor (splitLow n x).1 (f (splitLow n x).2), (splitLow n x).2)
  invFun x := (splitLow n).symm (xor (splitLow n x).1 (f (splitLow n x).2), (splitLow n x).2)
  left_inv x := by simp [Bool.xor_assoc]
  right_inv x := by simp [Bool.xor_assoc]

@[simp] theorem lowStage_apply (n : ℕ) (f : Fin (2 ^ n) → Bool) (b : Bool) (l : Fin (2 ^ n)) :
    lowStage n f ((splitLow n).symm (b, l)) = (splitLow n).symm (xor b (f l), l) := by
  simp [lowStage]

/-- The middle part: the half with lowest bit `b` is routed by `p b` on the other bits. -/
def midStage (n : ℕ) (p : Bool → Perm (Fin (2 ^ n))) : Perm (Fin (2 ^ (n + 1))) where
  toFun x := (splitLow n).symm ((splitLow n x).1, p (splitLow n x).1 (splitLow n x).2)
  invFun x := (splitLow n).symm ((splitLow n x).1, (p (splitLow n x).1).symm (splitLow n x).2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem midStage_apply (n : ℕ) (p : Bool → Perm (Fin (2 ^ n))) (b : Bool)
    (l : Fin (2 ^ n)) : midStage n p ((splitLow n).symm (b, l)) = (splitLow n).symm (b, p b l) := by
  simp [midStage]

/-- Switch settings of the Beneš network on `2^(n+1)` items (`true` = cross). -/
inductive Settings : ℕ → Type
  | leaf (b : Bool) : Settings 0
  | node {n : ℕ} (first : Fin (2 ^ (n + 1)) → Bool) (inner : Bool → Settings n)
      (last : Fin (2 ^ (n + 1)) → Bool) : Settings (n + 1)

/-- The permutation realized by the network (recursive form): item at input address `x` leaves at
output address `routeRec s x`. -/
def routeRec : {n : ℕ} → Settings n → Perm (Fin (2 ^ (n + 1)))
  | _, .leaf b => lowStage 0 fun _ => b
  | _, .node f t g => (lowStage _ f).trans ((midStage _ fun b => routeRec (t b)).trans (lowStage _ g))

/-! ## The looping rule -/

section Step

variable {n : ℕ}

/-- `σ`: the partner at the same input switch (flip the lowest bit). -/
def flip0 (n : ℕ) : Perm (Fin (2 ^ (n + 1))) := lowStage n fun _ => true

/-- `τ`: the partner at the same output switch, `π⁻¹ (flip0 (π x))`. -/
def tau (π : Perm (Fin (2 ^ (n + 1)))) : Perm (Fin (2 ^ (n + 1))) :=
  π.trans ((flip0 n).trans π.symm)

/-- The canonical colour of an item = the inner network that it goes through. -/
def col (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) : Bool :=
  Loop.colour (flip0 n) (tau π) x

/-- First-stage settings: the switch `l` is crossed iff the item `2l` has colour `true`. -/
def firstOf (π : Perm (Fin (2 ^ (n + 1)))) (l : Fin (2 ^ n)) : Bool :=
  col π ((splitLow n).symm (false, l))

/-- Last-stage settings: the switch `l` is crossed iff the item that leaves at `2l` has colour
`true`. -/
def lastOf (π : Perm (Fin (2 ^ (n + 1)))) (l : Fin (2 ^ n)) : Bool :=
  col π (π.symm ((splitLow n).symm (false, l)))

theorem flip0_apply (b : Bool) (l : Fin (2 ^ n)) :
    flip0 n ((splitLow n).symm (b, l)) = (splitLow n).symm (!b, l) := by
  simp [flip0]

theorem flip0_flip0 (x : Fin (2 ^ (n + 1))) : flip0 n (flip0 n x) = x := by
  obtain ⟨⟨b, l⟩, rfl⟩ := exists_splitLow n x
  simp [flip0_apply]

theorem flip0_ne (x : Fin (2 ^ (n + 1))) : flip0 n x ≠ x := by
  obtain ⟨⟨b, l⟩, rfl⟩ := exists_splitLow n x
  rw [flip0_apply]
  intro h
  have := congrArg (fun y => (splitLow n y).1) h
  simp at this

theorem tau_apply (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    tau π x = π.symm (flip0 n (π x)) := rfl

theorem tau_tau (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) : tau π (tau π x) = x := by
  simp [tau_apply, flip0_flip0]

theorem tau_ne (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) : tau π x ≠ x := by
  rw [tau_apply]
  intro h
  apply flip0_ne (π x)
  have := congrArg π h
  simpa using this

theorem col_flip0 (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    col π (flip0 n x) = !col π x :=
  Loop.colour_sigma _ _ flip0_flip0 (tau_tau π) flip0_ne (tau_ne π) x

theorem col_tau (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    col π (tau π x) = !col π x :=
  Loop.colour_tau _ _ flip0_flip0 (tau_tau π) flip0_ne (tau_ne π) x

/-- (L1) the colour of the item `2l + b`. -/
theorem col_splitLow (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) (l : Fin (2 ^ n)) :
    col π ((splitLow n).symm (b, l)) = xor b (firstOf π l) := by
  cases b
  · simp [firstOf]
  · have : (splitLow n).symm (true, l) = flip0 n ((splitLow n).symm (false, l)) := by
      rw [flip0_apply]; rfl
    rw [this, col_flip0]
    simp [firstOf]

/-- (L2) the colour of the item that leaves at `2l + b`. -/
theorem col_symm_splitLow (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) (l : Fin (2 ^ n)) :
    col π (π.symm ((splitLow n).symm (b, l))) = xor b (lastOf π l) := by
  cases b
  · simp [lastOf]
  · have : π.symm ((splitLow n).symm (true, l)) = tau π (π.symm ((splitLow n).symm (false, l))) := by
      rw [tau_apply, Equiv.apply_symm_apply, flip0_apply]; rfl
    rw [this, col_tau]
    simp [lastOf]

/-- The permutation of the half `b` (on the other bits) induced by the colouring. -/
def subFun (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) (l : Fin (2 ^ n)) : Fin (2 ^ n) :=
  (splitLow n (π ((splitLow n).symm (xor (firstOf π l) b, l)))).2

/-- Its inverse. -/
def subInv (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) (l : Fin (2 ^ n)) : Fin (2 ^ n) :=
  (splitLow n (π.symm ((splitLow n).symm (xor (lastOf π l) b, l)))).2

/-- (A) the item at input `x` leaves the inner network `col π x` at the address `(π x) / 2`. -/
theorem subFun_col (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    subFun π (col π x) (splitLow n x).2 = (splitLow n (π x)).2 := by
  obtain ⟨⟨b, l⟩, rfl⟩ := exists_splitLow n x
  rw [col_splitLow]
  simp only [subFun, Equiv.apply_symm_apply]
  congr 4
  cases b <;> cases firstOf π l <;> rfl

/-- (B) the inverse direction. -/
theorem subInv_col (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    subInv π (col π x) (splitLow n (π x)).2 = (splitLow n x).2 := by
  obtain ⟨⟨b, l⟩, hb⟩ := exists_splitLow n (π x)
  have hx : x = π.symm ((splitLow n).symm (b, l)) := by rw [← hb]; simp
  have hc : col π x = xor b (lastOf π l) := by rw [hx, col_symm_splitLow]
  rw [hb, hc]
  simp only [subInv, Equiv.apply_symm_apply]
  rw [hx]
  congr 4
  cases b <;> cases lastOf π l <;> rfl

/-- The induced permutation of the half `b`. -/
def sub (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) : Perm (Fin (2 ^ n)) where
  toFun := subFun π b
  invFun := subInv π b
  left_inv l := by
    have hc : col π ((splitLow n).symm (xor (firstOf π l) b, l)) = b := by
      rw [col_splitLow]; cases b <;> cases firstOf π l <;> rfl
    have h1 := subFun_col π ((splitLow n).symm (xor (firstOf π l) b, l))
    have h2 := subInv_col π ((splitLow n).symm (xor (firstOf π l) b, l))
    rw [hc, Equiv.apply_symm_apply] at h1 h2
    simp only at h1 h2
    rw [h1, h2]
  right_inv l := by
    have hc : col π (π.symm ((splitLow n).symm (xor (lastOf π l) b, l))) = b := by
      rw [col_symm_splitLow]; cases b <;> cases lastOf π l <;> rfl
    have h1 := subFun_col π (π.symm ((splitLow n).symm (xor (lastOf π l) b, l)))
    have h2 := subInv_col π (π.symm ((splitLow n).symm (xor (lastOf π l) b, l)))
    rw [hc, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
    simp only at h1 h2
    rw [h2, h1]

theorem sub_apply (π : Perm (Fin (2 ^ (n + 1)))) (b : Bool) (l : Fin (2 ^ n)) :
    sub π b l = subFun π b l := rfl

end Step

theorem bool_inj {f : Bool → Bool} (hf : Function.Injective f) (c : Bool) : f c = xor c (f false) := by
  cases c
  · simp
  · have : f true ≠ f false := fun h => by have := hf h; simp at this
    cases h1 : f true <;> cases h0 : f false <;> simp_all

/-- The canonical settings (deterministic looping rule) for a permutation `π` of `2^(n+1)` items. -/
def settings : (n : ℕ) → Perm (Fin (2 ^ (n + 1))) → Settings n
  | 0, π => .leaf (splitLow 0 (π ((splitLow 0).symm (false, ⟨0, by simp⟩)))).1
  | n + 1, π => .node (firstOf π) (fun b => settings n (sub π b)) (lastOf π)

/-- Correctness of the looping rule (recursive form). -/
theorem routeRec_settings : ∀ (n : ℕ) (π : Perm (Fin (2 ^ (n + 1)))), routeRec (settings n π) = π
  | 0, π => by
    have hu : ∀ u : Fin (2 ^ 0), u = ⟨0, by simp⟩ := fun u =>
      Fin.ext (by have := u.isLt; simp at this; omega)
    have hy : ∀ y : Fin (2 ^ (0 + 1)), y = (splitLow 0).symm ((splitLow 0 y).1, ⟨0, by simp⟩) := by
      intro y
      rw [← hu (splitLow 0 y).2, Prod.mk.eta, Equiv.symm_apply_apply]
    set f : Bool → Bool := fun c => (splitLow 0 (π ((splitLow 0).symm (c, ⟨0, by simp⟩)))).1 with hf
    have finj : Function.Injective f := by
      intro c c' h
      have e : π ((splitLow 0).symm (c, ⟨0, by simp⟩)) = π ((splitLow 0).symm (c', ⟨0, by simp⟩)) := by
        rw [hy (π ((splitLow 0).symm (c, ⟨0, by simp⟩))),
          hy (π ((splitLow 0).symm (c', ⟨0, by simp⟩)))]
        exact congrArg (fun b => (splitLow 0).symm (b, ⟨0, by simp⟩)) h
      have := congrArg (fun y => (splitLow 0 y).1) (π.injective e)
      simpa using this
    ext1 x
    obtain ⟨⟨c, u⟩, rfl⟩ := exists_splitLow 0 x
    rw [hu u]
    simp only [settings, routeRec, lowStage_apply]
    rw [hy (π ((splitLow 0).symm (c, ⟨0, by simp⟩)))]
    show (splitLow 0).symm (xor c (f false), ⟨0, by simp⟩) = (splitLow 0).symm (f c, ⟨0, by simp⟩)
    rw [bool_inj finj c]
  | n + 1, π => by
    ext1 x
    obtain ⟨⟨b, l⟩, rfl⟩ := exists_splitLow (n + 1) x
    have ih : ∀ c, routeRec (settings n (sub π c)) = sub π c := fun c => routeRec_settings n (sub π c)
    simp only [settings, routeRec, Equiv.trans_apply, lowStage_apply, midStage_apply, ih]
    have hc : xor b (firstOf π l) = col π ((splitLow (n + 1)).symm (b, l)) :=
      (col_splitLow π b l).symm
    rw [hc, sub_apply]
    have hA := subFun_col π ((splitLow (n + 1)).symm (b, l))
    rw [Equiv.apply_symm_apply] at hA
    simp only at hA
    rw [hA]
    obtain ⟨⟨b', l'⟩, hb'⟩ := exists_splitLow (n + 1) (π ((splitLow (n + 1)).symm (b, l)))
    have hcol : col π ((splitLow (n + 1)).symm (b, l)) = xor b' (lastOf π l') := by
      rw [← col_symm_splitLow, ← hb', Equiv.symm_apply_apply]
    rw [hb', Equiv.apply_symm_apply, hcol]
    simp only
    congr 2
    cases b' <;> cases lastOf π l' <;> rfl

/-! ## Flat (butterfly) form -/

/-- The address bit switched at stage `κ` (bit `0` = lowest): `0, 1, …, n, …, 1, 0`. -/
def stageBit (n κ : ℕ) : ℕ := if κ ≤ n then κ else 2 * n - κ

theorem stageBit_lt {n κ : ℕ} (h : κ ≤ 2 * n) : stageBit n κ < n + 1 := by
  unfold stageBit; split_ifs <;> omega

/-- Flip bit `j` of an address (the identity if `j > n`). -/
def flipBit : (n : ℕ) → ℕ → Fin (2 ^ (n + 1)) → Fin (2 ^ (n + 1))
  | n, 0, x => (splitLow n).symm (!(splitLow n x).1, (splitLow n x).2)
  | 0, _ + 1, x => x
  | n + 1, j + 1, x => (splitLow (n + 1)).symm ((splitLow (n + 1) x).1, flipBit n j (splitLow (n + 1) x).2)

theorem flipBit_flipBit : ∀ (n j : ℕ) (x : Fin (2 ^ (n + 1))), flipBit n j (flipBit n j x) = x
  | n, 0, x => by simp [flipBit]
  | 0, _ + 1, _ => rfl
  | n + 1, j + 1, x => by simp [flipBit, flipBit_flipBit n j]

/-- The setting (`true` = cross) at stage `κ` of the switch that contains the address `a`
(`false` for `κ > 2n`). -/
def cross : {n : ℕ} → Settings n → ℕ → Fin (2 ^ (n + 1)) → Bool
  | _, .leaf b, κ, _ => decide (κ = 0) && b
  | _, @Settings.node n f t g, κ, a =>
      if κ = 0 then f (splitLow (n + 1) a).2
      else if κ ≤ 2 * n + 1 then cross (t (splitLow (n + 1) a).1) (κ - 1) (splitLow (n + 1) a).2
      else if κ = 2 * n + 2 then g (splitLow (n + 1) a).2
      else false

theorem cross_eq_false : ∀ {n : ℕ} (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))),
    2 * n < κ → cross s κ a = false
  | _, .leaf b, κ, a, h => by simp [cross]; omega
  | _, @Settings.node n f t g, κ, a, h => by
    simp only [cross]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The two addresses of a switch have the same setting. -/
theorem cross_flipBit : ∀ {n : ℕ} (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))),
    κ ≤ 2 * n → cross s κ (flipBit n (stageBit n κ) a) = cross s κ a
  | _, .leaf b, κ, a, _ => by simp [cross]
  | _, @Settings.node n f t g, κ, a, hκ => by
    rcases Nat.eq_zero_or_pos κ with rfl | hpos
    · simp [cross, stageBit, flipBit]
    · by_cases h1 : κ ≤ 2 * n + 1
      · have hb : stageBit (n + 1) κ = stageBit n (κ - 1) + 1 := by
          unfold stageBit; split_ifs <;> omega
        rw [hb]
        simp only [cross, flipBit, Equiv.apply_symm_apply]
        rw [if_neg (by omega), if_pos h1, if_neg (by omega), if_pos h1]
        exact cross_flipBit (t _) (κ - 1) _ (by omega)
      · have hκ' : κ = 2 * n + 2 := by omega
        subst hκ'
        have hb : stageBit (n + 1) (2 * n + 2) = 0 := by
          unfold stageBit; split_ifs <;> omega
        rw [hb]
        simp [cross, flipBit]

variable {n : ℕ}

/-- One switch stage as a map on addresses. -/
def stageFun (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))) : Fin (2 ^ (n + 1)) :=
  if cross s κ a then flipBit n (stageBit n κ) a else a

theorem stageFun_stageFun (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))) :
    stageFun s κ (stageFun s κ a) = a := by
  unfold stageFun
  by_cases hc : cross s κ a = true
  · have hκ : κ ≤ 2 * n := by
      by_contra h
      rw [cross_eq_false s κ a (by omega)] at hc
      exact absurd hc (by simp)
    rw [if_pos hc, cross_flipBit s κ a hκ, if_pos hc, flipBit_flipBit]
  · simp [hc]

theorem cross_stageFun (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))) :
    cross s κ (stageFun s κ a) = cross s κ a := by
  unfold stageFun
  by_cases hc : cross s κ a = true
  · have hκ : κ ≤ 2 * n := by
      by_contra h
      rw [cross_eq_false s κ a (by omega)] at hc
      exact absurd hc (by simp)
    rw [if_pos hc, cross_flipBit s κ a hκ]
  · simp [hc]

/-- One switch stage as a permutation. -/
def stagePerm (s : Settings n) (κ : ℕ) : Perm (Fin (2 ^ (n + 1))) :=
  Function.Involutive.toPerm (stageFun s κ) (stageFun_stageFun s κ)

@[simp] theorem stagePerm_apply (s : Settings n) (κ : ℕ) (a : Fin (2 ^ (n + 1))) :
    stagePerm s κ a = stageFun s κ a := rfl

@[simp] theorem stagePerm_symm (s : Settings n) (κ : ℕ) : (stagePerm s κ).symm = stagePerm s κ :=
  Function.Involutive.toPerm_symm _

/-- The first `κ` stages: the item at input `a` is at `upTo s κ a` in column `κ`. -/
def upTo (s : Settings n) : ℕ → Perm (Fin (2 ^ (n + 1)))
  | 0 => 1
  | κ + 1 => (upTo s κ).trans (stagePerm s κ)

/-- The route of the flat network: the stages `0, 1, …, 2n` in this order. -/
def flatRoute (s : Settings n) : Perm (Fin (2 ^ (n + 1))) := upTo s (2 * n + 1)

theorem upTo_node {n : ℕ} (f : Fin (2 ^ (n + 1)) → Bool) (t : Bool → Settings n)
    (g : Fin (2 ^ (n + 1)) → Bool) (b : Bool) (l : Fin (2 ^ (n + 1))) :
    ∀ κ, κ ≤ 2 * n + 1 →
      upTo (Settings.node f t g) (κ + 1) ((splitLow (n + 1)).symm (b, l)) =
        (splitLow (n + 1)).symm (xor b (f l), upTo (t (xor b (f l))) κ l)
  | 0, _ => by
    simp only [upTo, Equiv.trans_apply, stagePerm_apply, stageFun, cross, Equiv.apply_symm_apply,
      if_pos rfl, Perm.one_apply]
    cases hf : f l
    · simp
    · simp [stageBit, flipBit]
  | κ + 1, hκ => by
    have ih := upTo_node f t g b l κ (by omega)
    rw [upTo, Equiv.trans_apply, ih, stagePerm_apply, upTo, Equiv.trans_apply, stagePerm_apply]
    have hb : stageBit (n + 1) (κ + 1) = stageBit n κ + 1 := by
      unfold stageBit; split_ifs <;> omega
    simp only [stageFun, cross, Equiv.apply_symm_apply, if_neg (Nat.succ_ne_zero κ),
      if_pos (show κ + 1 ≤ 2 * n + 1 by omega), Nat.add_sub_cancel, hb, flipBit]
    split_ifs <;> rfl

/-- The flat route equals the recursive route. -/
theorem flatRoute_eq : ∀ {n : ℕ} (s : Settings n), flatRoute s = routeRec s
  | _, .leaf b => by
    ext1 x
    obtain ⟨⟨c, u⟩, rfl⟩ := exists_splitLow 0 x
    simp only [flatRoute, upTo, Equiv.trans_apply, Perm.one_apply, stagePerm_apply, stageFun,
      cross, routeRec, lowStage_apply]
    cases b <;> simp [stageBit, flipBit]
  | _, @Settings.node n f t g => by
    ext1 x
    obtain ⟨⟨b, l⟩, rfl⟩ := exists_splitLow (n + 1) x
    have h2 : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by ring
    rw [flatRoute, h2, upTo, Equiv.trans_apply, upTo_node f t g b l (2 * n + 1) le_rfl]
    have ih : upTo (t (xor b (f l))) (2 * n + 1) = routeRec (t (xor b (f l))) :=
      flatRoute_eq (t (xor b (f l)))
    rw [ih]
    have hb : stageBit (n + 1) (2 * n + 1 + 1) = 0 := by
      unfold stageBit; split_ifs <;> omega
    simp only [stagePerm_apply, stageFun, cross, Equiv.apply_symm_apply,
      if_neg (show 2 * n + 1 + 1 ≠ 0 by omega), if_neg (show ¬ 2 * n + 1 + 1 ≤ 2 * n + 1 by omega),
      if_pos (show 2 * n + 1 + 1 = 2 * n + 2 by omega), hb, routeRec, Equiv.trans_apply,
      lowStage_apply, midStage_apply]
    cases g (routeRec (t (xor b (f l))) l) <;> simp [flipBit]

/-- Correctness of the canonical settings, flat form. -/
theorem flatRoute_settings (n : ℕ) (π : Perm (Fin (2 ^ (n + 1)))) :
    flatRoute (settings n π) = π := by
  rw [flatRoute_eq, routeRec_settings]

end Net
end P1Benes
