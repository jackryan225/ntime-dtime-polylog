import P1Net.Factors

/-! Finite-column switch equations in both directions. -/

namespace P1Net.AstraContract

variable {m W : ℕ} [NeZero m]

abbrev WordAt (m W : ℕ) := ℕ → Routing.Addr m → Fin W → Bool

def selected (s : Routing.Settings m) (c : ℕ) (x : Routing.Addr m) (u v : Fin W → Bool) : Fin W → Bool :=
  if c = 0 then u else if s (c - 1) (Routing.rep m (c - 1) x) then v else u

def sends (s : Routing.Settings m) (c : ℕ) (x : Routing.Addr m) (w o p : Fin W → Bool) : Prop :=
  if c + 1 = 2 * m then o = w
  else if s c (Routing.rep m c x) then p = w ∧ o = fun _ => false
  else o = w ∧ p = fun _ => false

def prefixWord (s : Routing.Settings m) (source : Routing.Addr m → Fin W → Bool)
    (c : ℕ) (x : Routing.Addr m) : Fin W → Bool := source ((Routing.routeUpTo s c).symm x)

theorem prefixWord_succ (s : Routing.Settings m) (source : Routing.Addr m → Fin W → Bool)
    (c : ℕ) (x : Routing.Addr m) :
    prefixWord s source (c + 1) x = prefixWord s source c (Routing.stage s c x) := by
  apply congrArg source
  apply (Routing.routeUpTo s (c + 1)).injective
  rw [Equiv.apply_symm_apply, Routing.routeUpTo_succ_apply, Equiv.apply_symm_apply, Routing.stage_stage]

/-- The two outgoing arc words constructed from a source row. The final cross arc has width zero. -/
def canonicalArc (s : Routing.Settings m) (source : Routing.Addr m → Fin W → Bool)
    (c : ℕ) (x : Routing.Addr m) (b : Bool) : Fin W → Bool :=
  if c + 1 = 2 * m then (if b then fun _ => false else prefixWord s source c x)
  else if b = s c (Routing.rep m c x) then prefixWord s source c x else fun _ => false

theorem canonical_sends (s : Routing.Settings m) (source : Routing.Addr m → Fin W → Bool)
    (c : ℕ) (x : Routing.Addr m) :
    sends s c x (prefixWord s source c x) (canonicalArc s source c x false)
      (canonicalArc s source c x true) := by
  by_cases hl : c + 1 = 2 * m <;> cases hs : s c (Routing.rep m c x) <;>
    simp only [sends, canonicalArc, hl, hs, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, and_self]

/-- The selected word at the next row is obtained from the canonical arcs of this row. -/
theorem canonical_step (s : Routing.Settings m) (source : Routing.Addr m → Fin W → Bool)
    (c : ℕ) (hc : c + 1 < 2 * m) (x : Routing.Addr m) :
    selected s (c + 1) x (canonicalArc s source c x false)
      (canonicalArc s source c (x + Routing.flip m c) true) = prefixWord s source (c + 1) x := by
  have hl : c + 1 ≠ 2 * m := Nat.ne_of_lt hc
  rw [prefixWord_succ]
  cases hs : s c (Routing.rep m c x) <;>
    simp only [selected, Nat.succ_ne_zero, Nat.add_sub_cancel, canonicalArc, hl, Routing.rep_add_flip,
      Routing.stage, hs, Bool.false_eq_true, if_true, if_false]

/-- Every satisfying array has the explicit word at every position. At every internal column
this also specifies both outgoing arcs, including the unselected one. -/
theorem switch_normal_form (s : Routing.Settings m) (i₂ i₃ o₀ o₁ : WordAt m W)
    (hok : ∀ c, c < 2 * m → ∀ x, routeOK s c x (i₂ c x) (i₃ c x) (o₀ c x) (o₁ c x))
    (hstraight : ∀ c, c + 1 < 2 * m → ∀ x, i₂ (c + 1) x = o₀ c x)
    (hcross : ∀ c, c + 1 < 2 * m → ∀ x, i₃ (c + 1) x = o₁ c (x + Routing.flip m c))
    (c : ℕ) (hc : c < 2 * m) (x : Routing.Addr m) :
    selected s c x (i₂ c x) (i₃ c x) = prefixWord s (i₂ 0) c x ∧
    sends s c x (prefixWord s (i₂ 0) c x) (o₀ c x) (o₁ c x) := by
  let pos := fun u y => selected s u y (i₂ u y) (i₃ u y)
  let arc := fun u y (b : Bool) => if b then o₁ u y else o₀ u y
  have hout : ∀ u < 2 * m - 1, ∀ y, arc u y (s u (Routing.rep m u y)) = pos u y := by
    intro u hu y
    have H := hok u (by omega) y
    change sends s u y (pos u y) (o₀ u y) (o₁ u y) at H
    have hl : u + 1 ≠ 2 * m := by omega
    simp only [sends, if_neg hl] at H
    cases he : s u (Routing.rep m u y) <;>
      simp only [he, Bool.false_eq_true, if_true, if_false] at H <;> simpa only [arc, he, Bool.false_eq_true, ↓reduceIte] using H.1
  have hin : ∀ u < 2 * m - 1, ∀ y,
      pos (u + 1) y = arc u (Routing.stage s u y) (s u (Routing.rep m u y)) := by
    intro u hu y
    cases he : s u (Routing.rep m u y) <;>
      simp only [pos, selected, Nat.succ_ne_zero, Nat.add_sub_cancel, arc, Routing.stage, he,
        Bool.false_eq_true, if_true, if_false]
    · exact hstraight u (by omega) y
    · exact hcross u (by omega) y
  have e := Routing.forcing_le s pos arc (2 * m - 1) hout hin c (by omega) ((Routing.routeUpTo s c).symm x)
  rw [Equiv.apply_symm_apply] at e
  have e' : pos c x = prefixWord s (i₂ 0) c x := e
  have H : sends s c x (pos c x) (o₀ c x) (o₁ c x) := hok c hc x
  exact ⟨e', e' ▸ H⟩

theorem last_switch (s : Routing.Settings m) (i₂ i₃ o₀ o₁ : WordAt m W)
    (hok : ∀ c, c < 2 * m → ∀ x, routeOK s c x (i₂ c x) (i₃ c x) (o₀ c x) (o₁ c x))
    (hstraight : ∀ c, c + 1 < 2 * m → ∀ x, i₂ (c + 1) x = o₀ c x)
    (hcross : ∀ c, c + 1 < 2 * m → ∀ x, i₃ (c + 1) x = o₁ c (x + Routing.flip m c))
    (x : Routing.Addr m) : o₀ (2 * m - 1) (Routing.route s x) = i₂ 0 x := by
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  have hl : 2 * m - 1 + 1 = 2 * m := by omega
  have H := (switch_normal_form s i₂ i₃ o₀ o₁ hok hstraight hcross
    (2 * m - 1) (by omega) (Routing.route s x)).2
  simpa only [sends, if_pos hl, prefixWord, Routing.route, Equiv.symm_apply_apply] using H

end P1Net.AstraContract
