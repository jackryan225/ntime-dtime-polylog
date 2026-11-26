import P1Net.StateNet

/-!
# Explicit numbering of the local vertices (base order of `N_{x,σ}`)

Lane P1-lean-net (2026-11-25, restart). Before the restart the base order used `Fintype.equivFin (Loc K h)`: a
bijection with no formula, chosen separately for every `h`, so no checker program could compute it. Now the
order is an explicit formula in `h`, `|K|` and two FIXED finite data of the machine, which do not depend on the
input length: the numbering `kIdx K` of the tapes and the order `extIdx K` of the table path.

`locNum l` (the value of `locEquiv K h l`), with `E = |Ext K|`, `k̂ = kIdx K k`, `C = 2 (h + 3)`, `D = 2 (h + 1)`:
* `tabC ↦ 0`;  `tabP c ↦ 1 + extIdx c`;
* `portIn k δ ↦ 1 + E + 3 k̂ + δ`;  `portOut k δ ↦ 1 + E + 3 |K| + 3 k̂ + δ`;
* `rt k c π ↦ 1 + E + 6 |K| + 8 (C k̂ + c) + num3 π`;
* `st c π ↦ 1 + E + 6 |K| + 8 C |K| + 2 c + π 0`;
* `eIn ↦ 1 + E + 6 |K| + 8 C |K| + 2 D`;  `eOut ↦` that `+ 1`;  `locCount K h =` that `+ 2`.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression

variable (K : Type) [Fintype K] [DecidableEq K] (h : ℕ)

/-- The fixed numbering of the tapes (a finite datum of the machine, independent of the input length). -/
noncomputable def kIdx : K ≃ Fin (Fintype.card K) := Fintype.equivFin K

/-- Type bits as numbers (`num3`, binary). -/
def bw3Equiv : BitWord 3 ≃ Fin 8 where
  toFun π := ⟨num3 π, num3_lt π⟩
  invFun n := code3 n
  left_inv π := code3_num3 π
  right_inv n := Fin.ext (num3_code3 n n.isLt)

/-- The one state type bit as a number. -/
def bw1Equiv : BitWord 1 ≃ Fin 2 := Equiv.funUnique (Fin 1) (ZMod 2)

theorem bw1Equiv_val (π : BitWord 1) : (bw1Equiv π : ℕ) = (π 0).val := rfl

/-- The local vertices as a sum of simple types (constructor order). -/
def locSum : Loc K h ≃
    Unit ⊕ (Ext K ⊕ ((K × Fin 3) ⊕ ((K × Fin 3) ⊕ (((K × Fin (2 * (h + 3))) × BitWord 3) ⊕
      ((Fin (2 * (h + 1)) × BitWord 1) ⊕ (Unit ⊕ Unit)))))) where
  toFun
    | .tabC => .inl ()
    | .tabP c => .inr (.inl c)
    | .portIn k δ => .inr (.inr (.inl (k, δ)))
    | .portOut k δ => .inr (.inr (.inr (.inl (k, δ))))
    | .rt k c π => .inr (.inr (.inr (.inr (.inl ((k, c), π)))))
    | .st c π => .inr (.inr (.inr (.inr (.inr (.inl (c, π))))))
    | .eIn => .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
    | .eOut => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
  invFun
    | .inl () => .tabC
    | .inr (.inl c) => .tabP c
    | .inr (.inr (.inl (k, δ))) => .portIn k δ
    | .inr (.inr (.inr (.inl (k, δ)))) => .portOut k δ
    | .inr (.inr (.inr (.inr (.inl ((k, c), π))))) => .rt k c π
    | .inr (.inr (.inr (.inr (.inr (.inl (c, π)))))) => .st c π
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))) => .eIn
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))) => .eOut
  left_inv l := by cases l <;> rfl
  right_inv x := by
    rcases x with _ | c | ⟨k, δ⟩ | ⟨k, δ⟩ | ⟨⟨k, c⟩, π⟩ | ⟨c, π⟩ | _ | _ <;> rfl

section LocSum
variable {K h}
@[simp] theorem locSum_tabC : locSum K h .tabC = .inl () := rfl
@[simp] theorem locSum_tabP (c : Ext K) : locSum K h (.tabP c) = .inr (.inl c) := rfl
@[simp] theorem locSum_portIn (k : K) (δ : Fin 3) : locSum K h (.portIn k δ) = .inr (.inr (.inl (k, δ))) := rfl
@[simp] theorem locSum_portOut (k : K) (δ : Fin 3) :
    locSum K h (.portOut k δ) = .inr (.inr (.inr (.inl (k, δ)))) := rfl
@[simp] theorem locSum_rt (k : K) (c : Fin (2 * (h + 3))) (π : BitWord 3) :
    locSum K h (.rt k c π) = .inr (.inr (.inr (.inr (.inl ((k, c), π))))) := rfl
@[simp] theorem locSum_st (c : Fin (2 * (h + 1))) (π : BitWord 1) :
    locSum K h (.st c π) = .inr (.inr (.inr (.inr (.inr (.inl (c, π)))))) := rfl
@[simp] theorem locSum_eIn : locSum K h .eIn = .inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))) := rfl
@[simp] theorem locSum_eOut : locSum K h .eOut = .inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))) := rfl
end LocSum

/-- Pairs `(k, δ)` as numbers `3 k̂ + δ`. -/
noncomputable def kpEquiv : K × Fin 3 ≃ Fin (Fintype.card K * 3) :=
  ((kIdx K).prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- Routing positions `((k, c), π)` as numbers `8 (C k̂ + c) + num3 π`. -/
noncomputable def rtEquiv : (K × Fin (2 * (h + 3))) × BitWord 3 ≃ Fin (Fintype.card K * (2 * (h + 3)) * 8) :=
  ((((kIdx K).prodCongr (Equiv.refl _)).trans finProdFinEquiv).prodCongr bw3Equiv).trans finProdFinEquiv

/-- State routing positions `(c, π)` as numbers `2 c + π 0`. -/
def stEquiv' : Fin (2 * (h + 1)) × BitWord 1 ≃ Fin (2 * (h + 1) * 2) :=
  ((Equiv.refl _).prodCongr bw1Equiv).trans finProdFinEquiv

/-- The number of local vertices of one big interval. -/
abbrev locCount : ℕ :=
  1 + (Fintype.card (Ext K) + (Fintype.card K * 3 + (Fintype.card K * 3 +
    (Fintype.card K * (2 * (h + 3)) * 8 + (2 * (h + 1) * 2 + (1 + 1))))))

/-- Two numbered blocks side by side. -/
def sumE {α β : Type} {m n : ℕ} (e₁ : α ≃ Fin m) (e₂ : β ≃ Fin n) : α ⊕ β ≃ Fin (m + n) :=
  (e₁.sumCongr e₂).trans finSumFinEquiv

theorem sumE_inl {α β : Type} {m n : ℕ} (e₁ : α ≃ Fin m) (e₂ : β ≃ Fin n) (x : α) :
    (sumE e₁ e₂ (Sum.inl x) : ℕ) = e₁ x := by
  simp [sumE]

theorem sumE_inr {α β : Type} {m n : ℕ} (e₁ : α ≃ Fin m) (e₂ : β ≃ Fin n) (y : β) :
    (sumE e₁ e₂ (Sum.inr y) : ℕ) = m + e₂ y := by
  simp [sumE]

theorem fin1_val (x : Fin 1) : (x : ℕ) = 0 := Nat.lt_one_iff.mp x.isLt

theorem kpEquiv_val (k : K) (δ : Fin 3) : (kpEquiv K (k, δ) : ℕ) = (δ : ℕ) + 3 * (kIdx K k : ℕ) := by
  simp [kpEquiv, finProdFinEquiv_apply_val]

theorem rtEquiv_val (k : K) (c : Fin (2 * (h + 3))) (π : BitWord 3) :
    (rtEquiv K h ((k, c), π) : ℕ) = num3 π + 8 * ((c : ℕ) + 2 * (h + 3) * (kIdx K k : ℕ)) := by
  simp [rtEquiv, finProdFinEquiv_apply_val, bw3Equiv]

theorem stEquiv'_val (c : Fin (2 * (h + 1))) (π : BitWord 1) :
    (stEquiv' h (c, π) : ℕ) = (π 0).val + 2 * (c : ℕ) := by
  simp only [stEquiv', Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    finProdFinEquiv_apply_val, bw1Equiv_val]

/-- **The explicit numbering of the local vertices.** -/
noncomputable def locEquiv : Loc K h ≃ Fin (locCount K h) :=
  (locSum K h).trans <|
    sumE finOneEquiv.symm <| sumE (extIdx K) <| sumE (kpEquiv K) <| sumE (kpEquiv K) <| sumE (rtEquiv K h) <|
      sumE (stEquiv' h) <| sumE finOneEquiv.symm finOneEquiv.symm

/-- The value of the numbering (closed form; see the module header). -/
noncomputable def locNum : Loc K h → ℕ
  | .tabC => 0
  | .tabP c => 1 + (extIdx K c : ℕ)
  | .portIn k δ => 1 + Fintype.card (Ext K) + (3 * (kIdx K k : ℕ) + (δ : ℕ))
  | .portOut k δ => 1 + Fintype.card (Ext K) + Fintype.card K * 3 + (3 * (kIdx K k : ℕ) + (δ : ℕ))
  | .rt k c π => 1 + Fintype.card (Ext K) + Fintype.card K * 3 + Fintype.card K * 3 +
      (8 * (2 * (h + 3) * (kIdx K k : ℕ) + (c : ℕ)) + num3 π)
  | .st c π => 1 + Fintype.card (Ext K) + Fintype.card K * 3 + Fintype.card K * 3 +
      Fintype.card K * (2 * (h + 3)) * 8 + (2 * (c : ℕ) + (π 0).val)
  | .eIn => 1 + Fintype.card (Ext K) + Fintype.card K * 3 + Fintype.card K * 3 +
      Fintype.card K * (2 * (h + 3)) * 8 + 2 * (h + 1) * 2
  | .eOut => 1 + Fintype.card (Ext K) + Fintype.card K * 3 + Fintype.card K * 3 +
      Fintype.card K * (2 * (h + 3)) * 8 + 2 * (h + 1) * 2 + 1

theorem locEquiv_val (l : Loc K h) : (locEquiv K h l : ℕ) = locNum K h l := by
  cases l <;>
    simp only [locEquiv, Equiv.trans_apply, locSum_tabC, locSum_tabP, locSum_portIn, locSum_portOut,
      locSum_rt, locSum_st, locSum_eIn, locSum_eOut, sumE_inl, sumE_inr, kpEquiv_val, rtEquiv_val,
      stEquiv'_val, fin1_val, locNum] <;> ring

omit [DecidableEq K] in
theorem card_loc : Fintype.card (Loc K h) = locCount K h :=
  (Fintype.card_congr (locEquiv K h)).trans (Fintype.card_fin _)

end P1Net
