import P1Benes.Net

/-!
# Wire values of the flat Beneš network (lane P1-lean-benes)

Items are a type `I` with an identification `e : I ≃ Fin (2^(n+1))` (the label). Position columns are
`0, …, 2n+1`; stage `κ ∈ {0, …, 2n}` lies between columns `κ` and `κ+1`. Every position `(κ, a)` with
`κ ≤ 2n` has two out-arcs: type `false` (straight) to `(κ+1, a)` and type `true` (cross) to
`(κ+1, flipI e κ a)`. `w κ a b` is the value on the out-arc of type `b` of position `(κ, a)`.

The position factor of the paper (network (d)): a position copies the value on its selected in-arc
(selected by the setting of the stage before it; the source value in column 0) to its selected out-arc
(selected by the setting of the stage after it; the destination in the last column), puts `z` on its
other out-arc, and requires its unselected in-arc to carry `z`. `ArcRun` lists these conditions.
Result: for every input there is exactly one run (`arcRun_unique`), and the destination of the item at
input `a` receives `inp a` at `routeI e s a` (`arcRun_out`).
-/

namespace P1Benes
namespace Net

open Equiv Equiv.Perm

variable {n : ℕ} {I : Type*} (e : I ≃ Fin (2 ^ (n + 1))) {α : Type*}

/-- The setting of stage `κ` at the switch that contains item `a` (`true` = cross). -/
def crossI (s : Settings n) (κ : ℕ) (a : I) : Bool := cross s κ (e a)

/-- The partner of `a` at stage `κ`: the other item of the same switch (bit `stageBit n κ` flipped). -/
def flipI (κ : ℕ) (a : I) : I := e.symm (flipBit n (stageBit n κ) (e a))

/-- Stage `κ` as a map on items: `a ↦ flipI e κ a` if crossed, else `a`. -/
def stageI (s : Settings n) (κ : ℕ) (a : I) : I := e.symm (stageFun s κ (e a))

theorem stageI_eq (s : Settings n) (κ : ℕ) (a : I) :
    stageI e s κ a = if crossI e s κ a then flipI e κ a else a := by
  unfold stageI crossI flipI stageFun
  split_ifs <;> simp

theorem flipI_flipI (κ : ℕ) (a : I) : flipI e κ (flipI e κ a) = a := by
  simp [flipI, flipBit_flipBit]

theorem crossI_flipI (s : Settings n) (κ : ℕ) (a : I) (hκ : κ ≤ 2 * n) :
    crossI e s κ (flipI e κ a) = crossI e s κ a := by
  simp [crossI, flipI, cross_flipBit s κ (e a) hκ]

theorem crossI_stageI (s : Settings n) (κ : ℕ) (a : I) :
    crossI e s κ (stageI e s κ a) = crossI e s κ a := by
  simp [crossI, stageI, cross_stageFun]

/-- Stage `κ` as a permutation of the items. -/
def stagePermI (s : Settings n) (κ : ℕ) : Perm I := e.trans ((stagePerm s κ).trans e.symm)

/-- The first `κ` stages on items. -/
def upToI (s : Settings n) : ℕ → Perm I
  | 0 => 1
  | κ + 1 => (upToI s κ).trans (stagePermI e s κ)

/-- The route on items: the stages `0, 1, …, 2n` in this order. -/
def routeI (s : Settings n) : Perm I := upToI e s (2 * n + 1)

theorem upToI_eq (s : Settings n) : ∀ κ, upToI e s κ = e.trans ((upTo s κ).trans e.symm)
  | 0 => by ext a; simp [upToI, upTo]
  | κ + 1 => by
    ext a
    simp [upToI, upTo, upToI_eq s κ, stagePermI]

theorem routeI_eq (s : Settings n) : routeI e s = e.trans ((flatRoute s).trans e.symm) :=
  upToI_eq e s _

/-- Correctness of the canonical settings on items. -/
theorem routeI_settings (π : Perm I) : routeI e (settings n (e.permCongr π)) = π := by
  rw [routeI_eq, flatRoute_settings]
  ext a
  simp [Equiv.permCongr_apply]

/-- The position factors of the network (paper network (d)) for inputs `inp`, destination values
`out`, arc values `w` and zero value `z`. -/
structure ArcRun (s : Settings n) (z : α) (inp out : I → α) (w : Fin (2 * n + 1) → I → Bool → α) :
    Prop where
  /-- column `0`: the selected out-arc carries the source value -/
  src : ∀ a, w 0 a (crossI e s 0 a) = inp a
  /-- columns `κ + 1 = 1, …, 2n`: the selected out-arc carries the value of the selected in-arc,
  which leaves `stageI e s κ a` and has type `crossI e s κ a` -/
  mid : ∀ (κ : Fin (2 * n)) a,
    w κ.succ a (crossI e s (κ.val + 1) a) = w κ.castSucc (stageI e s κ.val a) (crossI e s κ.val a)
  /-- every other out-arc carries `z` -/
  unsel : ∀ (κ : Fin (2 * n + 1)) a, w κ a (!crossI e s κ.val a) = z
  /-- last column `2n + 1`: the destination carries the value of the selected in-arc -/
  dest : ∀ a, out a = w (Fin.last (2 * n)) (stageI e s (2 * n) a) (crossI e s (2 * n) a)
  /-- the unselected in-arc of position `(κ + 1, a)` (type `!crossI e s κ a`) carries `z` -/
  zin : ∀ (κ : Fin (2 * n + 1)) a,
    w κ (if crossI e s κ.val a then a else flipI e κ.val a) (!crossI e s κ.val a) = z

/-- The value at position `(κ, a)` in the run: the input of the item that is there. -/
def posVal (s : Settings n) (inp : I → α) (κ : ℕ) (a : I) : α :=
  inp (e.symm ((upTo s κ).symm (e a)))

/-- The run: selected arcs carry the position value, the others `z`. -/
def canonW (s : Settings n) (z : α) (inp : I → α) : Fin (2 * n + 1) → I → Bool → α :=
  fun κ a b => if b = crossI e s κ.val a then posVal e s inp κ.val a else z

/-- The destinations of the run. -/
def canonOut (s : Settings n) (inp : I → α) : I → α := fun a => posVal e s inp (2 * n + 1) a

theorem posVal_zero (s : Settings n) (inp : I → α) (a : I) : posVal e s inp 0 a = inp a := by
  simp only [posVal, upTo]
  exact congrArg inp (e.symm_apply_apply a)

theorem posVal_succ (s : Settings n) (inp : I → α) (κ : ℕ) (a : I) :
    posVal e s inp (κ + 1) a = posVal e s inp κ (stageI e s κ a) := by
  simp [posVal, upTo, stageI, Equiv.symm_trans_apply]

theorem canon_arcRun (s : Settings n) (z : α) (inp : I → α) :
    ArcRun e s z inp (canonOut e s inp) (canonW e s z inp) where
  src a := by simp [canonW, posVal_zero]
  mid κ a := by
    simp only [canonW, Fin.val_succ, Fin.coe_castSucc, crossI_stageI, if_true, posVal_succ]
  unsel κ a := by simp [canonW]
  dest a := by
    simp only [canonOut, canonW, Fin.val_last, crossI_stageI, if_true, posVal_succ]
  zin κ a := by
    have hκ : κ.val ≤ 2 * n := by omega
    have hc : crossI e s κ.val (if crossI e s κ.val a then a else flipI e κ.val a) =
        crossI e s κ.val a := by
      split_ifs
      · rfl
      · exact crossI_flipI e s κ.val a hκ
    simp only [canonW, hc]
    cases crossI e s κ.val a <;> simp

/-- Every run is the canonical one. -/
theorem arcRun_eq {s : Settings n} {z : α} {inp out : I → α} {w : Fin (2 * n + 1) → I → Bool → α}
    (hr : ArcRun e s z inp out w) : w = canonW e s z inp ∧ out = canonOut e s inp := by
  -- the selected out-arc of `(k, a)` carries `posVal k a`
  have key : ∀ (k : ℕ) (hk : k < 2 * n + 1) (a : I),
      w ⟨k, hk⟩ a (crossI e s k a) = posVal e s inp k a := by
    intro k
    induction k with
    | zero => intro hk a; rw [posVal_zero]; exact hr.src a
    | succ k ih =>
      intro hk a
      have hm := hr.mid ⟨k, by omega⟩ a
      simp only [Fin.succ_mk, Fin.castSucc_mk] at hm
      rw [hm, posVal_succ, ← crossI_stageI e s k a]
      exact ih (by omega) _
  constructor
  · funext κ a b
    simp only [canonW]
    split_ifs with hb
    · subst hb; exact key κ.val κ.isLt a
    · have : b = !crossI e s κ.val a := by
        cases hc : crossI e s κ.val a <;> cases b <;> simp_all
      rw [this]; exact hr.unsel κ a
  · funext a
    rw [hr.dest a, canonOut, posVal_succ, ← crossI_stageI e s (2 * n) a]
    exact key (2 * n) (by omega) _

/-- Given the inputs, the wire values are uniquely determined. -/
theorem arcRun_unique (s : Settings n) (z : α) (inp : I → α) :
    ∃! p : (Fin (2 * n + 1) → I → Bool → α) × (I → α), ArcRun e s z inp p.2 p.1 := by
  refine ⟨(canonW e s z inp, canonOut e s inp), canon_arcRun e s z inp, ?_⟩
  rintro ⟨w, out⟩ hr
  obtain ⟨h1, h2⟩ := arcRun_eq e hr
  exact Prod.ext h1 h2

/-- The destination of the item at input `a` receives `inp a`. -/
theorem arcRun_out {s : Settings n} {z : α} {inp out : I → α} {w : Fin (2 * n + 1) → I → Bool → α}
    (hr : ArcRun e s z inp out w) (a : I) : out (routeI e s a) = inp a := by
  rw [(arcRun_eq e hr).2, canonOut, posVal, routeI_eq]
  simp [flatRoute]

end Net
end P1Benes
