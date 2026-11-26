import P1Net.GlueRouting

/-!
# P4 glue: the state routing delivers the state permutation (lane P1-lean-net, restart 2026-11-25)

The state routing of each big interval (positions `st c π`, `h + 1` address bits, one type bit) is the same butterfly
as the state routing; `st_route` is `rt_route` for it: in a labelling at which every site predicate holds, the item
at the last column at address `route s x` is the item at column `0` at address `x`, for the settings
`s = bset (1 + h) (stAddr h)`. Text adapted from `GlueRouting.lean` (`rt` → `st`, `3` type bits → `1`).
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-- The flip of stage `κ` on an address (type bits, lane bits). -/
theorem addrOf_add_flip1 (π : BitWord 1) (l : BitWord h) (κ : ℕ) :
    addrOf (π + tyFlip 1 h κ) (l + lnFlip 1 h κ) = addrOf π l + Routing.flip (1 + h) κ := by
  funext b
  by_cases hb : (b : ℕ) < 1
  · simp only [addrOf, dif_pos hb, Pi.add_apply, tyFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
  · simp only [addrOf, dif_neg hb, Pi.add_apply, lnFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
    have e : (b : ℕ) - 1 + 1 = b := by omega
    simp only [e]

theorem addrSplit_addrOf1 (π : BitWord 1) (l : BitWord h) : addrSplit (addrOf π l) = (π, l) :=
  (addrEquiv 1 h).left_inv (π, l)

theorem addrOf_addrSplit1 (x : Routing.Addr (1 + h)) : addrOf (addrSplit x).1 (addrSplit x).2 = x :=
  (addrEquiv 1 h).right_inv x

theorem addrSplit_add_flip1 (x : Routing.Addr (1 + h)) (κ : ℕ) :
    addrSplit (x + Routing.flip (1 + h) κ) =
      ((addrSplit x).1 + tyFlip 1 h κ, (addrSplit x).2 + lnFlip 1 h κ) := by
  rw [← addrSplit_addrOf1 ((addrSplit x).1 + tyFlip 1 h κ) ((addrSplit x).2 + lnFlip 1 h κ),
    addrOf_add_flip1, addrOf_addrSplit1]

/-! ## Mates of the routing slots -/

variable (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3)

theorem netMate_st2 (ι : Fin I) {c c' : Fin (2 * (h + 1))} (π : BitWord 1) (hp : colPred c = some c') :
    netMate I σ ((ι, Loc.st c π), 2) = some ((ι, Loc.st c' π), 0) := by
  simp [netMate, locMate, hp]

theorem netMate_st3 (ι : Fin I) {c c' : Fin (2 * (h + 1))} (π : BitWord 1) (hp : colPred c = some c') :
    netMate I σ ((ι, Loc.st c π), 3) = some ((ι, Loc.st c' (π + tyFlip 1 h c')), 1) := by
  simp [netMate, locMate, hp]

theorem netDisp_st2 (ι : Fin I) {c c' : Fin (2 * (h + 1))} (π : BitWord 1) (hp : colPred c = some c') :
    netDisp I σ ((ι, Loc.st c π), 2) = 0 := by
  simp [netDisp, netMate_st2 I σ ι π hp, disp1]

theorem netDisp_st3 (ι : Fin I) {c c' : Fin (2 * (h + 1))} (π : BitWord 1) (hp : colPred c = some c') :
    netDisp I σ ((ι, Loc.st c π), 3) = lnFlip 1 h c' := by
  simp [netDisp, netMate_st3 I σ ι π hp, disp1]

/-! ## Items and arcs of the state routing in a labelling -/

section Labelling

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : (e : (rnState V B I σ ha).network.Edge) → (rnState V B I σ ha).network.Payload e)

/-- The site of a state-routing position. -/
def stSite (ι : Fin I) (c : Fin (2 * (h + 1))) (π : BitWord 1) (l : BitWord h) :
    (rnState V B I σ ha).Base × BitWord h :=
  (((ι, Loc.st c π), false), l)

/-- The item at a state-routing position (column `κ`, address `x`): the word of the selected in-arc (the
source at column `0`). -/
noncomputable def stPos (ι : Fin I) (s : Routing.Settings (1 + h)) (κ : ℕ)
    (x : Routing.Addr (1 + h)) : Fin (strWidth V B) → Bool :=
  if hκ : κ < 2 * (h + 1) then
    if κ = 0 then zIn V B I σ ha z (stSite V B I σ ha ι ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 2
    else if s (κ - 1) (Routing.rep (1 + h) (κ - 1) x) then
      zIn V B I σ ha z (stSite V B I σ ha ι ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 3
    else zIn V B I σ ha z (stSite V B I σ ha ι ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 2
  else fun _ => false

/-- The out-arc `b` (straight `false`, cross `true`) of a state-routing position. -/
noncomputable def stArc (ι : Fin I) (κ : ℕ) (x : Routing.Addr (1 + h)) (b : Bool) :
    Fin (strWidth V B) → Bool :=
  if hκ : κ < 2 * (h + 1) then
    zOut V B I σ ha z (stSite V B I σ ha ι ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) (if b then 1 else 0)
  else fun _ => false

/-- The routing constraint at a state-routing position, read in the labelling. -/
theorem st_routeOK (hOK : ∀ u, rnSiteOK V B L I σ ha bset u
      (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u))
    (ι : Fin I) (c : Fin (2 * (h + 1))) (π : BitWord 1) (l : BitWord h) :
    routeOK (bset (1 + h) (stAddr h)) c (addrOf π l)
      (zIn V B I σ ha z (stSite V B I σ ha ι c π l) 2) (zIn V B I σ ha z (stSite V B I σ ha ι c π l) 3)
      (zOut V B I σ ha z (stSite V B I σ ha ι c π l) 0) (zOut V B I σ ha z (stSite V B I σ ha ι c π l) 1) :=
  hOK (stSite V B I σ ha ι c π l)

/-- **The state routing delivers the routed permutation.** -/
theorem st_route (hOK : ∀ u, rnSiteOK V B L I σ ha bset u
      (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u))
    (ι : Fin I) (x : Routing.Addr (1 + h)) :
    stPos V B I σ ha z ι (bset (1 + h) (stAddr h)) (2 * (h + 1) - 1)
        (Routing.routeUpTo (bset (1 + h) (stAddr h)) (2 * (h + 1) - 1) x) =
      stPos V B I σ ha z ι (bset (1 + h) (stAddr h)) 0 x := by
  set s := bset (1 + h) (stAddr h) with hs
  apply Routing.forcing_le s (stPos V B I σ ha z ι s) (stArc V B I σ ha z ι) (2 * (h + 1) - 1)
  · -- out side: the selected out-arc carries the item
    intro κ hκ x
    have hκ' : κ < 2 * (h + 1) := by omega
    have hr := st_routeOK V B L I σ ha bset z hOK ι ⟨κ, hκ'⟩ (addrSplit x).1 (addrSplit x).2
    rw [addrOf_addrSplit1] at hr
    simp only [routeOK] at hr
    rw [if_neg (show ¬ ((⟨κ, hκ'⟩ : Fin (2 * (h + 1))) : ℕ) + 1 = 2 * (1 + h) by simp; omega)] at hr
    simp only [stArc, stPos, dif_pos hκ']
    by_cases hsw : s κ (Routing.rep (1 + h) κ x) = true
    · rw [if_pos hsw] at hr
      simp only [hsw, ↓reduceIte]
      exact hr.1
    · rw [if_neg hsw] at hr
      simp only [hsw, Bool.false_eq_true, ↓reduceIte]
      exact hr.1
  · -- in side: the item of column `κ + 1` comes along the selected in-arc
    intro κ hκ x'
    have hκ1 : κ + 1 < 2 * (h + 1) := by omega
    have hκ0 : κ < 2 * (h + 1) := by omega
    have hp : colPred (⟨κ + 1, hκ1⟩ : Fin (2 * (h + 1))) = some ⟨κ, hκ0⟩ := by
      simp [colPred]
    simp only [stPos, dif_pos hκ1, Nat.add_sub_cancel, show κ + 1 ≠ 0 by omega, ↓reduceIte]
    by_cases hsw : s κ (Routing.rep (1 + h) κ x') = true
    · simp only [hsw, ↓reduceIte, Routing.stage]
      -- cross: from out-slot `1` of column `κ` at the flipped address
      rw [stSite, zIn_mate V B I σ ha z (netMate_st3 I σ ι (addrSplit x').1 hp),
        netDisp_st3 I σ ι (addrSplit x').1 hp]
      simp only [stArc, dif_pos hκ0, stSite, addrSplit_add_flip1, ↓reduceIte]
    · simp only [hsw, Bool.false_eq_true, ↓reduceIte, Routing.stage]
      rw [stSite, zIn_mate V B I σ ha z (netMate_st2 I σ ι (addrSplit x').1 hp),
        netDisp_st2 I σ ι (addrSplit x').1 hp, add_zero]
      simp only [stArc, dif_pos hκ0, stSite, Bool.false_eq_true, ↓reduceIte]
  · exact le_rfl

end Labelling

end P1Net
