import P1Net.Glue

/-!
# P4 glue: the content routing delivers the access permutation (lane P1-lean-net, copy A)

For an edge labelling `z` of `N_{x,σ}` at which every site predicate holds, and switch settings `s` of the content
routing of big interval `ι` and tape `k`: the item held at the last column at address `route s x` is the item
held at column `0` at address `x` (`rt_route`). Items: `rtPos` (the word of the selected in-arc; at column `0` the
source word), arcs `rtArc` (the out-words of slots `0` / `1`). The proof instantiates `Routing.forcing_le` with
the routing constraints `routeOK` (out side) and the mates of the in-slots `2`, `3` (in side: both ends read
one edge, `inWord_regularize_mate`; addresses move by the stage flip, `addrOf_add_flip`).
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-- The flip of stage `κ` on an address (type bits, lane bits). -/
theorem addrOf_add_flip (π : BitWord 3) (l : BitWord h) (κ : ℕ) :
    addrOf (π + tyFlip 3 h κ) (l + lnFlip 3 h κ) = addrOf π l + Routing.flip (3 + h) κ := by
  funext b
  by_cases hb : (b : ℕ) < 3
  · simp only [addrOf, dif_pos hb, Pi.add_apply, tyFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
  · simp only [addrOf, dif_neg hb, Pi.add_apply, lnFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
    have e : (b : ℕ) - 3 + 3 = b := by omega
    simp only [e]

theorem addrSplit_addrOf (π : BitWord 3) (l : BitWord h) : addrSplit (addrOf π l) = (π, l) :=
  (addrEquiv 3 h).left_inv (π, l)

theorem addrOf_addrSplit (x : Routing.Addr (3 + h)) : addrOf (addrSplit x).1 (addrSplit x).2 = x :=
  (addrEquiv 3 h).right_inv x

theorem addrSplit_add_flip (x : Routing.Addr (3 + h)) (κ : ℕ) :
    addrSplit (x + Routing.flip (3 + h) κ) =
      ((addrSplit x).1 + tyFlip 3 h κ, (addrSplit x).2 + lnFlip 3 h κ) := by
  rw [← addrSplit_addrOf ((addrSplit x).1 + tyFlip 3 h κ) ((addrSplit x).2 + lnFlip 3 h κ),
    addrOf_add_flip, addrOf_addrSplit]

/-! ## Mates of the routing slots -/

variable (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3)

theorem netMate_rt2 (ι : Fin I) (k : K) {c c' : Fin (2 * (h + 3))} (π : BitWord 3) (hp : colPred c = some c') :
    netMate I σ ((ι, Loc.rt k c π), 2) = some ((ι, Loc.rt k c' π), 0) := by
  simp [netMate, locMate, hp]

theorem netMate_rt3 (ι : Fin I) (k : K) {c c' : Fin (2 * (h + 3))} (π : BitWord 3) (hp : colPred c = some c') :
    netMate I σ ((ι, Loc.rt k c π), 3) = some ((ι, Loc.rt k c' (π + tyFlip 3 h c')), 1) := by
  simp [netMate, locMate, hp]

theorem netDisp_rt2 (ι : Fin I) (k : K) {c c' : Fin (2 * (h + 3))} (π : BitWord 3) (hp : colPred c = some c') :
    netDisp I σ ((ι, Loc.rt k c π), 2) = 0 := by
  simp [netDisp, netMate_rt2 I σ ι k π hp, disp1]

theorem netDisp_rt3 (ι : Fin I) (k : K) {c c' : Fin (2 * (h + 3))} (π : BitWord 3) (hp : colPred c = some c') :
    netDisp I σ ((ι, Loc.rt k c π), 3) = lnFlip 3 h c' := by
  simp [netDisp, netMate_rt3 I σ ι k π hp, disp1]

/-! ## Items and arcs of the content routing in a labelling -/

section Labelling

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : (e : (rnState V B I σ ha).network.Edge) → (rnState V B I σ ha).network.Payload e)

/-- The in-word of half-edge slot `s` at site `u` in the labelling `z`. -/
noncomputable def zIn (u : (rnState V B I σ ha).Base × BitWord h) (s : Fin 4) : Fin (strWidth V B) → Bool :=
  inWord (rnState V B I σ ha) u
    (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u)
    (s.castLE ha) (strWidth V B)

/-- The out-word of half-edge slot `s` at site `u` in the labelling `z`. -/
noncomputable def zOut (u : (rnState V B I σ ha).Base × BitWord h) (s : Fin 4) : Fin (strWidth V B) → Bool :=
  outWord (rnState V B I σ ha) u
    (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u)
    (s.castLE ha) (strWidth V B)

/-- The site of a content-routing position. -/
def rtSite (ι : Fin I) (k : V.K) (c : Fin (2 * (h + 3))) (π : BitWord 3) (l : BitWord h) :
    (rnState V B I σ ha).Base × BitWord h :=
  (((ι, Loc.rt k c π), false), l)

/-- Both ends of a mated half-edge read one edge. -/
theorem zIn_mate {v v' : Fin I × Loc V.K h} {s s' : Fin 4} (hm : netMate I σ (v, s) = some (v', s'))
    (l : BitWord h) :
    zIn V B I σ ha z ((v, false), l) s = zOut V B I σ ha z ((v', false), l + netDisp I σ (v, s)) s' :=
  inWord_regularize_mate (preGraph I σ) ha _ z hm false l (strWidth V B)

/-- The item at a content-routing position (column `κ`, address `x`): the word of the selected in-arc (the
source at column `0`). -/
noncomputable def rtPos (ι : Fin I) (k : V.K) (s : Routing.Settings (3 + h)) (κ : ℕ)
    (x : Routing.Addr (3 + h)) : Fin (strWidth V B) → Bool :=
  if hκ : κ < 2 * (h + 3) then
    if κ = 0 then zIn V B I σ ha z (rtSite V B I σ ha ι k ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 2
    else if s (κ - 1) (Routing.rep (3 + h) (κ - 1) x) then
      zIn V B I σ ha z (rtSite V B I σ ha ι k ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 3
    else zIn V B I σ ha z (rtSite V B I σ ha ι k ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) 2
  else fun _ => false

/-- The out-arc `b` (straight `false`, cross `true`) of a content-routing position. -/
noncomputable def rtArc (ι : Fin I) (k : V.K) (κ : ℕ) (x : Routing.Addr (3 + h)) (b : Bool) :
    Fin (strWidth V B) → Bool :=
  if hκ : κ < 2 * (h + 3) then
    zOut V B I σ ha z (rtSite V B I σ ha ι k ⟨κ, hκ⟩ (addrSplit x).1 (addrSplit x).2) (if b then 1 else 0)
  else fun _ => false

/-- The routing constraint at a content-routing position, read in the labelling. -/
theorem rt_routeOK (hOK : ∀ u, rnSiteOK V B L I σ ha bset u
      (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u))
    (ι : Fin I) (k : V.K) (c : Fin (2 * (h + 3))) (π : BitWord 3) (l : BitWord h) :
    routeOK (bset (3 + h) (accAddr I σ ι k)) c (addrOf π l)
      (zIn V B I σ ha z (rtSite V B I σ ha ι k c π l) 2) (zIn V B I σ ha z (rtSite V B I σ ha ι k c π l) 3)
      (zOut V B I σ ha z (rtSite V B I σ ha ι k c π l) 0) (zOut V B I σ ha z (rtSite V B I σ ha ι k c π l) 1) :=
  hOK (rtSite V B I σ ha ι k c π l)

/-- **The content routing delivers the routed permutation.** -/
theorem rt_route (hOK : ∀ u, rnSiteOK V B L I σ ha bset u
      (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u))
    (ι : Fin I) (k : V.K) (x : Routing.Addr (3 + h)) :
    rtPos V B I σ ha z ι k (bset (3 + h) (accAddr I σ ι k)) (2 * (h + 3) - 1)
        (Routing.routeUpTo (bset (3 + h) (accAddr I σ ι k)) (2 * (h + 3) - 1) x) =
      rtPos V B I σ ha z ι k (bset (3 + h) (accAddr I σ ι k)) 0 x := by
  set s := bset (3 + h) (accAddr I σ ι k) with hs
  apply Routing.forcing_le s (rtPos V B I σ ha z ι k s) (rtArc V B I σ ha z ι k) (2 * (h + 3) - 1)
  · -- out side: the selected out-arc carries the item
    intro κ hκ x
    have hκ' : κ < 2 * (h + 3) := by omega
    have hr := rt_routeOK V B L I σ ha bset z hOK ι k ⟨κ, hκ'⟩ (addrSplit x).1 (addrSplit x).2
    rw [addrOf_addrSplit] at hr
    simp only [routeOK] at hr
    rw [if_neg (show ¬ ((⟨κ, hκ'⟩ : Fin (2 * (h + 3))) : ℕ) + 1 = 2 * (3 + h) by simp; omega)] at hr
    simp only [rtArc, rtPos, dif_pos hκ']
    by_cases hsw : s κ (Routing.rep (3 + h) κ x) = true
    · rw [if_pos hsw] at hr
      simp only [hsw, ↓reduceIte]
      exact hr.1
    · rw [if_neg hsw] at hr
      simp only [hsw, Bool.false_eq_true, ↓reduceIte]
      exact hr.1
  · -- in side: the item of column `κ + 1` comes along the selected in-arc
    intro κ hκ x'
    have hκ1 : κ + 1 < 2 * (h + 3) := by omega
    have hκ0 : κ < 2 * (h + 3) := by omega
    have hp : colPred (⟨κ + 1, hκ1⟩ : Fin (2 * (h + 3))) = some ⟨κ, hκ0⟩ := by
      simp [colPred]
    simp only [rtPos, dif_pos hκ1, Nat.add_sub_cancel, show κ + 1 ≠ 0 by omega, ↓reduceIte]
    by_cases hsw : s κ (Routing.rep (3 + h) κ x') = true
    · simp only [hsw, ↓reduceIte, Routing.stage]
      -- cross: from out-slot `1` of column `κ` at the flipped address
      rw [rtSite, zIn_mate V B I σ ha z (netMate_rt3 I σ ι k (addrSplit x').1 hp),
        netDisp_rt3 I σ ι k (addrSplit x').1 hp]
      simp only [rtArc, dif_pos hκ0, rtSite, addrSplit_add_flip, ↓reduceIte]
    · simp only [hsw, Bool.false_eq_true, ↓reduceIte, Routing.stage]
      rw [rtSite, zIn_mate V B I σ ha z (netMate_rt2 I σ ι k (addrSplit x').1 hp),
        netDisp_rt2 I σ ι k (addrSplit x').1 hp, add_zero]
      simp only [rtArc, dif_pos hκ0, rtSite, Bool.false_eq_true, ↓reduceIte]
  · exact le_rfl

end Labelling

end P1Net
