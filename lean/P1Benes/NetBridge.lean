import P1Benes.Link

/-!
# P1Benes.NetBridge: the P2 theorems in the forms used by `P1Net.ContractEqCount` (lane P1-lean-benes)

For lane P1-lean-net (research/p1/lean/Net/P1Net/Factors.lean, GlueRouting.lean). Everything is stated over lane
net's own routing semantics `P1Net.Routing`; this file imports only `P1Benes.Link`, hence `P1Benes.Settings` and
`P1Net.Routing` (Mathlib only).

1. `bset`: the parameter `bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m` of
   `P1Net.rnSiteOK` / `P1Net.rnFactors` / `P1Net.ContractEqCount`, filled with the canonical settings of lane P2.
   `route_bset` is EXACTLY the hypothesis of `P1Net.ContractEqCount`.
2. The canonical run `runPos` / `runArc` of ANY settings `s` and sources `src`, and bounded uniqueness
   `eq_run_le`, `arc_eq_run_le` (hypotheses only on the first `n` stages, as in `Routing.forcing_le`).
3. The butterfly of the lane network in `routeOK` form. `routeOKNet` is a verbatim copy of `P1Net.routeOK`
   (`@P1Net.routeOK = @routeOKNet` by `rfl`). `IsRun`: the in-words of column `c + 1` are the out-words of their
   mates, and every position `c < 2m` satisfies `routeOK`. `canon_isRun` (existence: the canonical words form a
   run with any given sources), `IsRun.eq_canon` (uniqueness: every run equals the canonical words of its sources,
   except the two words that `routeOK` does not constrain: out-slot `1` of the last column and in-slot `3` of
   column `0`), `IsRun.unique`, `IsRun.deliver` (the destination `route s a` receives the source of `a`).
-/

namespace P1Benes.NetBridge

/-! ## 1. The settings parameter `bset` -/

/-- The switch settings parameter `bset` of `P1Net.rnSiteOK`, `P1Net.rnFactors` and `P1Net.ContractEqCount`: the
canonical settings `P1Benes.settings` (looping rule, lane P2) on `m = m' + 1` address bits. (`m = 0` has no
`NeZero` instance; the value there is never used.) -/
def bset (m : ℕ) [NeZero m] (π : Equiv.Perm (P1Net.Routing.Addr m)) : P1Net.Routing.Settings m :=
  match m, π with
  | 0, _ => fun _ _ => false
  | m + 1, π => P1Benes.settings m π

theorem bset_succ (m : ℕ) (π : Equiv.Perm (P1Net.Routing.Addr (m + 1))) :
    bset (m + 1) π = P1Benes.settings m π := rfl

/-- **The hypothesis of `P1Net.ContractEqCount`, discharged:** `bset` routes every permutation. -/
theorem route_bset (m : ℕ) [hm : NeZero m] (π : Equiv.Perm (P1Net.Routing.Addr m)) :
    P1Net.Routing.route (bset m π) = π := by
  cases m with
  | zero => exact (hm.out rfl).elim
  | succ m => exact P1Benes.route_settings_net m π

/-! ## 2. The canonical run of any settings, and bounded uniqueness -/

theorem bool_eq_not_of_ne {b c : Bool} (h : ¬ b = c) : b = !c := by
  cases b <;> cases c <;> simp_all

section Run

variable {m : ℕ} [NeZero m] {P : Type*}

/-- The item of the canonical run at column `κ`, address `y`: the source item that the first `κ` stages bring
to `y`. -/
def runPos (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (y : P1Net.Routing.Addr m) : P :=
  src ((P1Net.Routing.routeUpTo s κ).symm y)

/-- The out-arc `b` of position `(κ, y)` in the canonical run: the item on the selected arc, `z` on the other. -/
def runArc (s : P1Net.Routing.Settings m) (z : P) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (y : P1Net.Routing.Addr m) (b : Bool) : P :=
  if b = s κ (P1Net.Routing.rep m κ y) then runPos s src κ y else z

theorem runPos_zero (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → P) :
    runPos s src 0 = src := rfl

theorem runPos_routeUpTo (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (a : P1Net.Routing.Addr m) : runPos s src κ (P1Net.Routing.routeUpTo s κ a) = src a := by
  simp only [runPos, Equiv.symm_apply_apply]

/-- At the last column the destination `route s a` holds the source item of `a`. -/
theorem runPos_route (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → P)
    (a : P1Net.Routing.Addr m) : runPos s src (2 * m - 1) (P1Net.Routing.route s a) = src a :=
  runPos_routeUpTo s src (2 * m - 1) a

theorem runPos_succ_stage (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (a : P1Net.Routing.Addr m) :
    runPos s src (κ + 1) a = runPos s src κ (P1Net.Routing.stage s κ a) :=
  -- `(stagePerm s κ * routeUpTo s κ).symm = (routeUpTo s κ).symm ∘ stage s κ` by definition
  rfl

/-- Out side of the canonical run: the selected out-arc carries the item. -/
theorem runArc_sel (s : P1Net.Routing.Settings m) (z : P) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (y : P1Net.Routing.Addr m) :
    runArc s z src κ y (s κ (P1Net.Routing.rep m κ y)) = runPos s src κ y := by
  unfold runArc
  exact if_pos rfl

/-- The unselected out-arc carries `z`. -/
theorem runArc_unsel (s : P1Net.Routing.Settings m) (z : P) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (y : P1Net.Routing.Addr m) : runArc s z src κ y (!s κ (P1Net.Routing.rep m κ y)) = z := by
  unfold runArc
  rw [if_neg]
  cases s κ (P1Net.Routing.rep m κ y) <;> decide

/-- In side of the canonical run: the item of column `κ + 1` is the word of its selected in-arc. -/
theorem runPos_succ (s : P1Net.Routing.Settings m) (z : P) (src : P1Net.Routing.Addr m → P) (κ : ℕ)
    (a' : P1Net.Routing.Addr m) :
    runPos s src (κ + 1) a' =
      runArc s z src κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a')) := by
  rw [runPos_succ_stage]
  unfold runArc
  rw [P1Net.Routing.rep_stage, if_pos rfl]

/-- **Bounded uniqueness of the items.** A labelling that obeys the switch semantics on the first `n` stages has,
at every column `κ ≤ n`, the items of the canonical run of its column-`0` items. -/
theorem eq_run_le (s : P1Net.Routing.Settings m) (pos : ℕ → P1Net.Routing.Addr m → P)
    (arc : ℕ → P1Net.Routing.Addr m → Bool → P) (n : ℕ)
    (hout : ∀ κ < n, ∀ a, arc κ a (s κ (P1Net.Routing.rep m κ a)) = pos κ a)
    (hin : ∀ κ < n, ∀ a', pos (κ + 1) a' =
      arc κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a'))) :
    ∀ κ ≤ n, pos κ = runPos s (pos 0) κ := by
  intro κ hκ
  funext y
  have e := P1Net.Routing.forcing_le s pos arc n hout hin κ hκ ((P1Net.Routing.routeUpTo s κ).symm y)
  rw [Equiv.apply_symm_apply] at e
  exact e

/-- **Bounded uniqueness of the arcs.** If moreover every unselected out-arc of the first `n` stages carries `z`,
every out-arc of the first `n` stages is the canonical one. -/
theorem arc_eq_run_le (s : P1Net.Routing.Settings m) (z : P) (pos : ℕ → P1Net.Routing.Addr m → P)
    (arc : ℕ → P1Net.Routing.Addr m → Bool → P) (n : ℕ)
    (hout : ∀ κ < n, ∀ a, arc κ a (s κ (P1Net.Routing.rep m κ a)) = pos κ a)
    (hin : ∀ κ < n, ∀ a', pos (κ + 1) a' =
      arc κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a')))
    (hz : ∀ κ < n, ∀ a, arc κ a (!s κ (P1Net.Routing.rep m κ a)) = z) :
    ∀ κ < n, arc κ = runArc s z (pos 0) κ := by
  intro κ hκ
  funext y b
  unfold runArc
  split_ifs with hb
  · rw [hb, hout κ hκ y, eq_run_le s pos arc n hout hin κ hκ.le]
  · rw [bool_eq_not_of_ne hb, hz κ hκ y]

end Run

/-! ## 3. The butterfly of the lane network in `routeOK` form -/

/-- **Verbatim copy of `P1Net.routeOK`** (research/p1/lean/Net/P1Net/Factors.lean:129, with the `Routing.` prefix
written out): `@P1Net.routeOK = @P1Benes.NetBridge.routeOKNet` holds by `rfl`. -/
def routeOKNet {m W : ℕ} [NeZero m] (s : P1Net.Routing.Settings m) (c : ℕ) (a : P1Net.Routing.Addr m)
    (in2 in3 out0 out1 : Fin W → Bool) : Prop :=
  let item := if c = 0 then in2 else if s (c - 1) (P1Net.Routing.rep m (c - 1) a) then in3 else in2
  if c + 1 = 2 * m then out0 = item
  else if s c (P1Net.Routing.rep m c a) then out1 = item ∧ out0 = fun _ => false
  else out0 = item ∧ out1 = fun _ => false

section Butterfly

variable {m W : ℕ} [NeZero m]

/-- The item that `routeOK` reads at position `(c, a)`: the word of the selected in-arc (in-slot `3` = cross,
in-slot `2` = straight, selected by the switch of stage `c - 1`); at column `0` the source word (in-slot `2`). -/
def rtItem (s : P1Net.Routing.Settings m) (in2 in3 : ℕ → P1Net.Routing.Addr m → Fin W → Bool) (c : ℕ)
    (a : P1Net.Routing.Addr m) : Fin W → Bool :=
  if c = 0 then in2 c a else if s (c - 1) (P1Net.Routing.rep m (c - 1) a) then in3 c a else in2 c a

theorem routeOKNet_iff (s : P1Net.Routing.Settings m) (in2 in3 out0 out1 : ℕ → P1Net.Routing.Addr m → Fin W → Bool)
    (c : ℕ) (a : P1Net.Routing.Addr m) :
    routeOKNet s c a (in2 c a) (in3 c a) (out0 c a) (out1 c a) ↔
      if c + 1 = 2 * m then out0 c a = rtItem s in2 in3 c a
      else if s c (P1Net.Routing.rep m c a) = true then
        out1 c a = rtItem s in2 in3 c a ∧ out0 c a = fun _ => false
      else out0 c a = rtItem s in2 in3 c a ∧ out1 c a = fun _ => false :=
  Iff.rfl

/-- Out-arc `b` (`false` = straight = out-slot `0`, `true` = cross = out-slot `1`) of position `(c, a)`. -/
def bfArc (out0 out1 : ℕ → P1Net.Routing.Addr m → Fin W → Bool) (c : ℕ) (a : P1Net.Routing.Addr m) :
    Bool → Fin W → Bool
  | false => out0 c a
  | true => out1 c a

/-- **A run of the butterfly** (columns `c < 2m`, addresses `a`; words: in-slot `2` straight, in-slot `3` cross,
out-slot `0` straight, out-slot `1` cross). The in-words of column `c + 1` are the out-words of their mates
(straight: out-slot `0` of `(c, a)`; cross: out-slot `1` of `(c, a + flip c)`; in lane net this is
`P1Net.zIn_mate` with `netMate_rt2` / `netMate_rt3` and `addrOf_add_flip`), and every position satisfies
`routeOK` (`P1Net.rt_routeOK`). -/
def IsRun (s : P1Net.Routing.Settings m) (in2 in3 out0 out1 : ℕ → P1Net.Routing.Addr m → Fin W → Bool) :
    Prop :=
  (∀ c a, c + 1 < 2 * m → in2 (c + 1) a = out0 c a) ∧
  (∀ c a, c + 1 < 2 * m → in3 (c + 1) a = out1 c (a + P1Net.Routing.flip m c)) ∧
  (∀ c a, c < 2 * m → routeOKNet s c a (in2 c a) (in3 c a) (out0 c a) (out1 c a))

/-- The canonical out-words with sources `src`: at a column `c < 2m - 1` the canonical run (zero on the unselected
out-arc); at the last column the item on out-slot `0` and zero on out-slot `1`. -/
def canonOut (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) (b : Bool) (c : ℕ)
    (a : P1Net.Routing.Addr m) : Fin W → Bool :=
  if c + 1 = 2 * m then
    (match b with
      | false => runPos s src c a
      | true => fun _ => false)
  else runArc s (fun _ => false) src c a b

/-- The canonical in-words of slot `2`: the source at column `0`, the mate's out-word after. -/
def canonIn2 (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) (c : ℕ)
    (a : P1Net.Routing.Addr m) : Fin W → Bool :=
  if c = 0 then src a else canonOut s src false (c - 1) a

/-- The canonical in-words of slot `3`: zero at column `0`, the mate's out-word after. -/
def canonIn3 (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) (c : ℕ)
    (a : P1Net.Routing.Addr m) : Fin W → Bool :=
  if c = 0 then fun _ => false else canonOut s src true (c - 1) (a + P1Net.Routing.flip m (c - 1))

theorem canonOut_last {s : P1Net.Routing.Settings m} {src : P1Net.Routing.Addr m → Fin W → Bool} {c : ℕ}
    (a : P1Net.Routing.Addr m) (hl : c + 1 = 2 * m) : canonOut s src false c a = runPos s src c a := by
  unfold canonOut
  rw [if_pos hl]
  try rfl

theorem canonOut_mid {s : P1Net.Routing.Settings m} {src : P1Net.Routing.Addr m → Fin W → Bool} {c : ℕ}
    (b : Bool) (a : P1Net.Routing.Addr m) (hl : c + 1 ≠ 2 * m) :
    canonOut s src b c a = runArc s (fun _ => false) src c a b := by
  unfold canonOut
  rw [if_neg hl]

theorem rtItem_canon (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) (c : ℕ)
    (a : P1Net.Routing.Addr m) (hc : c < 2 * m) :
    rtItem s (canonIn2 s src) (canonIn3 s src) c a = runPos s src c a := by
  rcases c with _ | c
  · rfl
  · have h0 : c + 1 ≠ 0 := by omega
    have hl : c + 1 ≠ 2 * m := by omega
    rw [runPos_succ_stage]
    unfold rtItem canonIn2 canonIn3 canonOut
    rw [if_neg h0, if_neg h0, if_neg h0, Nat.add_sub_cancel, if_neg hl, if_neg hl]
    unfold runArc P1Net.Routing.stage
    by_cases hs : s c (P1Net.Routing.rep m c a) = true
    · rw [if_pos hs, P1Net.Routing.rep_add_flip, if_pos hs.symm, if_pos hs]
    · have hs' : s c (P1Net.Routing.rep m c a) = false := by simpa using hs
      rw [if_neg hs, if_neg hs, if_pos hs'.symm]

/-- **Existence.** The canonical words form a run with sources `src`. -/
theorem canon_isRun (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) :
    IsRun s (canonIn2 s src) (canonIn3 s src) (canonOut s src false) (canonOut s src true) := by
  unfold IsRun
  refine ⟨fun c a _ => ?_, fun c a _ => ?_, fun c a hc => ?_⟩
  · have h0 : c + 1 ≠ 0 := by omega
    unfold canonIn2
    rw [if_neg h0, Nat.add_sub_cancel]
  · have h0 : c + 1 ≠ 0 := by omega
    unfold canonIn3
    rw [if_neg h0, Nat.add_sub_cancel]
  · rw [routeOKNet_iff s (canonIn2 s src) (canonIn3 s src) (canonOut s src false) (canonOut s src true) c a,
      rtItem_canon s src c a hc]
    by_cases hl : c + 1 = 2 * m
    · rw [if_pos hl]
      exact canonOut_last a hl
    · rw [if_neg hl, canonOut_mid false a hl, canonOut_mid true a hl]
      have e1 := runArc_sel s (fun _ => false : Fin W → Bool) src c a
      have e2 := runArc_unsel s (fun _ => false : Fin W → Bool) src c a
      by_cases hs : s c (P1Net.Routing.rep m c a) = true
      · rw [if_pos hs]
        rw [hs] at e1 e2
        exact ⟨e1, e2⟩
      · have hs' : s c (P1Net.Routing.rep m c a) = false := by simpa using hs
        rw [if_neg hs]
        rw [hs'] at e1 e2
        exact ⟨e1, e2⟩

theorem canonIn2_zero (s : P1Net.Routing.Settings m) (src : P1Net.Routing.Addr m → Fin W → Bool) :
    canonIn2 s src 0 = src := rfl

/-- **Uniqueness.** Every run equals the canonical words of its sources `in2 0`, except the two words that
`routeOK` does not constrain (out-slot `1` of the last column, in-slot `3` of column `0`). -/
theorem IsRun.eq_canon {s : P1Net.Routing.Settings m} {in2 in3 out0 out1 : ℕ → P1Net.Routing.Addr m → Fin W → Bool}
    (h : IsRun s in2 in3 out0 out1) :
    (∀ c a, c + 1 < 2 * m →
      out0 c a = canonOut s (in2 0) false c a ∧ out1 c a = canonOut s (in2 0) true c a) ∧
    (∀ a, out0 (2 * m - 1) a = canonOut s (in2 0) false (2 * m - 1) a) ∧
    (∀ c a, 0 < c → c < 2 * m → in2 c a = canonIn2 s (in2 0) c a ∧ in3 c a = canonIn3 s (in2 0) c a) := by
  obtain ⟨hm2, hm3, hok⟩ := h
  have hm0 : m ≠ 0 := NeZero.ne m
  have hout : ∀ κ < 2 * m - 1, ∀ a,
      bfArc out0 out1 κ a (s κ (P1Net.Routing.rep m κ a)) = rtItem s in2 in3 κ a := by
    intro κ hκ a
    have hr := (routeOKNet_iff s in2 in3 out0 out1 κ a).1 (hok κ a (by omega))
    rw [if_neg (show κ + 1 ≠ 2 * m by omega)] at hr
    by_cases hs : s κ (P1Net.Routing.rep m κ a) = true
    · rw [if_pos hs] at hr
      rw [hs]
      exact hr.1
    · have hs' : s κ (P1Net.Routing.rep m κ a) = false := by simpa using hs
      rw [if_neg hs] at hr
      rw [hs']
      exact hr.1
  have hz : ∀ κ < 2 * m - 1, ∀ a,
      bfArc out0 out1 κ a (!s κ (P1Net.Routing.rep m κ a)) = fun _ => false := by
    intro κ hκ a
    have hr := (routeOKNet_iff s in2 in3 out0 out1 κ a).1 (hok κ a (by omega))
    rw [if_neg (show κ + 1 ≠ 2 * m by omega)] at hr
    by_cases hs : s κ (P1Net.Routing.rep m κ a) = true
    · rw [if_pos hs] at hr
      rw [hs]
      exact hr.2
    · have hs' : s κ (P1Net.Routing.rep m κ a) = false := by simpa using hs
      rw [if_neg hs] at hr
      rw [hs']
      exact hr.2
  have hin : ∀ κ < 2 * m - 1, ∀ a', rtItem s in2 in3 (κ + 1) a' =
      bfArc out0 out1 κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a')) := by
    intro κ hκ a'
    have h0 : κ + 1 ≠ 0 := by omega
    unfold rtItem P1Net.Routing.stage
    rw [if_neg h0, Nat.add_sub_cancel]
    by_cases hs : s κ (P1Net.Routing.rep m κ a') = true
    · rw [if_pos hs, if_pos hs, hs]
      exact hm3 κ a' (by omega)
    · have hs' : s κ (P1Net.Routing.rep m κ a') = false := by simpa using hs
      rw [if_neg hs, if_neg hs, hs']
      exact hm2 κ a' (by omega)
  have hp0 : rtItem s in2 in3 0 = in2 0 := rfl
  have hp := eq_run_le s (rtItem s in2 in3) (bfArc out0 out1) (2 * m - 1) hout hin
  have ha := arc_eq_run_le s (fun _ => false) (rtItem s in2 in3) (bfArc out0 out1) (2 * m - 1) hout hin hz
  rw [hp0] at hp ha
  have hmid : ∀ c a, c + 1 < 2 * m →
      out0 c a = canonOut s (in2 0) false c a ∧ out1 c a = canonOut s (in2 0) true c a := by
    intro c a hc
    have e := ha c (by omega)
    have hl : c + 1 ≠ 2 * m := by omega
    rw [canonOut_mid false a hl, canonOut_mid true a hl]
    exact ⟨congrFun (congrFun e a) false, congrFun (congrFun e a) true⟩
  refine ⟨hmid, fun a => ?_, fun c a hc0 hc => ?_⟩
  · have hr := (routeOKNet_iff s in2 in3 out0 out1 (2 * m - 1) a).1 (hok (2 * m - 1) a (by omega))
    have hl : 2 * m - 1 + 1 = 2 * m := by omega
    rw [if_pos hl] at hr
    rw [hr, hp (2 * m - 1) le_rfl, canonOut_last a hl]
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have h0 : c + 1 ≠ 0 := by omega
    have hc' : c + 1 < 2 * m := hc
    unfold canonIn2 canonIn3
    rw [if_neg h0, if_neg h0, Nat.add_sub_cancel, hm2 c a hc', hm3 c a hc']
    exact ⟨(hmid c a hc').1, (hmid c (a + P1Net.Routing.flip m c) hc').2⟩

/-- **Uniqueness, two runs.** Two runs with the same sources agree on every constrained word. -/
theorem IsRun.unique {s : P1Net.Routing.Settings m}
    {in2 in3 out0 out1 in2' in3' out0' out1' : ℕ → P1Net.Routing.Addr m → Fin W → Bool}
    (h : IsRun s in2 in3 out0 out1) (h' : IsRun s in2' in3' out0' out1') (h0 : in2 0 = in2' 0) :
    (∀ c a, c + 1 < 2 * m → out0 c a = out0' c a ∧ out1 c a = out1' c a) ∧
    (∀ a, out0 (2 * m - 1) a = out0' (2 * m - 1) a) ∧
    (∀ c a, 0 < c → c < 2 * m → in2 c a = in2' c a ∧ in3 c a = in3' c a) := by
  obtain ⟨e1, e2, e3⟩ := h.eq_canon
  obtain ⟨f1, f2, f3⟩ := h'.eq_canon
  rw [h0] at e1 e2 e3
  refine ⟨fun c a hc => ?_, fun a => ?_, fun c a hc0 hc => ?_⟩
  · rw [(e1 c a hc).1, (e1 c a hc).2, (f1 c a hc).1, (f1 c a hc).2]
    exact ⟨rfl, rfl⟩
  · rw [e2 a, f2 a]
  · rw [(e3 c a hc0 hc).1, (e3 c a hc0 hc).2, (f3 c a hc0 hc).1, (f3 c a hc0 hc).2]
    exact ⟨rfl, rfl⟩

/-- **Delivery.** In a run the destination `route s a` (out-slot `0` of the last column) receives the source word
of `a` (in-slot `2` of column `0`). -/
theorem IsRun.deliver {s : P1Net.Routing.Settings m}
    {in2 in3 out0 out1 : ℕ → P1Net.Routing.Addr m → Fin W → Bool} (h : IsRun s in2 in3 out0 out1)
    (a : P1Net.Routing.Addr m) : out0 (2 * m - 1) (P1Net.Routing.route s a) = in2 0 a := by
  have hm0 : m ≠ 0 := NeZero.ne m
  rw [h.eq_canon.2.1, canonOut_last _ (show 2 * m - 1 + 1 = 2 * m by omega)]
  exact runPos_route s (in2 0) a

end Butterfly

end P1Benes.NetBridge
