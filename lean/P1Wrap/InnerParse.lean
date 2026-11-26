import P1Wrap.ParamTask
import P1Wrap.InnerSpec

/-!
# Piece B of W3: the parser `pF` of the inner verifier, in linear time

`pF j a b n₁ z = (ok, x, u, γ)` on the raw verifier input `z = withGuess w y`:
`ok` says that `y = 1^n 0 x u 0^{padLen}` with `|x| = n ≥ n₁` and `|u| = m(n)`; then `x`, `u` are these words and
`γ = w.take k(n)`.

* `easy_pF (hUG : Easy unG) : Easy (pF j a b n₁)` (uses `PT.paramM`, `PT.paramK`; `unG` is the text of
  `P1Hier.UM.unGuess`, lane hier B proves `Easy unGuess` as its input h1).
* `pF_valid`: on a valid padded word, `pF = (true, x, u, w.take k)`.
* `pF_ok`: `ok = true` only on a valid padded word.
-/

namespace P1Wrap.W3.Inner

open P1Int C1Challenge P1Wrap.W3 P1Wrap.W3.PT
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Splitting the verifier input -/

/-- Split a verifier input into guess and input (text of `P1Hier.UM.unGuess`). -/
def unG : List Bool → List Bool × List Bool
  | true :: b :: r => (b :: (unG r).1, (unG r).2)
  | false :: r => ([], r)
  | _ => ([], [])

theorem unG_withGuess (u x : List Bool) : unG (withGuess u x) = (u, x) := by
  induction u with
  | nil => simp [withGuess, unG]
  | cons b r ih =>
    have h : withGuess (b :: r) x = true :: b :: withGuess r x := by simp [withGuess]
    rw [h]
    simp [unG, ih]

/-! ## Two transducers -/

def onesStep (b : Bool) (s : Bool) : Bool × List Unit := if s && b then (true, [()]) else (false, [])

/-- The number of leading `true`s, unary. -/
def ones (y : List Bool) : Tally := (machine onesStep (y, true)).1

theorem machine_ones_false : ∀ r : List Bool, (machine onesStep (r, false)).1 = []
  | [] => rfl
  | b :: r => by
      rw [machine_cons]
      simp only [onesStep, Bool.false_and, Bool.false_eq_true, if_false]
      rw [machine_ones_false r]
      rfl

theorem ones_true (l : List Bool) : ones (true :: l) = () :: ones l := by
  unfold ones
  rw [machine_cons]
  simp only [onesStep, Bool.and_self, if_true]
  rfl

theorem ones_false (l : List Bool) : ones (false :: l) = [] := by
  unfold ones
  rw [machine_cons]
  simp only [onesStep, Bool.and_false, Bool.false_eq_true, if_false]
  rw [machine_ones_false]
  rfl

theorem ones_nil : ones [] = [] := rfl

theorem ones_rep (n : ℕ) (r : List Bool) : ones (List.replicate n true ++ false :: r) = tally n := by
  induction n with
  | zero => simp [ones_false, tally]
  | succ n ih => rw [List.replicate_succ, List.cons_append, ones_true, ih, tally_succ]

theorem ones_spec : ∀ y : List Bool,
    y = List.replicate (ones y).length true ++ y.drop (ones y).length ∧
      (y.drop (ones y).length).head? ≠ some true
  | [] => by simp [ones_nil]
  | false :: l => by simp [ones_false]
  | true :: l => by
      obtain ⟨h1, h2⟩ := ones_spec l
      rw [ones_true, List.length_cons, List.replicate_succ, List.drop_succ_cons]
      exact ⟨by rw [List.cons_append, ← h1], h2⟩

theorem easy_ones : Easy ones := by
  have h : Easy (fun y : List Bool => (y, true)) := Easy.pair easy_id (Easy.const true)
  exact (Easy.machine (step := onesStep) h).fstCompose

def afStep (b : Bool) (s : Bool) : Bool × List Unit := (s && !b, [])

/-- All letters are `false`. -/
def allF (l : List Bool) : Bool := (machine afStep (l, true)).2

theorem machine_af : ∀ (l : List Bool) (s : Bool),
    (machine afStep (l, s)).2 = (s && l.all fun b => !b)
  | [], s => by simp [machine_nil]
  | b :: l, s => by
      rw [machine_cons]
      simp only [afStep]
      rw [machine_af l]
      cases s <;> cases b <;> simp

theorem allF_iff (l : List Bool) : allF l = true ↔ l = List.replicate l.length false := by
  unfold allF
  rw [machine_af, Bool.true_and, List.all_eq_true, List.eq_replicate_iff]
  simp

theorem easy_allF : Easy allF := by
  have h : Easy (fun y : List Bool => (y, true)) := Easy.pair easy_id (Easy.const true)
  exact (Easy.machine (step := afStep) h).sndCompose

/-! ## The parser -/

noncomputable section Parser
variable (j a b n₁ : ℕ)

def pW (z : List Bool) : List Bool := (unG z).1
def pY (z : List Bool) : List Bool := (unG z).2
def pN (z : List Bool) : Tally := ones (pY z)
def pY1 (z : List Bool) : List Bool := (cutLists (pN z, pY z)).2
def pY2 (z : List Bool) : List Bool := (cutLists (tally 1, pY1 z)).2
def pX (z : List Bool) : List Bool := (cutLists (pN z, pY2 z)).1
def pY3 (z : List Bool) : List Bool := (cutLists (pN z, pY2 z)).2
def pM (z : List Bool) : Tally := tally (mCheck j a b (pN z).length (ruler (pY3 z)).length)
def pU (z : List Bool) : List Bool := (cutLists (pM j a b z, pY3 z)).1
def pZ (z : List Bool) : List Bool := (cutLists (pM j a b z, pY3 z)).2
def pG (z : List Bool) : List Bool := (cutLists (tally (lpK2 a b (pN z).length), pW z)).1

def okOf (t : Bool × Bool × Bool × Bool × Bool) : Bool := t.1 && t.2.1 && t.2.2.1 && t.2.2.2.1 && t.2.2.2.2

def pOk (z : List Bool) : Bool :=
  okOf (!((pY1 z).headD true), !(Iter.small (pY2 z, pN z)), Iter.small (([] : Tally), pM j a b z),
    allF (pZ j a b z), !(Iter.small (pN z, tally n₁)))

/-- The parser of the inner verifier. -/
def pF (z : List Bool) : Bool × List Bool × List Bool × List Bool :=
  (pOk j a b n₁ z, pX z, pU j a b z, pG a b z)

end Parser

section EasyParser
variable (hUG : Easy unG) (j a b n₁ : ℕ)
include hUG

theorem easy_pW : Easy pW := hUG.fstCompose
theorem easy_pY : Easy pY := hUG.sndCompose
theorem easy_pN : Easy pN := (easy_pY hUG).compose easy_ones
theorem easy_pY1 : Easy pY1 := (easy_cut ((easy_pN hUG).pair (easy_pY hUG))).sndCompose
theorem easy_pY2 : Easy pY2 := (easy_cut ((Easy.const (tally 1)).pair (easy_pY1 hUG))).sndCompose
theorem easy_pX : Easy pX := (easy_cut ((easy_pN hUG).pair (easy_pY2 hUG))).fstCompose
theorem easy_pY3 : Easy pY3 := (easy_cut ((easy_pN hUG).pair (easy_pY2 hUG))).sndCompose

theorem easy_pM : Easy (pM j a b) := by
  have h : Easy (fun z => (pN z, ruler (pY3 z))) := (easy_pN hUG).pair (Easy.ruler (easy_pY3 hUG))
  exact h.compose (paramM j a b)

theorem easy_pU : Easy (pU j a b) := (easy_cut ((easy_pM hUG j a b).pair (easy_pY3 hUG))).fstCompose
theorem easy_pZ : Easy (pZ j a b) := (easy_cut ((easy_pM hUG j a b).pair (easy_pY3 hUG))).sndCompose

theorem easy_pG : Easy (pG a b) := by
  have h : Easy (fun z => tally (lpK2 a b (pN z).length)) := (easy_pN hUG).compose (paramK a b)
  exact (easy_cut (h.pair (easy_pW hUG))).fstCompose

theorem easy_pOk : Easy (pOk j a b n₁) := by
  have nt : Easy (fun v : Bool => !v) := Easy.finite _
  have o1 : Easy (fun z => !((pY1 z).headD true)) :=
    ((easy_pY1 hUG).compose (Iter.leader true)).compose nt
  have o2 : Easy (fun z => !(Iter.small (pY2 z, pN z))) :=
    (((easy_pY2 hUG).pair (easy_pN hUG)).compose Iter.small_easy).compose nt
  have o3 : Easy (fun z => Iter.small (([] : Tally), pM j a b z)) :=
    ((Easy.const ([] : Tally)).pair (easy_pM hUG j a b)).compose Iter.small_easy
  have o4 : Easy (fun z => allF (pZ j a b z)) := (easy_pZ hUG j a b).compose easy_allF
  have o5 : Easy (fun z => !(Iter.small (pN z, tally n₁))) :=
    (((easy_pN hUG).pair (Easy.const (tally n₁))).compose Iter.small_easy).compose nt
  exact (o1.pair (o2.pair (o3.pair (o4.pair o5)))).compose (Easy.finite okOf)

theorem easy_pF : Easy (pF j a b n₁) :=
  (easy_pOk hUG j a b n₁).pair ((easy_pX hUG).pair ((easy_pU hUG j a b).pair (easy_pG hUG a b)))

end EasyParser

/-! ## Correctness of the parser -/

theorem lpM2_pos (j a b n : ℕ) : 0 < lpM2 (sOf j) a b n := by
  unfold lpM2
  apply Nat.mul_pos (by positivity)
  have h1 : 1 ≤ lpTime a b n := by unfold lpTime; omega
  have h2 : 0 < 2 ^ lpT2 (sOf j) a b n := by positivity
  apply Nat.div_pos _ h2
  omega

theorem mCheck_eq (j a b n : ℕ) :
    mCheck j a b n (lpM2 (sOf j) a b n + padLen j a b n) = lpM2 (sOf j) a b n := by
  unfold mCheck padLen
  rw [if_pos (by ring)]

theorem pF_valid (j a b n₁ : ℕ) {x u : List Bool} (hx : n₁ ≤ x.length)
    (hu : u.length = lpM2 (sOf j) a b x.length) (w : List Bool) :
    pF j a b n₁ (withGuess w (padIn j a b x u)) = (true, x, u, w.take (lpK2 a b x.length)) := by
  set n := x.length with hn
  set m := lpM2 (sOf j) a b n with hm
  set P := padLen j a b n with hP
  have eY : pY (withGuess w (padIn j a b x u)) =
      List.replicate n true ++ false :: (x ++ (u ++ List.replicate P false)) := by
    simp [pY, unG_withGuess, padIn, hn, hP, List.append_assoc]
  have eW : pW (withGuess w (padIn j a b x u)) = w := by simp [pW, unG_withGuess]
  have eN : pN (withGuess w (padIn j a b x u)) = tally n := by rw [pN, eY, ones_rep]
  have eY1 : pY1 (withGuess w (padIn j a b x u)) = false :: (x ++ (u ++ List.replicate P false)) := by
    rw [pY1, eN, eY]
    simp [cutLists]
  have eY2 : pY2 (withGuess w (padIn j a b x u)) = x ++ (u ++ List.replicate P false) := by
    rw [pY2, eY1]; simp [cutLists]
  have eX : pX (withGuess w (padIn j a b x u)) = x := by
    rw [pX, eN, eY2]; simp [cutLists, hn]
  have eY3 : pY3 (withGuess w (padIn j a b x u)) = u ++ List.replicate P false := by
    rw [pY3, eN, eY2]; simp [cutLists, hn]
  have eM : pM j a b (withGuess w (padIn j a b x u)) = tally m := by
    rw [pM, eN, eY3]
    simp only [ruler_length, List.length_append, List.length_replicate, tally_length, hu]
    rw [mCheck_eq]
  have eU : pU j a b (withGuess w (padIn j a b x u)) = u := by
    rw [pU, eM, eY3]; simp [cutLists, hu, hm]
  have eZ : pZ j a b (withGuess w (padIn j a b x u)) = List.replicate P false := by
    rw [pZ, eM, eY3]; simp [cutLists, hu, hm]
  have eG : pG a b (withGuess w (padIn j a b x u)) = w.take (lpK2 a b n) := by
    rw [pG, eN, eW]; simp [cutLists]
  have eOk : pOk j a b n₁ (withGuess w (padIn j a b x u)) = true := by
    have hm0 : 0 < m := lpM2_pos j a b n
    have hz : allF (List.replicate P false) = true := by
      rw [allF_iff]; simp
    rw [pOk, eY1, eY2, eN, eM, eZ, hz]
    simp [okOf, Iter.small, tally_length, hm0]
    omega
  rw [pF, eOk, eX, eU, eG]

theorem pF_ok (j a b n₁ : ℕ) (z : List Bool) (h : pOk j a b n₁ z = true) :
    ∃ x u : List Bool, n₁ ≤ x.length ∧ u.length = lpM2 (sOf j) a b x.length ∧
      pY z = padIn j a b x u := by
  simp only [pOk, okOf, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  set y := pY z with hy
  set n := (pN z).length with hn
  obtain ⟨hy1, hy2⟩ := ones_spec y
  have hpN : pN z = ones y := rfl
  rw [← hpN, ← hn] at hy1 hy2
  -- the letter after the ones is `false`
  have eY1 : pY1 z = y.drop n := by simp [pY1, cutLists, hy, hn]
  rw [eY1] at h1
  obtain ⟨y2, hy2'⟩ : ∃ y2, y.drop n = false :: y2 := by
    cases hd : y.drop n with
    | nil => rw [hd] at h1; simp at h1
    | cons c t =>
      cases c
      · exact ⟨t, rfl⟩
      · rw [hd] at h1; simp at h1
  have eY2 : pY2 z = y2 := by simp [pY2, eY1, hy2', cutLists]
  rw [eY2] at h2
  have hn2 : n ≤ y2.length := by
    simp only [Iter.small, decide_eq_false_iff_not, not_lt] at h2
    rw [← hn] at h2; exact h2
  set x := y2.take n with hx
  set y3 := y2.drop n with hy3
  have hxl : x.length = n := by simp [hx]; omega
  have eY3 : pY3 z = y3 := by simp [pY3, eY2, cutLists, hy3, hn]
  -- the parameter test
  have eM : pM j a b z = tally (mCheck j a b n y3.length) := by simp [pM, eY3, hn]
  rw [eM] at h3
  simp only [Iter.small, List.length_nil, tally_length, decide_eq_true_eq] at h3
  have hmc : (lpP2 a b n + 2) * lpM2 (sOf j) a b n = y3.length := by
    by_contra hc
    unfold mCheck at h3
    rw [if_neg hc] at h3
    omega
  have hmv : mCheck j a b n y3.length = lpM2 (sOf j) a b n := by unfold mCheck; rw [if_pos hmc]
  set m := lpM2 (sOf j) a b n with hm
  have eM' : pM j a b z = tally m := by rw [eM, hmv]
  set u := y3.take m with hu
  set zr := y3.drop m with hzr
  have hm3 : m ≤ y3.length := by rw [← hmc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hul : u.length = m := by simp [hu]; omega
  have hzl : zr.length = padLen j a b n := by
    simp only [hzr, List.length_drop, ← hmc]
    unfold padLen
    rw [← hm]
    ring_nf
    omega
  have eZ : pZ j a b z = zr := by simp [pZ, eM', eY3, cutLists, hzr]
  rw [eZ, allF_iff, hzl] at h4
  have h5' : n₁ ≤ n := by
    simp only [Iter.small, tally_length, decide_eq_false_iff_not, not_lt] at h5
    rw [← hn] at h5; exact h5
  refine ⟨x, u, by omega, by rw [hul, hxl], ?_⟩
  have e1 : y = List.replicate n true ++ y.drop n := hy1
  rw [hy2'] at e1
  have e2 : y2 = x ++ y3 := (List.take_append_drop n y2).symm
  have e3 : y3 = u ++ zr := (List.take_append_drop m y3).symm
  rw [e1, e2, e3, h4]
  unfold padIn
  rw [hxl, List.append_assoc]

end P1Wrap.W3.Inner
