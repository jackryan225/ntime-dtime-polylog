import P1ProgDir.Signed
import P1ProgDir.SweepSpec
import OAI.Computability.IntegerMultiplication.Code.FoldLeft

namespace P1ProgDir.SolIndexedSweep

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolSigned P1ProgDir.SolSweepSpec

variable {Y A : Type} [Codec Y] [Codec A]

abbrev Context (Y : Type) := Tally × Y
abbrev Acc (Y : Type) := Context Y × Word × Bool

def step (test : Y × Word × A → Bool) (p : A × Acc Y) : Acc Y :=
  (p.2.1, resize (p.2.1.1, incMagnitude p.2.2.1),
    p.2.2.2 && test (p.2.1.2, p.2.2.1, p.1))

theorem easy_step (test : Y × Word × A → Bool) (htest : Easy test) : Easy (step test) := by
  let P := A × Acc Y
  have hctx : Easy (fun p : P => p.2.1) := Easy.snd.compose Easy.fst
  have hctr : Easy (fun p : P => p.2.2.1) := Easy.snd.compose (Easy.snd.compose Easy.fst)
  have hok : Easy (fun p : P => p.2.2.2) := Easy.snd.compose (Easy.snd.compose Easy.snd)
  have ht := ((hctx.compose Easy.snd).pair (hctr.pair Easy.fst)).compose htest
  exact hctx.pair ((easy_resize ((hctx.compose Easy.fst).pair (hctr.compose easy_incMagnitude))).pair
    ((hok.pair ht).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2))))

def initial (ctx : Context Y) : Acc Y := (ctx, fill false ctx.1, true)

theorem easy_initial : Easy (initial : Context Y → Acc Y) :=
  Easy.identity.pair ((easy_fill false Easy.fst).pair (Easy.const true))

def run (test : Y × Word × A → Bool) (p : List A × Context Y) : Bool :=
  (p.1.foldl (fun acc row => step test (row, acc)) (initial p.2)).2.2

private theorem tally_length_eq (r : Tally) : tally r.length = r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases a
    change () :: tally r.length = () :: r
    rw [ih]

theorem resize_length_eq (r : Tally) (w : Word) : (resize (r, w)).length = r.length := by
  calc
    _ = (sized r.length w).length := by rw [sized, tally_length_eq]
    _ = _ := sized_length _ _

theorem resize_low (r : Tally) (w : Word) (h : value w < 2 ^ r.length) :
    value (resize (r, w)) = value w := by
  simpa only [sized, tally_length_eq, Nat.mod_eq_of_lt h] using sized_low r.length w

theorem resize_of_length (r : Tally) (w : Word) (h : w.length = r.length) :
    resize (r, w) = w := by
  simpa only [resize, cutLists, ← h] using List.take_left (l₁ := w) (l₂ := fill false r)

theorem fill_false_length (r : Tally) : (fill false r).length = r.length := by
  induction r with
  | nil => rfl
  | cons _ r ih => exact congrArg Nat.succ ih

theorem value_fill_false (r : Tally) : value (fill false r) = 0 := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    change value (false :: fill false r) = 0
    rw [value_cons, d0, ih]

theorem fold_agrees (test : Y × Word × A → Bool) (testNat : ℕ → A → Bool)
    (rows : List A) (ctx : Context Y)
    (h : ∀ w row, test (ctx.2, w, row) = testNat (value w) row)
    (ctr : Word) (ok : Bool) (hcap : value ctr + rows.length < 2 ^ ctx.1.length) :
    (rows.foldl (fun acc row => step test (row, acc)) (ctx, ctr, ok)).2.2 =
      (sweep testNat rows (value ctr) ok).2 := by
  induction rows generalizing ctr ok with
  | nil => rfl
  | cons row rows ih =>
    let next := resize (ctx.1, incMagnitude ctr)
    have hc : value (incMagnitude ctr) < 2 ^ ctx.1.length := by
      rw [incMagnitude_value]
      simp only [List.length_cons] at hcap
      omega
    have hn : value next = value ctr + 1 := (resize_low _ _ hc).trans (incMagnitude_value ctr)
    simp only [List.foldl_cons, step, h]
    change (rows.foldl (fun acc row => step test (row, acc)) (ctx, next, ok && testNat (value ctr) row)).2.2 =
      (sweep testNat rows (value ctr + 1) (ok && testNat (value ctr) row)).2
    rw [ih _ _ (by rw [hn]; simp only [List.length_cons] at hcap; omega), hn]

theorem run_iff (test : Y × Word × A → Bool) (testNat : ℕ → A → Bool)
    (rows : List A) (ctx : Context Y)
    (h : ∀ w row, test (ctx.2, w, row) = testNat (value w) row)
    (hcap : rows.length < 2 ^ ctx.1.length) :
    run test (rows, ctx) = true ↔ ∀ j : Fin rows.length, testNat j.val rows[j] = true := by
  unfold run initial
  rw [fold_agrees test testNat rows ctx h _ _ (by simpa only [value_fill_false, Nat.zero_add]),
    value_fill_false, sweep_correct]
  simp only [true_and, Nat.zero_add]

/-- One scan charging a fixed-size context and index per row. -/
theorem task (test : Y × Word × A → Bool) (htest : Easy test) :
    Computes (fun p : List A × Context Y =>
      size p.1 + (p.1.length + 1) * (size p.2 + 2 * p.2.1.length + 5)) (run test) := by
  let normalize (ctx : Context Y) (acc : Word × Bool) : Acc Y :=
    (ctx, resize (ctx.1, acc.1), acc.2)
  let next (ctx : Context Y) (acc : Word × Bool) (row : A) : Word × Bool :=
    (step test (row, normalize ctx acc)).2
  let a (ctx : Context Y) (row : A) := size row + size ctx + 2 * ctx.1.length + 5
  let D (_ : Context Y) (_ : A) := True
  have hb (b : Bool) : size b = 1 := by cases b <;> rfl
  have hnorm (ctx : Context Y) (p : A) (z : Word × Bool) :
      step test (p, normalize ctx z) = normalize ctx (next ctx z p) := by
    have e := resize_of_length ctx.1 (resize (ctx.1, incMagnitude (resize (ctx.1, z.1))))
        (resize_length_eq _ _)
    simp only [step, normalize, next, e]
  have hsize (ctx : Context Y) (z : Word × Bool) :
      size (normalize ctx z) = size ctx + 2 * ctx.1.length + 4 := by
    simp only [normalize, size_prod, size_word, hb, resize_length_eq]
    omega
  have hstep : Task (fun p : {p : A × (Word × Bool) × Context Y // D p.2.2 p.1} => a p.val.2.2 p.val.1)
      (fun p => send (p.val.1, normalize p.val.2.2 p.val.2.1))
      (fun p => send (normalize p.val.2.2 (next p.val.2.2 p.val.2.1 p.val.1))) := by
    refine ((easy_step test htest).on
      (fun p : {p : A × (Word × Bool) × Context Y // D p.2.2 p.1} =>
        (p.val.1, normalize p.val.2.2 p.val.2.1))).conform ?_ (fun _ => rfl) ?_
    · intro p
      change size (p.val.1, normalize p.val.2.2 p.val.2.1) = a p.val.2.2 p.val.1
      simp only [size_prod, hsize, a]
      omega
    · intro p
      exact congrArg send (hnorm _ _ _)
  let P := List A × Context Y
  let seed (p : P) : Word × Bool := (fill false p.2.1, true)
  let arg (p : P) : {s : List A × (Word × Bool) × Context Y // ∀ v ∈ s.1, D s.2.2 v} :=
    ⟨(p.1, seed p, p.2), fun _ _ => trivial⟩
  let out (p : P) := normalize p.2 (p.1.foldl (next p.2) (seed p))
  have hseed (p : P) : normalize p.2 (seed p) = initial p.2 := by
    simp only [normalize, seed, initial, resize_of_length _ _ (fill_false_length _)]
  have hfold (rows : List A) (ctx : Context Y) (z : Word × Bool) :
      normalize ctx (rows.foldl (next ctx) z) =
        rows.foldl (fun acc row => step test (row, acc)) (normalize ctx z) := by
    induction rows generalizing z with
    | nil => rfl
    | cons row rows ih =>
      simp only [List.foldl_cons, ih, hnorm]
  have hcost (rows : List A) (ctx : Context Y) :
      costSum (a ctx) rows ≤ size rows + rows.length * (size ctx + 2 * ctx.1.length + 5) := by
    induction rows with
    | nil => simp only [costSum_nil, size_nil, List.length_nil, Nat.zero_mul]; omega
    | cons row rows ih =>
      rw [costSum_cons, size_cons, List.length_cons, Nat.succ_mul]
      change size row + size ctx + 2 * ctx.1.length + 5 + costSum (a ctx) rows ≤ _
      omega
  have h₁ := (easy_initial.on (Prod.snd : P → Context Y)).right (fun p => send p.1)
  have h₂ := (Task.foldLeft (fun _ x => send x) (fun ctx z => send (normalize ctx z))
    next a hstep).on arg
  have h₂' : Task _ (fun p : P => send (p.1, initial p.2)) (fun p => send (out p)) :=
    h₂.conform (fun _ => rfl)
      (fun p => by simp only [arg, Task.forest_send, hseed, send_prod]) (fun _ => rfl)
  have h₃ : Task (fun p : P => size (out p)) (fun p => send (out p))
      (fun p => send (run test p)) := by
    refine ((Easy.snd.compose Easy.snd : Easy (fun c : Acc Y => c.2.2)).on out).conform
      (fun _ => rfl) (fun _ => rfl) ?_
    intro p
    unfold out run
    rw [hfold, hseed]
  refine ((h₁.compose h₂').compose h₃).bound 4 ?_
  intro p
  have h := hcost p.1 p.2
  simp only [arg, Task.forest_send, out, hsize]
  change size p.1 + size p.2 + (costSum (a p.2) p.1 + size p.1) +
      (size p.2 + 2 * p.2.1.length + 4) + 1 ≤ _
  rw [Nat.add_mul p.1.length 1, Nat.one_mul]
  omega

end P1ProgDir.SolIndexedSweep
