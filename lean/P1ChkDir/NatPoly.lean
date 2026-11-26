import OAI.Computability.IntegerMultiplication.Carry.Remainder
import OAI.Computability.IntegerMultiplication.Code.Pace
import Mathlib.Tactic.Ring

/-!
# P1ChkDir.NatPoly: natural numbers in binary as an OpenAI `Codec`, with polynomial-time arithmetic

Lane P1-lean-checks (2026-11-25). Tool for the check programs: with the scoped instance `NP.natCodec`
(`send n := send (Carry.born n)`, the canonical binary word of `n`, least significant bit first) a plain Lean function
on natural numbers built from `+`, `-`, `*`, `/`, `%`, the Boolean tests `ltb`, `eqb`, `bif .. then .. else ..`,
pairs and projections is `Poly` by `fun_prop`. So the arithmetic of a check is written ONCE, as a function on `ℕ`, and
is at the same time the specification and the program.

* `norm w = born (value w)` (`norm_eq`), `Poly norm`: the canonical word of the value of a word.
* `lift1`, `lift2`, `liftB2`: a word function that computes `F` on values gives `Poly F` on numbers.
* `poly_add`, `poly_sub`, `poly_mul`, `poly_div`, `poly_mod`, `poly_ltb`, `poly_eqb` (from OpenAI's `Carry.swift`,
  `sub0_r`, `polyTime`, `polyND`, `ltPoly`), `poly_and`, `poly_or`, `poly_not`.
* conversions: `poly_value` (word to number), `poly_born` (number to word), `poly_length` (tally to number),
  `easy_wordLength` (length of a bit list as a number, linear time).
* lists: `poly_headD`, `easy_tail`, `poly_getD` (constant index), `poly_table` (a constant list looked up by a
  number: finite tables such as the tape numbering).
* `pow2c κ T = 2 ^ min κ |T|` (`poly_pow2c`): a power of two with the exponent capped by a tally.

The instance is `scoped`: open the namespace `P1ChkDir.NP` to use it. No final statement of the lane mentions it.
-/

namespace P1ChkDir.NP

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry

/-! ## Canonical words -/

theorem born_eq_nil {n : ℕ} : born n = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [birth (Nat.pos_of_ne_zero hn)] at h
    exact absurd h (by simp)
  · rintro rfl
    exact born0

theorem born_cons (b : Bool) (v : ℕ) (h : ¬(b = false ∧ v = 0)) : born (digit b + 2 * v) = b :: born v := by
  have hpos : 0 < digit b + 2 * v := by
    cases b
    · have : v ≠ 0 := fun hv => h ⟨rfl, hv⟩
      simp only [d0]
      omega
    · simp only [d1]
      omega
  rw [birth hpos]
  cases b
  · have h1 : (0 + 2 * v) % 2 ≠ 1 := by omega
    have h2 : (0 + 2 * v) / 2 = v := by omega
    simp only [d0, parity, h1, h2, decide_false]
  · have h1 : (1 + 2 * v) % 2 = 1 := by omega
    have h2 : (1 + 2 * v) / 2 = v := by omega
    simp only [d1, parity, h1, h2, decide_true]

/-- One step of `norm`: put the next lower bit `b` in front of the canonical word `acc`; a high zero is dropped. -/
def normStep (p : Unit × Word × Bool) : Word := bif (p.2.1.isEmpty && !p.2.2) then [] else p.2.2 :: p.2.1

/-- The canonical word of the value of `w` (high zeros removed). -/
def norm (w : Word) : Word := trek normStep (w.reverse, (), ([] : Word))

theorem norm_nil : norm [] = [] := rfl

theorem norm_cons (b : Bool) (w : Word) : norm (b :: w) = normStep ((), norm w, b) := by
  simp only [norm, trek, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem norm_eq (w : Word) : norm w = born (value w) := by
  induction w with
  | nil => simp only [norm_nil, value_nil, born0]
  | cons b w ih =>
    rw [norm_cons, ih, value_cons]
    show (bif ((born (value w)).isEmpty && !b) then [] else b :: born (value w)) = _
    by_cases h : b = false ∧ value w = 0
    · obtain ⟨rfl, hv⟩ := h
      simp only [hv, born0, d0, List.isEmpty_nil, Bool.not_false, Bool.and_self, Bool.cond_true, Nat.mul_zero,
        Nat.add_zero]
    · rw [born_cons b _ h]
      have hc : ((born (value w)).isEmpty && !b) = false := by
        cases b
        · have hv : value w ≠ 0 := fun hv => h ⟨rfl, hv⟩
          have hne : born (value w) ≠ [] := fun e => hv (born_eq_nil.1 e)
          cases hb : born (value w) with
          | nil => exact absurd hb hne
          | cons _ _ => rfl
        · simp only [Bool.not_true, Bool.and_false]
      rw [hc, Bool.cond_false]

@[fun_prop] theorem poly_and : Poly (fun p : Bool × Bool => p.1 && p.2) := (Easy.finite _).poly
@[fun_prop] theorem poly_or : Poly (fun p : Bool × Bool => p.1 || p.2) := (Easy.finite _).poly
@[fun_prop] theorem poly_not : Poly (fun b : Bool => !b) := (Easy.finite _).poly

@[fun_prop] theorem poly_isEmpty {X : Type} [Codec X] : Poly (fun l : List X => l.isEmpty) := (vacant X).poly

theorem poly_normStep : Poly normStep := by
  unfold normStep
  fun_prop

theorem size_normStep (p : Unit) (x : Word) (y : Bool) :
    size (normStep (p, x, y)) ≤ size x + 1 * (size p + size y) := by
  show size (bif (x.isEmpty && !y) then [] else y :: x) ≤ _
  have h1 : size p = 1 := rfl
  have h2 : size y = 1 := rfl
  cases (x.isEmpty && !y)
  · simp only [Bool.cond_false, size_cons, h1, h2]
    omega
  · simp only [Bool.cond_true, size_nil, h1, h2]
    omega

@[fun_prop] theorem poly_norm : Poly norm := by
  unfold norm
  exact (show Poly (fun w : Word => (w.reverse, (), ([] : Word))) from by fun_prop).compose
    (polyTrek _ poly_normStep 1 size_normStep)

/-! ## Numbers as trees -/

/-- **Numbers in binary**: the tree of `n` is the tree of its canonical word `born n`. -/
scoped instance natCodec : Codec ℕ := ⟨fun n => send (born n)⟩

theorem send_nat (n : ℕ) : (send n : Tree) = send (born n) := rfl

theorem size_nat (n : ℕ) : size n = size (born n) := rfl

/-- A word function that computes `F` on values gives `F` on numbers. -/
theorem lift1 {g : Word → Word} (hg : Poly g) {F : ℕ → ℕ} (h : ∀ x, value (g x) = F (value x)) : Poly F := by
  obtain ⟨t, ht, hT⟩ := hg.compose poly_norm
  refine ⟨fun n => t (born n), ht.map born, ?_⟩
  exact (hT.on born).conform (fun _ => rfl) (fun _ => rfl) (fun n => by
    show send (norm (g (born n))) = send (born (F n))
    rw [norm_eq, h, birthValue])

theorem lift2 {g : Word × Word → Word} (hg : Poly g) {F : ℕ → ℕ → ℕ}
    (h : ∀ x y, value (g (x, y)) = F (value x) (value y)) : Poly (fun p : ℕ × ℕ => F p.1 p.2) := by
  obtain ⟨t, ht, hT⟩ := hg.compose poly_norm
  refine ⟨fun p => t (born p.1, born p.2), ht.map (fun p : ℕ × ℕ => (born p.1, born p.2)), ?_⟩
  exact (hT.on (fun p : ℕ × ℕ => (born p.1, born p.2))).conform (fun _ => rfl) (fun _ => rfl) (fun p => by
    show send (norm (g (born p.1, born p.2))) = send (born (F p.1 p.2))
    rw [norm_eq, h, birthValue, birthValue])

theorem liftB2 {g : Word × Word → Bool} (hg : Poly g) {F : ℕ → ℕ → Bool}
    (h : ∀ x y, g (x, y) = F (value x) (value y)) : Poly (fun p : ℕ × ℕ => F p.1 p.2) := by
  obtain ⟨t, ht, hT⟩ := hg
  refine ⟨fun p => t (born p.1, born p.2), ht.map (fun p : ℕ × ℕ => (born p.1, born p.2)), ?_⟩
  exact (hT.on (fun p : ℕ × ℕ => (born p.1, born p.2))).conform (fun _ => rfl) (fun _ => rfl) (fun p => by
    show send (g (born p.1, born p.2)) = send (F p.1 p.2)
    rw [h, birthValue, birthValue])

/-! ## Arithmetic -/

@[fun_prop] theorem poly_add : Poly (fun p : ℕ × ℕ => p.1 + p.2) := lift2 swift (fun x y => add_val x y)

@[fun_prop] theorem poly_sub : Poly (fun p : ℕ × ℕ => p.1 - p.2) := lift2 sub0_r (fun x y => sub0_v x y)

@[fun_prop] theorem poly_mul : Poly (fun p : ℕ × ℕ => p.1 * p.2) := lift2 polyTime (fun x y => tm_value x y)

@[fun_prop] theorem poly_div : Poly (fun p : ℕ × ℕ => p.1 / p.2) :=
  lift2 polyND.fstCompose (fun x y => (division_rules x y).1)

@[fun_prop] theorem poly_mod : Poly (fun p : ℕ × ℕ => p.1 % p.2) :=
  lift2 polyND.sndCompose (fun x y => (division_rules x y).2)

/-- `a < b` as a Boolean. -/
def ltb (a b : ℕ) : Bool := decide (a < b)

/-- `a = b` as a Boolean. -/
def eqb (a b : ℕ) : Bool := decide (a = b)

@[simp] theorem ltb_iff {a b : ℕ} : ltb a b = true ↔ a < b := by simp [ltb]
@[simp] theorem eqb_iff {a b : ℕ} : eqb a b = true ↔ a = b := by simp [eqb]
@[simp] theorem ltb_false_iff {a b : ℕ} : ltb a b = false ↔ b ≤ a := by simp [ltb]
@[simp] theorem eqb_false_iff {a b : ℕ} : eqb a b = false ↔ a ≠ b := by simp [eqb]

@[fun_prop] theorem poly_ltb : Poly (fun p : ℕ × ℕ => ltb p.1 p.2) := liftB2 ltPoly (fun x y => lt_r x y)

theorem eqb_eq (a b : ℕ) : eqb a b = (!(ltb a b || ltb b a)) := by
  unfold eqb ltb
  by_cases s : a = b
  · subst s
    simp
  · rcases Nat.lt_or_gt_of_ne s with h | h <;> simp [s, h, Nat.lt_asymm h]

@[fun_prop] theorem poly_eqb : Poly (fun p : ℕ × ℕ => eqb p.1 p.2) := by
  have h : Poly (fun p : ℕ × ℕ => !(ltb p.1 p.2 || ltb p.2 p.1)) := by fun_prop
  have e : (fun p : ℕ × ℕ => eqb p.1 p.2) = (fun p : ℕ × ℕ => !(ltb p.1 p.2 || ltb p.2 p.1)) :=
    funext fun p => eqb_eq p.1 p.2
  rw [e]
  exact h

/-! ## Conversions -/

@[fun_prop] theorem poly_value : Poly (fun w : Word => value w) := by
  obtain ⟨t, ht, hT⟩ := poly_norm
  exact ⟨t, ht, hT.conform (fun _ => rfl) (fun _ => rfl) (fun w => by
    show send (norm w) = send (born (value w))
    rw [norm_eq])⟩

@[fun_prop] theorem poly_born : Poly (fun n : ℕ => born n) :=
  ⟨size, Dom.base _, (Task.self : Task (size : ℕ → ℕ) (fun n : ℕ => send n) (fun n : ℕ => send n))⟩

/-- The length of a tally as a number, in linear time (OpenAI `easy_chart`). -/
theorem easy_length : Easy (fun t : Tally => t.length) := easy_chart

@[fun_prop] theorem poly_length : Poly (fun t : Tally => t.length) := easy_length.poly

/-- The length of a bit list as a number, in linear time. -/
theorem easy_wordLength {A : Type} [Codec A] : Easy (fun w : List A => w.length) := by
  have h : Easy (fun w : List A => born (ruler w).length) := (Easy.ruler Easy.identity).compose easy_chart
  exact Task.conform h (fun _ => rfl) (fun _ => rfl) (fun w => by
    show send (born (ruler w).length) = send (born w.length)
    rw [ruler_length])

/-! ## Lists -/

@[fun_prop] theorem poly_headD {X : Type} [Codec X] (d : X) : Poly (fun l : List X => l.headD d) :=
  (Iter.leader d).poly

theorem easy_tail {X : Type} [Codec X] : Easy (fun l : List X => l.tail) := by
  suffices e : (fun l : List X => l.tail) =
      (fun l => List.casesOn (motive := fun _ => List X) l [] (fun a b => (fun p : X × List X => p.2) (a, b))) from
    e ▸ Easy.listCase ([] : List X) Easy.snd
  funext l
  cases l <;> rfl

@[fun_prop] theorem poly_tail {X : Type} [Codec X] : Poly (fun l : List X => l.tail) := easy_tail.poly

theorem getD_zero_headD {X : Type} (l : List X) (d : X) : l.getD 0 d = l.headD d := by
  cases l <;> rfl

theorem getD_succ_tail {X : Type} (l : List X) (j : ℕ) (d : X) : l.getD (j + 1) d = l.tail.getD j d := by
  cases l <;> simp

/-- An entry of a list at a CONSTANT index. -/
theorem poly_getD {X : Type} [Codec X] (d : X) : ∀ j : ℕ, Poly (fun l : List X => l.getD j d)
  | 0 => by
    have e : (fun l : List X => l.getD 0 d) = (fun l => l.headD d) := funext fun l => getD_zero_headD l d
    rw [e]
    exact poly_headD d
  | j + 1 => by
    have e : (fun l : List X => l.getD (j + 1) d) = (fun l => l.tail.getD j d) :=
      funext fun l => getD_succ_tail l j d
    rw [e]
    exact poly_tail.compose (poly_getD d j)

/-- **Finite tables.** A CONSTANT list looked up by a number (`d` beyond its end). -/
theorem poly_table (d : ℕ) : ∀ l : List ℕ, Poly (fun n : ℕ => l.getD n d)
  | [] => by
    have e : (fun n : ℕ => ([] : List ℕ).getD n d) = (fun _ => d) := funext fun n => by simp
    rw [e]
    exact Code.Poly.const d
  | a :: l => by
    have e : (fun n : ℕ => (a :: l).getD n d) = (fun n => bif eqb n 0 then a else l.getD (n - 1) d) := by
      funext n
      cases n with
      | zero => simp [eqb]
      | succ n => simp [eqb]
    rw [e]
    have h1 : Poly (fun n : ℕ => eqb n 0) := by fun_prop
    have h2 : Poly (fun n : ℕ => n - 1) := by fun_prop
    exact Code.Poly.choose h1 (Code.Poly.const a) (h2.compose (poly_table d l))

/-! ## Powers of two with a capped exponent -/

theorem born_length_mono {m n : ℕ} (h : m ≤ n) : (born m).length ≤ (born n).length := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hn : 0 < n := lt_of_lt_of_le hm h
      rw [birth hm, birth hn, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (ih (n / 2) (Nat.div_lt_self hn (by norm_num)) (Nat.div_le_div_right h))

theorem born_two_mul_length (n : ℕ) : (born (2 * n)).length ≤ (born n).length + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := born_cons false n (by simp; omega)
    simp only [d0, Nat.zero_add] at h
    rw [h, List.length_cons]

theorem born_succ_length (n : ℕ) : (born (n + 1)).length ≤ (born n).length + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [birth (by norm_num : 0 < 0 + 1)]
    simp
  · exact (born_length_mono (by omega : n + 1 ≤ 2 * n)).trans (born_two_mul_length n)

theorem size_two_mul (n : ℕ) : size (2 * n) ≤ size n + 2 := by
  rw [size_nat, size_nat, size_word, size_word]
  have := born_two_mul_length n
  omega

theorem size_succ (n : ℕ) : size (n + 1) ≤ size n + 2 := by
  rw [size_nat, size_nat, size_word, size_word]
  have := born_succ_length n
  omega

/-- One step of the capped power: the state `(j, 2 ^ j)` moves to `(j + 1, 2 ^ (j + 1))` while `j < κ`. -/
def powStep (p : ℕ × ℕ × ℕ) : ℕ × ℕ := bif ltb p.2.1 p.1 then (p.2.1 + 1, 2 * p.2.2) else p.2

theorem poly_powStep : Poly powStep := by
  unfold powStep
  fun_prop

theorem size_powStep (κ : ℕ) (y : ℕ × ℕ) : size (powStep (κ, y)) ≤ 4 * size κ + size y := by
  obtain ⟨j, acc⟩ := y
  show size (bif ltb j κ then (j + 1, 2 * acc) else (j, acc)) ≤ _
  have hκ : 1 ≤ size κ := size_pos κ
  cases ltb j κ
  · simp only [Bool.cond_false, size_prod]
    omega
  · simp only [Bool.cond_true, size_prod]
    have h1 := size_succ j
    have h2 := size_two_mul acc
    omega

theorem powStep_iter (κ : ℕ) : ∀ n : ℕ, ((fun y => powStep (κ, y))^[n]) (0, 1) = (min κ n, 2 ^ min κ n)
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', powStep_iter κ n]
    show (bif ltb (min κ n) κ then (min κ n + 1, 2 * 2 ^ min κ n) else (min κ n, 2 ^ min κ n)) = _
    by_cases h : n < κ
    · have h1 : min κ n = n := Nat.min_eq_right (Nat.le_of_lt h)
      have h2 : min κ (n + 1) = n + 1 := Nat.min_eq_right h
      have h3 : ltb n κ = true := ltb_iff.2 h
      rw [h1, h2, h3, Bool.cond_true, pow_succ, Nat.mul_comm]
    · have hk : κ ≤ n := Nat.le_of_not_lt h
      have h1 : min κ n = κ := Nat.min_eq_left hk
      have h2 : min κ (n + 1) = κ := Nat.min_eq_left (Nat.le_succ_of_le hk)
      have h3 : ltb κ κ = false := ltb_false_iff.2 (Nat.le_refl κ)
      rw [h1, h2, h3, Bool.cond_false]

/-- `2 ^ min κ |T|`: a power of two whose exponent is capped by the tally `T`. -/
def pow2c (κ : ℕ) (T : Tally) : ℕ := 2 ^ min κ T.length

theorem pow2c_eq {κ : ℕ} {T : Tally} (h : κ ≤ T.length) : pow2c κ T = 2 ^ κ := by
  rw [pow2c, Nat.min_eq_left h]

@[fun_prop] theorem poly_pow2c : Poly (fun p : ℕ × Tally => pow2c p.1 p.2) := by
  have hb := Poly.bounder powStep poly_powStep 4 size_powStep
  have h1 : Poly (fun p : ℕ × Tally => (p.2, (p.1, ((0 : ℕ), (1 : ℕ))))) := by fun_prop
  have h2 := (h1.compose hb).sndCompose
  have e : (fun p : ℕ × Tally => pow2c p.1 p.2) =
      (fun p : ℕ × Tally => (((fun y => powStep (p.1, y))^[p.2.length]) (0, 1)).2) := by
    funext p
    rw [powStep_iter]
    rfl
  rw [e]
  exact h2

end P1ChkDir.NP
