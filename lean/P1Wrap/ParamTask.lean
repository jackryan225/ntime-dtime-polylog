import P1Wrap.ParamAlg
import OAI.Computability.IntegerMultiplication.Carry.Small
import OAI.Computability.IntegerMultiplication.Carry.Wide
import OAI.Computability.IntegerMultiplication.Bits.Multiply

/-!
# Piece A of the W3 split: the parameters `m(n)`, `padLen(n)`, `k(n)` as OpenAI tasks

Statements (fixed on the board, 2026-11-25 ~10:58Z; pieces B = `InnerImpl` and C = `OuterImpl` use them):

* `ParamM j a b`: `Easy (fun i : Tally × Tally => tally (mCheck j a b i.1.length i.2.length))`, where
  `mCheck n L = m(n)` if `L = (p + 2) m(n)` (the length `m + padLen` of `u ++ 0^padLen`), else `0`.
* `ParamK a b`: `Easy (fun s : Tally => tally (lpK2 a b s.length))`.
* `ParamPad j a b`: `Computes (fun s : Tally => nuOf j a b s.length)
    (fun s : Tally => (tally (lpM2 (sOf j) a b s.length), tally (padLen j a b s.length)))`.

Method: unary `n` to binary by `Carry.easy_chart` (linear); the parameters by OpenAI's polynomial-time binary
arithmetic (`Bits.add`, `Bits.scale`, `Bits.product` (Toom), `Carry.light` = `⌈log₂⌉`, halving, shifts); the
polynomial cost in the bit length is absorbed into linear cost (`absorb1`, `absorb2`: `(2r+4)^k ≤ C 2^r` and
`2^|born n| ≤ 2n+1`); binary to unary by `Carry.rice` (cost = value + size).
-/

namespace P1Wrap.W3.PT

open P1Int P1Wrap.W3
open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open OAI.Computability.IntegerMultiplication.Carry

noncomputable section

/-! ## The three statements -/

/-- `m(n)` if the remainder length `L` equals `(p + 2) m(n)` (`= m + padLen`), else `0`. -/
def mCheck (j a b n L : ℕ) : ℕ :=
  if (lpP2 a b n + 2) * lpM2 (sOf j) a b n = L then lpM2 (sOf j) a b n else 0

def ParamM (j a b : ℕ) : Prop :=
  Easy (fun i : Tally × Tally => tally (mCheck j a b i.1.length i.2.length))

def ParamK (a b : ℕ) : Prop :=
  Easy (fun s : Tally => tally (lpK2 a b s.length))

def ParamPad (j a b : ℕ) : Prop :=
  Computes (fun s : Tally => nuOf j a b s.length)
    (fun s : Tally => (tally (lpM2 (sOf j) a b s.length), tally (padLen j a b s.length)))

theorem mCheck_le (j a b n L : ℕ) : mCheck j a b n L ≤ L := by
  unfold mCheck
  split_ifs with h
  · rw [← h]; exact Nat.le_mul_of_pos_left _ (by omega)
  · exact Nat.zero_le _

/-! ## Polylogarithmic cost is linear -/

theorem two_pow_len_born_pos : ∀ n : ℕ, 1 ≤ n → 2 ^ (born n).length ≤ 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [birth hn, List.length_cons, pow_succ]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h1 : n = 1 := by omega
      subst h1
      simp
    · have := ih (n / 2) (Nat.div_lt_self hn (by norm_num)) (by omega)
      omega

theorem two_pow_len_born (n : ℕ) : 2 ^ (born n).length ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := two_pow_len_born_pos n hn; omega

theorem poly_le_two_pow (k : ℕ) : ∃ C : ℕ, ∀ r : ℕ, (2 * r + 4) ^ k ≤ C * 2 ^ r := by
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 (eventually_poly_le (2 ^ k) k)
  refine ⟨(2 * Q + 4) ^ k + 1, fun r => ?_⟩
  have e : (2 * r + 4) ^ k = 2 ^ k * (r + 2) ^ k := by
    rw [show 2 * r + 4 = 2 * (r + 2) by ring, mul_pow]
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rcases Nat.lt_or_ge r Q with h | h
  · have h2 : (2 * r + 4) ^ k ≤ (2 * Q + 4) ^ k := Nat.pow_le_pow_left (by omega) k
    calc (2 * r + 4) ^ k ≤ (2 * Q + 4) ^ k := h2
      _ ≤ ((2 * Q + 4) ^ k + 1) * 1 := by omega
      _ ≤ ((2 * Q + 4) ^ k + 1) * 2 ^ r := Nat.mul_le_mul_left _ h1
  · have h3 := hQ r h
    calc (2 * r + 4) ^ k = 2 ^ k * (r + 2) ^ k := e
      _ ≤ 2 ^ r := h3
      _ ≤ ((2 * Q + 4) ^ k + 1) * 2 ^ r := Nat.le_mul_of_pos_left _ (by omega)

theorem absorb1 (k C : ℕ) : ∃ D : ℕ, ∀ n : ℕ, C * (size (born n) + 1) ^ k ≤ D * (n + 1) := by
  obtain ⟨E, hE⟩ := poly_le_two_pow k
  refine ⟨2 * C * E, fun n => ?_⟩
  have h1 : size (born n) + 1 ≤ 2 * (born n).length + 4 := by rw [size_word]; omega
  have h2 := hE (born n).length
  have h3 := two_pow_len_born n
  calc C * (size (born n) + 1) ^ k ≤ C * (2 * (born n).length + 4) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k)
    _ ≤ C * (E * 2 ^ (born n).length) := Nat.mul_le_mul_left _ h2
    _ ≤ C * (E * (2 * n + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ ≤ 2 * C * E * (n + 1) := by
      have e : 2 * C * E * (n + 1) = C * (E * (2 * n + 1)) + C * E := by ring
      rw [e]; exact Nat.le_add_right _ _

theorem absorb2 (k C : ℕ) : ∃ D : ℕ, ∀ n L : ℕ,
    C * (size (born n, born L) + 1) ^ k ≤ D * (n + L + 1) := by
  obtain ⟨E, hE⟩ := poly_le_two_pow k
  refine ⟨2 * (C * (2 ^ k * E)), fun n L => ?_⟩
  set r := max (born n).length (born L).length with hr
  have h1 : size (born n, born L) + 1 ≤ 2 * (2 * r + 4) := by
    simp only [size_prod, size_word]
    have := le_max_left (born n).length (born L).length
    have := le_max_right (born n).length (born L).length
    omega
  have h2 : 2 ^ r ≤ 2 * (n + L) + 1 := by
    rcases le_total (born n).length (born L).length with h | h
    · rw [hr, max_eq_right h]; have := two_pow_len_born L; omega
    · rw [hr, max_eq_left h]; have := two_pow_len_born n; omega
  calc C * (size (born n, born L) + 1) ^ k ≤ C * (2 * (2 * r + 4)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k)
    _ = C * (2 ^ k * (2 * r + 4) ^ k) := by rw [mul_pow]
    _ ≤ C * (2 ^ k * (E * 2 ^ r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hE r))
    _ ≤ C * (2 ^ k * (E * (2 * (n + L) + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2))
    _ ≤ 2 * (C * (2 ^ k * E)) * (n + L + 1) := by
      have e : 2 * (C * (2 ^ k * E)) * (n + L + 1) =
          C * (2 ^ k * (E * (2 * (n + L) + 1))) + C * (2 ^ k * E) := by ring
      rw [e]; exact Nat.le_add_right _ _

/-! ## The binary computation -/

/-- `w ↦ w²`. -/
def sqW (w : Word) : Word := product (w, w)

/-- `t = (b + 2a)(n² + 1) + n + 1`. -/
def tW (a b : ℕ) (w : Word) : Word := add (add (scale (b + 2 * a) (add (sqW w, [true])), w), [true])

/-- `λ = ⌈log₂ t⌉`, unary. -/
def lamT (a b : ℕ) (w : Word) : Tally := light (tW a b w)

/-- `p = ⌊log₂ λ⌋ = ⌈log₂ (λ + 1)⌉ - 1`, unary. -/
def pT (a b : ℕ) (w : Word) : Tally :=
  (cutLists (tally 1, light (add (born (lamT a b w).length, [true])))).2

def halfStep (s : Tally) : Tally := (half s).1

def halfIter : ℕ → Tally → Tally
  | 0, s => s
  | j + 1, s => halfIter j (halfStep s)

/-- `T = p / 2^j`, unary. -/
def TT (j a b : ℕ) (w : Word) : Tally := halfIter j (pT a b w)

/-- `⌈t / 2^T⌉ = (t + 2^T - 1) >>> T`. -/
def qW (j a b : ℕ) (w : Word) : Word :=
  (cutLists (TT j a b w, add (tW a b w, fill true (TT j a b w)))).2

def p1W (a b : ℕ) (w : Word) : Word := born (() :: pT a b w).length

def p2W (a b : ℕ) (w : Word) : Word := born (() :: () :: pT a b w).length

/-- `m = (p + 1)^6 ⌈t / 2^T⌉`. -/
def mW (j a b : ℕ) (w : Word) : Word :=
  product (product (sqW (sqW (p1W a b w)), sqW (p1W a b w)), qW j a b w)

/-- `padLen = (p + 1) m`. -/
def padW (j a b : ℕ) (w : Word) : Word := product (p1W a b w, mW j a b w)

def eqW (x y : Word) : Bool := !(more (x, y)) && !(more (y, x))

def mChk (j a b : ℕ) (i : Word × Word) : Word :=
  bif eqW (product (p2W a b i.1, mW j a b i.1)) i.2 then mW j a b i.1 else []

/-! ## Values -/

theorem value_one : value [true] = 1 := by simp

theorem value_replicate_true (k : ℕ) : value (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, value_cons, d1, pow_succ]; omega

theorem value_drop (l : Word) (k : ℕ) : value (l.drop k) = value l / 2 ^ k := by
  have e := value_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at e
  have hlt := value_lt (l.take k)
  rcases Nat.le_total k l.length with h | h
  · rw [List.length_take_of_le h] at e hlt
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  · rw [List.drop_eq_nil_of_le h, value_nil]
    have h1 := value_lt l
    have h2 : value l < 2 ^ k := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h)
    exact (Nat.div_eq_of_lt h2).symm

theorem value_tW (a b : ℕ) (w : Word) : value (tW a b w) = lpTime a b (value w) := by
  simp only [tW, sqW, add_val, scale_exact, exact_prod, value_one]
  rw [lpTime_eq]; ring

theorem lamT_eq (a b : ℕ) (w : Word) : lamT a b w = tally (lpLam2 a b (value w)) := by
  rw [lamT, light_v, value_tW]; rfl

theorem clog_succ_sub_one (x : ℕ) : Nat.clog 2 (x + 1) - 1 = Nat.log 2 x := by
  rw [clog_two_eq_size, log_two_eq_size]; simp

theorem pT_length (a b : ℕ) (w : Word) : (pT a b w).length = lpP2 a b (value w) := by
  simp only [pT, cutLists, List.length_drop, light_v, tally_length, add_val, lamT_eq, birthValue,
    value_one]
  rw [clog_succ_sub_one]; rfl

theorem halfStep_length (s : Tally) : (halfStep s).length = s.length / 2 := by
  simp only [halfStep, half_v, tally_length]

theorem halfIter_length : ∀ (j : ℕ) (s : Tally), (halfIter j s).length = s.length / 2 ^ j
  | 0, s => by simp [halfIter]
  | j + 1, s => by
      rw [halfIter, halfIter_length j, halfStep_length, Nat.div_div_eq_div_mul, pow_succ,
        Nat.mul_comm 2]

theorem TT_length (j a b : ℕ) (w : Word) : (TT j a b w).length = lpT2 (sOf j) a b (value w) := by
  rw [TT, halfIter_length, pT_length, lpT2_sOf]

theorem value_fill_true (s : Tally) : value (fill true s) + 1 = 2 ^ s.length := by
  rw [fill_eq]; exact value_replicate_true _

theorem value_qW (j a b : ℕ) (w : Word) : value (qW j a b w) =
    (lpTime a b (value w) + 2 ^ lpT2 (sOf j) a b (value w) - 1) / 2 ^ lpT2 (sOf j) a b (value w) := by
  have h1 := value_fill_true (TT j a b w)
  rw [TT_length] at h1
  simp only [qW, cutLists]
  rw [value_drop, add_val, value_tW, TT_length]
  congr 1
  omega

theorem value_p1W (a b : ℕ) (w : Word) : value (p1W a b w) = lpP2 a b (value w) + 1 := by
  rw [p1W, birthValue, List.length_cons, pT_length]

theorem value_p2W (a b : ℕ) (w : Word) : value (p2W a b w) = lpP2 a b (value w) + 2 := by
  rw [p2W, birthValue, List.length_cons, List.length_cons, pT_length]

theorem value_mW (j a b : ℕ) (w : Word) : value (mW j a b w) = lpM2 (sOf j) a b (value w) := by
  simp only [mW, sqW, exact_prod, value_p1W, value_qW]
  unfold lpM2; ring

theorem value_padW (j a b : ℕ) (w : Word) : value (padW j a b w) = padLen j a b (value w) := by
  simp only [padW, exact_prod, value_p1W, value_mW]
  unfold padLen; ring

theorem eqW_iff (x y : Word) : eqW x y = true ↔ value x = value y := by
  unfold eqW
  have h1 := more_lt x y
  have h2 := more_lt y x
  cases hx : more (x, y) <;> cases hy : more (y, x) <;> simp_all <;> omega

theorem value_mChk (j a b n L : ℕ) : value (mChk j a b (born n, born L)) = mCheck j a b n L := by
  have e : value (product (p2W a b (born n), mW j a b (born n))) =
      (lpP2 a b n + 2) * lpM2 (sOf j) a b n := by
    rw [exact_prod, value_p2W, value_mW, birthValue]
  unfold mChk mCheck
  dsimp only
  by_cases h : (lpP2 a b n + 2) * lpM2 (sOf j) a b n = L
  · have hb : eqW (product (p2W a b (born n), mW j a b (born n))) (born L) = true :=
      (eqW_iff _ _).2 (by rw [e, birthValue, h])
    rw [hb, if_pos h, Bool.cond_true, value_mW, birthValue]
  · have hb : eqW (product (p2W a b (born n), mW j a b (born n))) (born L) = false := by
      cases hc : eqW (product (p2W a b (born n), mW j a b (born n))) (born L)
      · rfl
      · exact absurd (by rw [← e, ← birthValue L]; exact (eqW_iff _ _).1 hc) h
    rw [hb, if_neg h, Bool.cond_false, value_nil]

/-! ## Polynomial time of the binary computation -/

section PolyLemmas
variable {X E : Type*} [Codec X] [Codec E]

theorem poly_add {f g : X → Word} (hf : Poly f) (hg : Poly g) : Poly (fun x => add (f x, g x)) := by
  have e : Poly (fun z : Word × Word => add z) := (easy_add (f := fun z : Word × Word => z) easy_id).poly
  exact (hf.pair hg).compose e

theorem poly_mul {f g : X → Word} (hf : Poly f) (hg : Poly g) : Poly (fun x => product (f x, g x)) :=
  poly_product (hf.pair hg)

theorem poly_sq {f : X → Word} (hf : Poly f) : Poly (fun x => sqW (f x)) := by
  unfold sqW; exact poly_mul hf hf

theorem poly_scale (k : ℕ) {f : X → Word} (hf : Poly f) : Poly (fun x => scale k (f x)) := by
  have e : Poly (fun z : Word => scale k z) := (easy_scale k (f := fun z : Word => z) easy_id).poly
  exact hf.compose e

theorem poly_light {f : X → Word} (hf : Poly f) : Poly (fun x => light (f x)) := hf.compose lightPoly

theorem poly_chart {s : X → Tally} (hs : Poly s) : Poly (fun x => born (s x).length) :=
  hs.compose easy_chart.poly

theorem poly_drop {s : X → Tally} {l : X → List E} (hs : Poly s) (hl : Poly l) :
    Poly (fun x => (cutLists (s x, l x)).2) := by
  have e : Poly (fun z : Tally × List E => (cutLists z).2) :=
    (easy_cut (g := fun z : Tally × List E => z) easy_id).sndCompose.poly
  exact (hs.pair hl).compose e

theorem poly_fill {s : X → Tally} (hs : Poly s) : Poly (fun x => fill true (s x)) := by
  have e : Poly (fun z : Tally => fill true z) := (easy_fill true (g := fun z : Tally => z) easy_id).poly
  exact hs.compose e

theorem poly_consU {s : X → Tally} (hs : Poly s) : Poly (fun x => () :: s x) := by
  have e : Poly (fun i : Unit × List Unit => i.1 :: i.2) := Code.Poly.cons
  exact ((Code.Poly.const ()).pair hs).compose e

theorem poly_eqW {f g : X → Word} (hf : Poly f) (hg : Poly g) : Poly (fun x => eqW (f x) (g x)) := by
  have m : Poly (fun z : Word × Word => more z) := (easy_more (f := fun z : Word × Word => z) easy_id).poly
  have e1 : Poly (fun x => more (f x, g x)) := (hf.pair hg).compose m
  have e2 : Poly (fun x => more (g x, f x)) := (hg.pair hf).compose m
  have e3 : Poly (fun z : Bool × Bool => !z.1 && !z.2) := (Easy.finite _).poly
  unfold eqW
  exact (e1.pair e2).compose e3

end PolyLemmas

theorem easy_halfStep : Easy halfStep := by
  unfold halfStep; exact halfCost.fstCompose

theorem easy_halfIter : ∀ j : ℕ, Easy (halfIter j)
  | 0 => by
      have e : halfIter 0 = fun s => s := funext fun s => rfl
      rw [e]; exact easy_id
  | j + 1 => by
      have e : halfIter (j + 1) = fun s => halfIter j (halfStep s) := funext fun s => rfl
      rw [e]; exact easy_halfStep.compose (easy_halfIter j)

theorem poly_tW (a b : ℕ) : Poly (tW a b) := by
  have hs : Poly (fun w : Word => sqW w) := poly_sq Code.Poly.identity
  unfold tW
  exact poly_add (poly_add (poly_scale _ (poly_add hs (Code.Poly.const _))) Code.Poly.identity) (Code.Poly.const _)

theorem poly_lamT (a b : ℕ) : Poly (lamT a b) := by
  unfold lamT; exact poly_light (poly_tW a b)

theorem poly_pT (a b : ℕ) : Poly (pT a b) := by
  unfold pT
  exact poly_drop (Code.Poly.const (tally 1)) (poly_light (poly_add (poly_chart (poly_lamT a b)) (Code.Poly.const _)))

theorem poly_TT (j a b : ℕ) : Poly (TT j a b) := by
  unfold TT; exact (poly_pT a b).compose (easy_halfIter j).poly

theorem poly_qW (j a b : ℕ) : Poly (qW j a b) := by
  unfold qW; exact poly_drop (poly_TT j a b) (poly_add (poly_tW a b) (poly_fill (poly_TT j a b)))

theorem poly_p1W (a b : ℕ) : Poly (p1W a b) := by
  unfold p1W; exact poly_chart (poly_consU (poly_pT a b))

theorem poly_p2W (a b : ℕ) : Poly (p2W a b) := by
  unfold p2W; exact poly_chart (poly_consU (poly_consU (poly_pT a b)))

theorem poly_mW (j a b : ℕ) : Poly (mW j a b) := by
  unfold mW
  exact poly_mul (poly_mul (poly_sq (poly_sq (poly_p1W a b))) (poly_sq (poly_p1W a b))) (poly_qW j a b)

theorem poly_padW (j a b : ℕ) : Poly (padW j a b) := by
  unfold padW; exact poly_mul (poly_p1W a b) (poly_mW j a b)

theorem poly_mChk (j a b : ℕ) : Poly (mChk j a b) := by
  have h1 : Poly (fun i : Word × Word => p2W a b i.1) := Easy.fst.poly.compose (poly_p2W a b)
  have h2 : Poly (fun i : Word × Word => mW j a b i.1) := Easy.fst.poly.compose (poly_mW j a b)
  have h3 : Poly (fun i : Word × Word => i.2) := Easy.snd.poly
  unfold mChk
  exact Code.Poly.choose (poly_eqW (poly_mul h1 h2) h3) h2 (Code.Poly.const _)

theorem poly_mPad (j a b : ℕ) : Poly (fun w => (mW j a b w, padW j a b w)) :=
  (poly_mW j a b).pair (poly_padW j a b)


/-! ## The three tasks -/

/-- `ParamK`: `k(n) = λ(n)` in unary, in linear time. -/
theorem paramK (a b : ℕ) : ParamK a b := by
  obtain ⟨t, ⟨k, C, ht⟩, hT⟩ := poly_lamT a b
  obtain ⟨D, hD⟩ := absorb1 k C
  have h1 : Task (fun s : Tally => size s + t (born s.length)) send
      (fun s => send (lamT a b (born s.length))) :=
    Task.compose easy_chart (Task.on hT (fun s : Tally => born s.length))
  have h2 : Task (fun s : Tally => size s) send (fun s => send (lamT a b (born s.length))) := by
    refine Task.bound h1 (D + 2) (fun s => ?_)
    show size s + t (born s.length) + 1 ≤ (D + 2) * (size s + 1)
    have e1 := ht (born s.length)
    have e2 := hD s.length
    have e3 : s.length + 1 ≤ size s + 1 := by rw [size_tally]; omega
    have e4 : D * (s.length + 1) ≤ D * (size s + 1) := Nat.mul_le_mul_left _ e3
    have e5 : (D + 2) * (size s + 1) = D * (size s + 1) + 2 * (size s + 1) := by ring
    omega
  show Task size send (fun s : Tally => send (tally (lpK2 a b s.length)))
  exact Task.conform h2 (fun _ => rfl) (fun _ => rfl) (fun s => by rw [lamT_eq, birthValue]; rfl)

/-- Unary pair to binary pair. -/
def e2W (i : Tally × Tally) : Word × Word := (born i.1.length, born i.2.length)

theorem easy_e2W : Easy e2W := by
  unfold e2W
  exact Easy.pair (Easy.fst.compose easy_chart) (Easy.snd.compose easy_chart)

/-- `ParamM`: `mCheck n L` in unary, in linear time in `n + L`. -/
theorem paramM (j a b : ℕ) : ParamM j a b := by
  obtain ⟨t, ⟨k, C, ht⟩, hT⟩ := poly_mChk j a b
  obtain ⟨k2, C2, hs⟩ := (poly_mChk j a b).length
  obtain ⟨D, hD⟩ := absorb2 k C
  obtain ⟨D2, hD2⟩ := absorb2 k2 C2
  have h1 : Task (fun i : Tally × Tally => (size i + t (e2W i)) +
      (size (mChk j a b (e2W i)) + value (mChk j a b (e2W i)))) send
      (fun i => send (tally (value (mChk j a b (e2W i))))) :=
    Task.compose (Task.compose easy_e2W (Task.on hT e2W)) (Task.on rice (fun i => mChk j a b (e2W i)))
  have h2 : Task (fun i : Tally × Tally => size i) send
      (fun i => send (tally (value (mChk j a b (e2W i))))) := by
    refine Task.bound h1 (D + D2 + 4) (fun i => ?_)
    show size i + t (e2W i) + (size (mChk j a b (e2W i)) + value (mChk j a b (e2W i))) + 1 ≤
      (D + D2 + 4) * (size i + 1)
    have e1 : t (e2W i) ≤ D * (i.1.length + i.2.length + 1) :=
      le_trans (ht (e2W i)) (hD i.1.length i.2.length)
    have e2 : size (mChk j a b (e2W i)) ≤ D2 * (i.1.length + i.2.length + 1) :=
      le_trans (hs (e2W i)) (hD2 i.1.length i.2.length)
    have e3 : value (mChk j a b (e2W i)) ≤ i.2.length := by
      rw [e2W, value_mChk]; exact mCheck_le _ _ _ _ _
    have e4 : size i = 2 * i.1.length + 1 + (2 * i.2.length + 1) + 1 := by
      rw [size_prod, size_tally, size_tally]
    have e5 : D * (i.1.length + i.2.length + 1) ≤ D * (size i + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e6 : D2 * (i.1.length + i.2.length + 1) ≤ D2 * (size i + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e7 : (D + D2 + 4) * (size i + 1) =
        D * (size i + 1) + D2 * (size i + 1) + 4 * (size i + 1) := by ring
    omega
  show Task size send (fun i : Tally × Tally => send (tally (mCheck j a b i.1.length i.2.length)))
  exact Task.conform h2 (fun _ => rfl) (fun _ => rfl) (fun i => by rw [e2W, value_mChk])

/-- `ParamPad`: `m(n)` and `padLen(n)` in unary, in time linear in `ν(n)`. -/
theorem paramPad (j a b : ℕ) : ParamPad j a b := by
  obtain ⟨t, ⟨k, C, ht⟩, hT⟩ := poly_mPad j a b
  obtain ⟨k2, C2, hs⟩ := (poly_mPad j a b).length
  obtain ⟨D, hD⟩ := absorb1 k C
  obtain ⟨D2, hD2⟩ := absorb1 k2 C2
  have r1 : Task (fun z : Word × Word => size z.1 + value z.1) send
      (fun z => Tree.fork (send (tally (value z.1))) (send z.2)) :=
    Task.left (Task.on rice Prod.fst) (fun z : Word × Word => send z.2)
  have r2 : Task (fun z : Word × Word => (send (tally (value z.1))).count + (size z.2 + value z.2))
      (fun z => Tree.fork (send (tally (value z.1))) (send z.2))
      (fun z => send (tally (value z.1), tally (value z.2))) :=
    Task.right (Task.on rice Prod.snd) (fun z : Word × Word => send (tally (value z.1)))
  have h1 := Task.compose (Task.compose easy_chart (Task.on hT (fun s : Tally => born s.length)))
    (Task.on (Task.compose r1 r2)
      (fun s : Tally => (mW j a b (born s.length), padW j a b (born s.length))))
  have h2 : Task (fun s : Tally => nuOf j a b s.length) send
      (fun s => send (tally (value (mW j a b (born s.length))),
        tally (value (padW j a b (born s.length))))) := by
    refine Task.bound h1 (D + D2 + 8) (fun s => ?_)
    show size s + t (born s.length) + ((size (mW j a b (born s.length)) +
        value (mW j a b (born s.length))) + ((send (tally (value (mW j a b (born s.length))))).count +
        (size (padW j a b (born s.length)) + value (padW j a b (born s.length))))) + 1 ≤
      (D + D2 + 8) * (nuOf j a b s.length + 1)
    have e1 : t (born s.length) ≤ D * (s.length + 1) := le_trans (ht _) (hD _)
    have e2 : size (mW j a b (born s.length), padW j a b (born s.length)) ≤ D2 * (s.length + 1) :=
      le_trans (hs _) (hD2 _)
    have e2' : size (mW j a b (born s.length), padW j a b (born s.length)) =
        size (mW j a b (born s.length)) + size (padW j a b (born s.length)) + 1 := rfl
    have e3 : value (mW j a b (born s.length)) = lpM2 (sOf j) a b s.length := by
      rw [value_mW, birthValue]
    have e4 : value (padW j a b (born s.length)) = padLen j a b s.length := by
      rw [value_padW, birthValue]
    have e5 : (send (tally (value (mW j a b (born s.length))))).count =
        2 * value (mW j a b (born s.length)) + 1 := by
      have h := size_tally (tally (value (mW j a b (born s.length))))
      rw [tally_length] at h
      exact h
    have e6 : size s = 2 * s.length + 1 := size_tally s
    have e7 : nuOf j a b s.length = 2 * s.length + 1 + lpM2 (sOf j) a b s.length +
        padLen j a b s.length := rfl
    have e8 : D * (s.length + 1) ≤ D * (nuOf j a b s.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e9 : D2 * (s.length + 1) ≤ D2 * (nuOf j a b s.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e10 : (D + D2 + 8) * (nuOf j a b s.length + 1) = D * (nuOf j a b s.length + 1) +
        D2 * (nuOf j a b s.length + 1) + 8 * (nuOf j a b s.length + 1) := by ring
    omega
  show Task (fun s : Tally => nuOf j a b s.length) send
    (fun s : Tally => send (tally (lpM2 (sOf j) a b s.length), tally (padLen j a b s.length)))
  exact Task.conform h2 (fun _ => rfl) (fun _ => rfl)
    (fun s => by rw [value_mW, value_padW, birthValue])

end

end P1Wrap.W3.PT
