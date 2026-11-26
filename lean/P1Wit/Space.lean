import P1Wit.Decode
import P1Wrap.Params

/-!
# P1Wit.Space: the witness fits into `m` bits (lem:space, gap G3; task P6)

Lane P1-lean-W2-P6. Paper `research/papers/ntime-dtime-polylog.tex`, Lemma `lem:space` (l.1093-1106), with
`eq:p1`, `eq:p2`, `eq:size`, `eq:zlen`; parameters of `P1Wrap.Params` (task P10).

`SpaceIn K aM C t D zl` collects the size facts that the construction supplies at time bound `t` (one constant `C`):
* `eq:p1`: `D.I = ⌈aM 2^λ / b⌉` (`Params.I aM t`), `D.N = 2^h` (`Params.N t`);
* constant number of tapes, slots per base, slot, colour and tag bits, term arity;
* field widths: addresses, directory entries, energy prefixes and `Ω` take `≤ C λ` bits; arc widths and term numbers
  `≤ C (p + 1)` bits (`O(log λ)`); chain entries `≤ C` bits;
* `eq:p2`: every level has `2^g` lanes with `h - b0 T ≤ g ≤ h`;
* positions: `∑_ℓ |B_ℓ| · lanes_ℓ ≤ C I N (p + 1)` (H8: `∑ P_ℓ ≤ 2 (s0 + 1) P_0`, `P_0 = O(I h N)`), term keys
  `≤ C · lanes` per base, `Λ + 1 ≤ C (p + 1)`, chain length `≤ C I N (p + 1)`, guess blocks `≤ C I`;
* `eq:zlen`: `2^T |z| ≤ C t (p + 1)`.

**`enc_length_le`**: for every such data, for all large `t`, `D.fixedLen + zl ≤ m K t`; hence (`enc_length_eq`) the
witness `enc D (m K t) F z` has length exactly `m K t`.
-/

namespace P1Wit

open Filter P1Wrap

/-! ## The fixed length as a sum -/

theorem offAt_eq_sum (c w : ℕ → ℕ) (n : ℕ) : offAt c w n = ∑ s ∈ Finset.range n, c s * w s := by
  induction n with
  | zero => simp [offAt]
  | succ n ih => rw [offAt, ih, Finset.sum_range_succ]

/-- Bits of the twelve sections of level `ℓ`. -/
def levBits (D : Dims) (ℓ : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 12, D.count (5 + 12 * ℓ + k) * D.width (5 + 12 * ℓ + k)

theorem sum_levels (D : Dims) (L : ℕ) :
    ∑ x ∈ Finset.range (12 * L), D.count (5 + x) * D.width (5 + x) = ∑ ℓ ∈ Finset.range L, levBits D ℓ := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 12 * (L + 1) = 12 * L + 12 by ring, Finset.sum_range_add, ih, Finset.sum_range_succ _ L]
    congr 1

theorem fixedLen_eq (D : Dims) : D.fixedLen =
    (∑ s ∈ Finset.range 5, D.count s * D.width s) + (∑ ℓ ∈ Finset.range (D.top + 1), levBits D ℓ) +
      (D.count D.secOmega * D.width D.secOmega + D.count D.secChain * D.width D.secChain) := by
  unfold Dims.fixedLen Dims.off Dims.nSec
  rw [offAt_eq_sum, show 7 + 12 * (D.top + 1) = 5 + (12 * (D.top + 1) + 2) by ring,
    Finset.sum_range_add _ 5 (12 * (D.top + 1) + 2), Finset.sum_range_add _ (12 * (D.top + 1)) 2,
    sum_levels, Finset.sum_range_succ _ 1, Finset.sum_range_succ _ 0, Finset.sum_range_zero]
  have e1 : 5 + (12 * (D.top + 1) + 0) = D.secOmega := by unfold Dims.secOmega; ring
  have e2 : 5 + (12 * (D.top + 1) + 1) = D.secChain := by unfold Dims.secChain; ring
  rw [e1, e2]
  ring

theorem head_eq (D : Dims) : ∑ s ∈ Finset.range 5, D.count s * D.width s =
    D.I * D.N * D.r * 2 + D.I * D.r * D.bigW + D.I * D.r * 3 * D.bigW + D.I * D.r * 3 * D.bigW +
      D.nGB * D.bigW := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rfl

theorem levBits_eq (D : Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) : levBits D ℓ =
    ∑ k ∈ Finset.range 12, (D.lv ℓ).count (Mem.ofCode k) * D.levWidth (D.lv ℓ) (Mem.ofCode k) := by
  unfold levBits
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < 12 := Finset.mem_range.1 hk
  have e : 5 + 12 * ℓ + k = secLev ℓ (Mem.ofCode k) := by unfold secLev; rw [Mem.toNat_ofNat k hk']
  rw [e, D.count_secLev _ hℓ, D.width_secLev _ hℓ]

theorem levBits_explicit (D : Dims) {ℓ : ℕ} (hℓ : ℓ ≤ D.top) : levBits D ℓ =
    (D.lv ℓ).count .layout * 1 + (D.lv ℓ).count .outAddr * D.bigW + (D.lv ℓ).count .outDisp * (D.lv ℓ).laneW
    + (D.lv ℓ).count .outFar * (D.lv ℓ).slotW + (D.lv ℓ).count .inAddr * D.bigW
    + (D.lv ℓ).count .inDisp * (D.lv ℓ).laneW + (D.lv ℓ).count .inFar * (D.lv ℓ).slotW
    + (D.lv ℓ).count .width * D.wW + (D.lv ℓ).count .colour * (D.lv ℓ).colW
    + (D.lv ℓ).count .offset * (D.lv ℓ).tagW + (D.lv ℓ).count .energy * D.bigW
    + (D.lv ℓ).count .terms * D.wW := by
  rw [levBits_eq D hℓ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rfl

/-! ## Arithmetic helpers -/

/-- `Q = 10 (C+1)^2`: bounds every per-level coefficient. -/
def Qc (C : ℕ) : ℕ := 10 * ((C + 1) * (C + 1))

theorem le_Q (C : ℕ) : C ≤ Qc C ∧ 1 ≤ Qc C ∧ 2 ≤ Qc C ∧ 10 ≤ Qc C ∧ C * (C + 1) ≤ Qc C := by
  have h1 : C + 1 ≤ (C + 1) * (C + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : C * (C + 1) ≤ (C + 1) * (C + 1) := Nat.mul_le_mul_right _ (by omega)
  unfold Qc
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem term_le {c w Cc Cw X W Y Q : ℕ} (hc : c ≤ Cc * X) (hw : w ≤ Cw * W) (hCc : Cc ≤ Q) (hCw : Cw ≤ Q)
    (hXW : X * W ≤ Y) : c * w ≤ (Q * Q) * Y :=
  calc c * w ≤ (Cc * X) * (Cw * W) := Nat.mul_le_mul hc hw
    _ = (Cc * Cw) * (X * W) := by ring
    _ ≤ (Q * Q) * Y := Nat.mul_le_mul (Nat.mul_le_mul hCc hCw) hXW

theorem ite_count_le (b : Bool) (x : ℕ) : (if b = true then x else 0) ≤ 1 * x := by
  split <;> omega

/-! ## One level -/

theorem levBits_le (D : Dims) {ℓ C L P : ℕ} (hℓ : ℓ ≤ D.top) (hL1 : 1 ≤ L) (hP1 : 1 ≤ P)
    (hLl : L ≤ (D.lv ℓ).lanes) (hsl : (D.lv ℓ).slots ≤ C) (hslW : (D.lv ℓ).slotW ≤ C)
    (hlaneW : (D.lv ℓ).laneW ≤ 10 * L) (hcol : (D.lv ℓ).colW ≤ C) (htag : (D.lv ℓ).tagW ≤ C)
    (hkeys : (D.lv ℓ).termKeys ≤ C * (D.lv ℓ).lanes) (har : (D.lv ℓ).termArity ≤ C)
    (hbig : D.bigW ≤ C * L) (hwW : D.wW ≤ C * P) :
    levBits D ℓ ≤ 1 + 11 * ((Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P)) := by
  rw [levBits_explicit D hℓ]
  obtain ⟨q1, q2, q3, q4, q5⟩ := le_Q C
  have hBL : (D.lv ℓ).bases * L ≤ (D.lv ℓ).bases * (D.lv ℓ).lanes * P :=
    calc (D.lv ℓ).bases * L ≤ (D.lv ℓ).bases * (D.lv ℓ).lanes := Nat.mul_le_mul_left _ hLl
      _ ≤ (D.lv ℓ).bases * (D.lv ℓ).lanes * P := Nat.le_mul_of_pos_right _ hP1
  have hBP : (D.lv ℓ).bases * (D.lv ℓ).lanes * P ≤ (D.lv ℓ).bases * (D.lv ℓ).lanes * P := le_rfl
  have cSlot : (D.lv ℓ).bases * (D.lv ℓ).slots ≤ C * (D.lv ℓ).bases := by
    rw [Nat.mul_comm C]; exact Nat.mul_le_mul_left _ hsl
  have cWid : (D.lv ℓ).bases * (D.lv ℓ).lanes * (D.lv ℓ).slots ≤ C * ((D.lv ℓ).bases * (D.lv ℓ).lanes) := by
    rw [Nat.mul_comm C]; exact Nat.mul_le_mul_left _ hsl
  have cTerm : (D.lv ℓ).bases * (D.lv ℓ).termKeys * ((D.lv ℓ).termArity + 1) ≤
      C * (C + 1) * ((D.lv ℓ).bases * (D.lv ℓ).lanes) :=
    calc (D.lv ℓ).bases * (D.lv ℓ).termKeys * ((D.lv ℓ).termArity + 1)
          ≤ (D.lv ℓ).bases * (C * (D.lv ℓ).lanes) * (C + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hkeys) (by omega)
      _ = C * (C + 1) * ((D.lv ℓ).bases * (D.lv ℓ).lanes) := by ring
  have cCol : (D.lv ℓ).count .colour ≤ 1 * (D.lv ℓ).bases := ite_count_le _ _
  have cOff : (D.lv ℓ).count .offset ≤ 1 * (D.lv ℓ).bases := ite_count_le _ _
  have cEn : (D.lv ℓ).count .energy ≤ 2 * (D.lv ℓ).bases := by
    simp only [LevelDims.count]; split <;> omega
  have wSlot : (D.lv ℓ).slotW ≤ C * L := le_trans hslW (Nat.le_mul_of_pos_right _ hL1)
  have wCol : (D.lv ℓ).colW ≤ C * L := le_trans hcol (Nat.le_mul_of_pos_right _ hL1)
  have wTag : (D.lv ℓ).tagW ≤ C * L := le_trans htag (Nat.le_mul_of_pos_right _ hL1)
  have t0 : (D.lv ℓ).count .layout * 1 ≤ 1 := by simp only [LevelDims.count]; split <;> omega
  have t1 : (D.lv ℓ).count .outAddr * D.bigW ≤ (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) :=
    term_le cSlot hbig q1 q1 hBL
  have t2 : (D.lv ℓ).count .outDisp * (D.lv ℓ).laneW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cSlot hlaneW q1 q4 hBL
  have t3 : (D.lv ℓ).count .outFar * (D.lv ℓ).slotW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cSlot wSlot q1 q1 hBL
  have t4 : (D.lv ℓ).count .inAddr * D.bigW ≤ (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) :=
    term_le cSlot hbig q1 q1 hBL
  have t5 : (D.lv ℓ).count .inDisp * (D.lv ℓ).laneW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cSlot hlaneW q1 q4 hBL
  have t6 : (D.lv ℓ).count .inFar * (D.lv ℓ).slotW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cSlot wSlot q1 q1 hBL
  have t7 : (D.lv ℓ).count .width * D.wW ≤ (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) :=
    term_le cWid hwW q1 q1 hBP
  have t8 : (D.lv ℓ).count .colour * (D.lv ℓ).colW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cCol wCol q2 q1 hBL
  have t9 : (D.lv ℓ).count .offset * (D.lv ℓ).tagW ≤
      (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) := term_le cOff wTag q2 q1 hBL
  have t10 : (D.lv ℓ).count .energy * D.bigW ≤ (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) :=
    term_le cEn hbig q3 q1 hBL
  have t11 : (D.lv ℓ).count .terms * D.wW ≤ (Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P) :=
    term_le cTerm hwW q5 q1 hBP
  omega

/-! ## The size facts supplied by the construction -/

/-- The size facts of `lem:space` at time bound `t` (see the module docstring). -/
structure SpaceIn (K : Consts) (aM C t : ℕ) (D : Dims) (zl : ℕ) : Prop where
  I_eq : D.I = Params.I aM t
  N_eq : D.N = Params.N t
  r_le : D.r ≤ C
  nGB_le : D.nGB ≤ C * D.I
  bigW_le : D.bigW ≤ C * Params.lam t
  wW_le : D.wW ≤ C * (Params.p t + 1)
  chainLen_le : D.chainLen ≤ C * D.I * D.N * (Params.p t + 1)
  chainW_le : D.chainW ≤ C
  top_le : D.top + 1 ≤ C * (Params.p t + 1)
  pos_le : ∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes ≤ C * D.I * D.N * (Params.p t + 1)
  lanes_eq : ∀ ℓ ≤ D.top, (D.lv ℓ).lanes = 2 ^ (D.lv ℓ).laneW
  laneW_ge : ∀ ℓ ≤ D.top, Params.h t - K.b0 * Params.T K t ≤ (D.lv ℓ).laneW
  laneW_le : ∀ ℓ ≤ D.top, (D.lv ℓ).laneW ≤ Params.h t
  slots_le : ∀ ℓ ≤ D.top, (D.lv ℓ).slots ≤ C
  slotW_le : ∀ ℓ ≤ D.top, (D.lv ℓ).slotW ≤ C
  colW_le : ∀ ℓ ≤ D.top, (D.lv ℓ).colW ≤ C
  tagW_le : ∀ ℓ ≤ D.top, (D.lv ℓ).tagW ≤ C
  keys_le : ∀ ℓ ≤ D.top, (D.lv ℓ).termKeys ≤ C * (D.lv ℓ).lanes
  arity_le : ∀ ℓ ≤ D.top, (D.lv ℓ).termArity ≤ C
  z_le : 2 ^ Params.T K t * zl ≤ C * t * (Params.p t + 1)

/-! ## Facts about the parameters -/

/-- `λ ≤ 2^g` for every `g ≥ h - b0 T`, once `λ ≥ 3` (from `eq:p2`, `Params.lam_pow_nine_lt`). -/
theorem lam_le_lanes (K : Consts) {t g : ℕ} (hl : 3 ≤ Params.lam t) (hg : Params.h t - K.b0 * Params.T K t ≤ g) :
    Params.lam t ≤ 2 ^ g := by
  have e0 := Params.lam_pow_nine_lt K t
  have e1 : 2 ^ (Params.h t - K.b0 * Params.T K t) ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have e2 : 3 ^ 8 ≤ Params.lam t ^ 8 := Nat.pow_le_pow_left hl 8
  have e3 : Params.lam t ^ 9 = Params.lam t * Params.lam t ^ 8 := by ring
  have e4 : Params.lam t * 2 ^ 9 ≤ Params.lam t * Params.lam t ^ 8 :=
    Nat.mul_le_mul_left _ (le_trans (by norm_num) e2)
  have e5 : 2 ^ 9 * Params.lam t < 2 ^ 9 * 2 ^ g := by
    calc 2 ^ 9 * Params.lam t = Params.lam t * 2 ^ 9 := by ring
      _ ≤ Params.lam t ^ 9 := by rw [e3]; exact e4
      _ < 2 ^ 9 * 2 ^ (Params.h t - K.b0 * Params.T K t) := e0
      _ ≤ 2 ^ 9 * 2 ^ g := Nat.mul_le_mul_left _ e1
  exact (Nat.lt_of_mul_lt_mul_left e5).le

/-- `h ≤ 10 λ` (as `p ≤ λ`). -/
theorem h_le_ten_lam {t : ℕ} (ht : 2 ≤ t) : Params.h t ≤ 10 * Params.lam t := by
  have e1 := Params.two_pow_p_le ht
  have e2 := Params.lt_two_pow' (Params.p t)
  unfold Params.h
  omega

/-- `λ ≤ N = 2^h` once `p ≥ 1`. -/
theorem lam_le_N {t : ℕ} (hp : 1 ≤ Params.p t) : Params.lam t ≤ Params.N t := by
  have e1 := Params.lam_lt_two_pow_p t
  have e2 : Params.p t + 1 ≤ Params.h t := by unfold Params.h; omega
  unfold Params.N
  exact le_trans e1.le (Nat.pow_le_pow_right (by norm_num) e2)

/-! ## The bound on the fixed part -/

/-- The constant of the bound on the fixed part. -/
def Gc (C aM : ℕ) : ℕ := 4 * aM * (13 * ((C + 1) * (C + 1)) + 11 * (Qc C * Qc C * C))

theorem fixedLen_le_U (K : Consts) {aM C t : ℕ} (D : Dims) (zl : ℕ) (hS : SpaceIn K aM C t D zl)
    (ht : 2 ≤ t) (hl : 3 ≤ Params.lam t) (hp : 1 ≤ Params.p t) (hI1 : 1 ≤ D.I) :
    D.fixedLen ≤ (13 * ((C + 1) * (C + 1)) + 11 * (Qc C * Qc C * C)) *
      (D.I * D.N * ((Params.p t + 1) * (Params.p t + 1))) := by
  set L := Params.lam t with hLdef
  set P := Params.p t + 1 with hPdef
  set CC := (C + 1) * (C + 1) with hCC
  set U := D.I * D.N * (P * P) with hU
  have hL1 : 1 ≤ L := by omega
  have hP1 : 1 ≤ P := by rw [hPdef]; omega
  have hN1 : 1 ≤ D.N := by rw [hS.N_eq]; unfold Params.N; exact Nat.one_le_two_pow
  have hLN : L ≤ D.N := by rw [hS.N_eq]; exact lam_le_N hp
  have hIN1 : 1 ≤ D.I * D.N := Nat.mul_le_mul hI1 hN1
  have hPP1 : 1 ≤ P * P := Nat.mul_le_mul hP1 hP1
  have hINU : D.I * D.N ≤ U := Nat.le_mul_of_pos_right _ hPP1
  have hINP : D.I * D.N * P ≤ U := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hP1)
  have hPU : P ≤ U := le_trans (Nat.le_mul_of_pos_left _ hIN1) hINP
  have c1 : C ≤ CC := by
    rw [hCC]; have : C + 1 ≤ (C + 1) * (C + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have c2 : C * C ≤ CC := by rw [hCC]; exact Nat.mul_le_mul (by omega) (by omega)
  have hr := hS.r_le
  have hbig := hS.bigW_le
  -- S0, S1, guess blocks
  have p1 : D.I * D.N * D.r * 2 ≤ 2 * (CC * U) :=
    calc D.I * D.N * D.r * 2 = 2 * (D.r * (D.I * D.N)) := by ring
      _ ≤ 2 * (CC * U) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (le_trans hr c1) hINU)
  have p2 : D.I * D.r * D.bigW ≤ CC * U :=
    calc D.I * D.r * D.bigW ≤ D.I * C * (C * L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) hbig
      _ = (C * C) * (D.I * L) := by ring
      _ ≤ CC * (D.I * D.N) := Nat.mul_le_mul c2 (Nat.mul_le_mul_left _ hLN)
      _ ≤ CC * U := Nat.mul_le_mul_left _ hINU
  have p3 : D.I * D.r * 3 * D.bigW ≤ 3 * (CC * U) :=
    calc D.I * D.r * 3 * D.bigW = 3 * (D.I * D.r * D.bigW) := by ring
      _ ≤ 3 * (CC * U) := Nat.mul_le_mul_left _ p2
  have p4 : D.nGB * D.bigW ≤ CC * U :=
    calc D.nGB * D.bigW ≤ (C * D.I) * (C * L) := Nat.mul_le_mul hS.nGB_le hbig
      _ = (C * C) * (D.I * L) := by ring
      _ ≤ CC * (D.I * D.N) := Nat.mul_le_mul c2 (Nat.mul_le_mul_left _ hLN)
      _ ≤ CC * U := Nat.mul_le_mul_left _ hINU
  -- the levels
  have hlev : ∀ ℓ ∈ Finset.range (D.top + 1),
      levBits D ℓ ≤ 1 + 11 * ((Qc C * Qc C) * ((D.lv ℓ).bases * (D.lv ℓ).lanes * P)) := by
    intro ℓ hmem
    have hℓ : ℓ ≤ D.top := Nat.lt_succ_iff.1 (Finset.mem_range.1 hmem)
    have hlanes : L ≤ (D.lv ℓ).lanes := by
      rw [hS.lanes_eq ℓ hℓ]; exact lam_le_lanes K hl (hS.laneW_ge ℓ hℓ)
    exact levBits_le D hℓ hL1 hP1 hlanes (hS.slots_le ℓ hℓ) (hS.slotW_le ℓ hℓ)
      (le_trans (hS.laneW_le ℓ hℓ) (h_le_ten_lam ht)) (hS.colW_le ℓ hℓ) (hS.tagW_le ℓ hℓ)
      (hS.keys_le ℓ hℓ) (hS.arity_le ℓ hℓ) hbig hS.wW_le
  have p5 : ∑ ℓ ∈ Finset.range (D.top + 1), levBits D ℓ ≤ CC * U + 11 * (Qc C * Qc C * C * U) := by
    have s1 := Finset.sum_le_sum hlev
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum] at s1
    have e : ∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes * P =
        (∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes) * P := by
      rw [Finset.sum_mul]
    rw [e] at s1
    have s2 : (∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes) * P ≤ C * U :=
      calc (∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes) * P
            ≤ (C * D.I * D.N * P) * P := Nat.mul_le_mul_right _ hS.pos_le
        _ = C * U := by rw [hU]; ring
    have s3 : Qc C * Qc C * ((∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes) * P) ≤
        Qc C * Qc C * C * U := by
      rw [Nat.mul_assoc (Qc C * Qc C) C U]; exact Nat.mul_le_mul_left _ s2
    have s4 : (D.top + 1) * 1 ≤ CC * U :=
      calc (D.top + 1) * 1 = D.top + 1 := Nat.mul_one _
        _ ≤ C * P := hS.top_le
        _ ≤ CC * U := Nat.mul_le_mul c1 hPU
    omega
  -- Omega and the chain
  have hpos1 : (D.lv D.top).bases * (D.lv D.top).lanes ≤
      ∑ ℓ ∈ Finset.range (D.top + 1), (D.lv ℓ).bases * (D.lv ℓ).lanes :=
    Finset.single_le_sum (f := fun ℓ => (D.lv ℓ).bases * (D.lv ℓ).lanes) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_self _))
  have p6 : D.count D.secOmega * D.width D.secOmega ≤ CC * U := by
    have e : D.count D.secOmega * D.width D.secOmega = (D.lv D.top).bases * D.bigW := by
      simp only [Dims.count, Dims.width, D.kind_Omega]
    have hlanes : L ≤ (D.lv D.top).lanes := by
      rw [hS.lanes_eq D.top le_rfl]; exact lam_le_lanes K hl (hS.laneW_ge D.top le_rfl)
    rw [e]
    calc (D.lv D.top).bases * D.bigW ≤ (D.lv D.top).bases * (C * L) := Nat.mul_le_mul_left _ hbig
      _ = C * ((D.lv D.top).bases * L) := by ring
      _ ≤ C * ((D.lv D.top).bases * (D.lv D.top).lanes) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlanes)
      _ ≤ C * (C * D.I * D.N * P) := Nat.mul_le_mul_left _ (le_trans hpos1 hS.pos_le)
      _ = (C * C) * (D.I * D.N * P) := by ring
      _ ≤ CC * U := Nat.mul_le_mul c2 hINP
  have p7 : D.count D.secChain * D.width D.secChain ≤ CC * U := by
    have e : D.count D.secChain * D.width D.secChain = D.chainLen * D.chainW := by
      simp only [Dims.count, Dims.width, D.kind_chain]
    rw [e]
    calc D.chainLen * D.chainW ≤ (C * D.I * D.N * P) * C := Nat.mul_le_mul hS.chainLen_le hS.chainW_le
      _ = (C * C) * (D.I * D.N * P) := by ring
      _ ≤ CC * U := Nat.mul_le_mul c2 hINP
  rw [fixedLen_eq, head_eq]
  have fin : 13 * (CC * U) + 11 * (Qc C * Qc C * C * U) = (13 * CC + 11 * (Qc C * Qc C * C)) * U := by ring
  rw [← fin]
  omega

/-- `B · fixedLen ≤ G t (p + 1)^2` for all large `t` (the S0-S2 part of `lem:space`). -/
theorem fixedLen_le (K : Consts) {aM : ℕ} (haM : 1 ≤ aM) (C : ℕ) :
    ∀ᶠ t in atTop, ∀ (D : Dims) (zl : ℕ), SpaceIn K aM C t D zl →
      Params.B t * D.fixedLen ≤ Gc C aM * t * (Params.p t + 1) ^ 2 := by
  filter_upwards [Params.eventually_Ib aM haM, Params.eventually_of_p (eventually_ge_atTop 1),
    Params.eventually_of_lam (eventually_ge_atTop 3), eventually_ge_atTop 2] with t hIb hp hl ht D zl hS
  have hbb : Params.bb t = Params.B t * Params.N t := rfl
  have hI1 : 1 ≤ D.I := by
    rw [hS.I_eq]
    rcases Nat.eq_zero_or_pos (Params.I aM t) with h0 | h0
    · rw [h0] at hIb
      have : 1 * 1 ≤ aM * t := Nat.mul_le_mul haM (show 1 ≤ t by omega)
      omega
    · exact h0
  have hU := fixedLen_le_U K D zl hS ht hl hp hI1
  set G0 := 13 * ((C + 1) * (C + 1)) + 11 * (Qc C * Qc C * C) with hG0
  have hINB : D.I * D.N * Params.B t ≤ 4 * aM * t := by
    rw [hS.I_eq, hS.N_eq]
    calc Params.I aM t * Params.N t * Params.B t = Params.I aM t * Params.bb t := by rw [hbb]; ring
      _ ≤ 4 * aM * t := hIb.2
  calc Params.B t * D.fixedLen
        ≤ Params.B t * (G0 * (D.I * D.N * ((Params.p t + 1) * (Params.p t + 1)))) := Nat.mul_le_mul_left _ hU
    _ = G0 * (D.I * D.N * Params.B t) * ((Params.p t + 1) * (Params.p t + 1)) := by ring
    _ ≤ G0 * (4 * aM * t) * ((Params.p t + 1) * (Params.p t + 1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hINB)
    _ = Gc C aM * t * (Params.p t + 1) ^ 2 := by rw [hG0]; unfold Gc; ring

/-- **P6 `enc_length_le`** (lem:space). For all large `t`, every witness format and payload length that satisfy the
size facts of the construction fit into `m = (p+1)^6 ⌈t / 2^T⌉` bits. -/
theorem enc_length_le (K : Consts) {aM : ℕ} (haM : 1 ≤ aM) (C : ℕ) :
    ∀ᶠ t in atTop, ∀ (D : Dims) (zl : ℕ), SpaceIn K aM C t D zl → D.fixedLen + zl ≤ Params.m K t := by
  filter_upwards [fixedLen_le K haM C, Params.eventually_aux K (Gc C aM), Params.eventually_z K C]
    with t h1 h2 h3 D zl hS
  have a1 := h2 _ (h1 D zl hS)
  have a2 := h3 _ hS.z_le
  omega

/-- The witness of the genuine contents has length exactly `m K t`. -/
theorem enc_length_eq (K : Consts) {aM : ℕ} (haM : 1 ≤ aM) (C : ℕ) :
    ∀ᶠ t in atTop, ∀ (D : Dims) (F : Fields) (z : List Bool), SpaceIn K aM C t D z.length →
      (enc D (Params.m K t) F z).length = Params.m K t ∧
        List.ofFn (encFn D (Params.m K t) F z) = enc D (Params.m K t) F z := by
  filter_upwards [enc_length_le K haM C] with t h D F z hS
  exact ⟨enc_length D _ F z (h D z.length hS), ofFn_encFn D _ F z (h D z.length hS)⟩

end P1Wit
