import P1Case1.Chain
import OAI.Computability.MultitapeWeakETH.CoarseTrace

/-!
# P1, Case 1, task G2 by a guessing machine: the TRANS trace bound from a display machine

OpenAI's coarse-trace machinery (`TraceSchedule`, `TraceTables`, `TracePaths`) feeds the first operand
`x` through input terminals, hard-wires the second operand `y` into the tables, and reads the output
word from the output tape at the end. A TRANS decider reads `(X, Y)`. To make `Y` a free variable of the
relation network without editing OpenAI's files, run a NONDETERMINISTIC machine `M'` that guesses `Y`
(one coin per bit), writes it on its output tape and where the decider reads it, and then runs the
decider. Its accepting runs write exactly `Xᵀ` (by correctness of the decider). This is
`TransDisplayBound` (open piece 1a, a machine construction: task G1').

Proved here: `transTraceBound_of_display : TransDisplayBound → TransTraceBound`, by OpenAI's trace
lemmas with all coins admitted (adapted copy of `coarseTraceBound`, `CoarseTrace.lean`).
-/

namespace P1Case1

open OAI.DepthThreeLowerBound
open OAI.Computability.MultitapeWeakETH (Word Network Machine timely writes initial frozenRun
  timely_frozen_iff TraceCode most_frequent_trace PriceTwo)
open OAI.Computability.MultitapeWeakETH.PhysicalBlocks

/-- **Open piece 1a (task G1').** For every TRANS decider `M` there are an OpenAI `Machine` `M'` and a
constant `a` such that on input `x` (`N²` bits; the second operand all `false`), within
`T' = T + a (N² + 1)` steps, some coin seed gives an accepting run that writes `xᵀ`, and every accepting
run writes `xᵀ`. -/
def TransDisplayBound : Prop := ∀ M : FiniteMultiTapeMachine, ∃ (M' : Machine) (a : ℕ),
  ∀ N T : ℕ, DecidesTransInOAI M N T → ∀ x : Word (N * N),
    (∃ seed : Fin (T + a * (N * N + 1) + 1) → M'.Choice,
        timely M' (T + a * (N * N + 1)) seed x (fun _ => false) (transposeWord x)) ∧
    ∀ (seed : Fin (T + a * (N * N + 1) + 1) → M'.Choice) (out : Word (N * N)),
      timely M' (T + a * (N * N + 1)) seed x (fun _ => false) out → out = transposeWord x

noncomputable section

variable {M : Machine}

/-- A seed on `[0, T]` extended to all times (copy of the private `extend` of `CoarseTrace.lean`). -/
def extendSeed {T : ℕ} (s : Fin (T+1) → M.Choice) (t : ℕ) : M.Choice := s ⟨min t T, by omega⟩

theorem timely_path' {n T : ℕ} (s : Fin (T+1) → M.Choice) (x y out : Word n) :
    timely M T s x y out ↔
      Accept (frozenRun M (extendSeed s) (initial M x y) (T+1)) ∧
        writes M (config (frozenRun M (extendSeed s) (initial M x y) (T+1))) out := by
  rw [timely_frozen_iff]
  change (∃ cfg, frozenRun M (extendSeed s) (initial M x y) (T+1) = .halted cfg ∧ _) ↔ _
  cases h : frozenRun M (extendSeed s) (initial M x y) (T+1) with
  | running p => simp [Accept, stopped]
  | halted p => simp [Accept, stopped, config]

theorem seed_of_path' {n T : ℕ} {x y out : Word n} (coins : ℕ → M.Choice)
    (acc : Accept (frozenRun M coins (initial M x y) (T+1)))
    (wr : writes M (config (frozenRun M coins (initial M x y) (T+1))) out) :
    ∃ s : Fin (T+1) → M.Choice, timely M T s x y out := by
  let s : Fin (T+1) → M.Choice := fun i => coins i.val
  have agree : ∀ t < T+1, extendSeed s t = coins t := by
    intro t ht
    simp [s, extendSeed, min_eq_left (by omega : t ≤ T)]
  refine ⟨s, (timely_path' s x y out).mpr ?_⟩
  rw [prefix_coins _ _ agree]
  exact ⟨acc, wr⟩

/-- Pigeonhole over trace codes for single words. -/
theorem wordDensity_fiber {n h e : ℕ} (record : Word n → TraceCode h e) :
    ∃ code, ∀ good : Word n → Prop, (∀ x, record x = code → good x) →
      (1 : ℝ) ≤ (3:ℝ) ^ (h * e) * wordDensity good := by
  classical
  obtain ⟨code, best⟩ := most_frequent_trace (Finset.univ : Finset (Word n)) record
  refine ⟨code, fun good keep => ?_⟩
  have inclus : (Finset.univ.filter fun x => record x = code) ⊆ Finset.univ.filter good := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, keep x (Finset.mem_filter.mp hx).2⟩
  have bound := best.trans (Nat.mul_le_mul_left _ (Finset.card_le_card inclus))
  rw [Finset.card_univ] at bound
  have hpos : (0:ℝ) < Fintype.card (Word n) := by exact_mod_cast Fintype.card_pos
  have hreal : (Fintype.card (Word n) : ℝ) ≤
      (3:ℝ) ^ (h * e) * ((Finset.univ.filter good).card : ℝ) := by exact_mod_cast bound
  unfold wordDensity
  rw [mul_div_assoc', le_div_iff₀ hpos, one_mul]
  convert hreal using 3

/-- Copy of the private `trace_loss` of `CoarseTrace.lean`. -/
theorem trace_loss' {b : ℕ} (hb : 0 < b) (heads T : ℕ) (a : ℕ) (ha : 2*heads ≤ a) :
    (3:ℝ)^(heads * epochs T b) ≤ (2:ℝ) ^ ((a:ℝ)*(1+(T:ℝ)/b)) := by
  have div : ((T/b:ℕ):ℝ) ≤ (T:ℝ)/b :=
    (le_div_iff₀ (by exact_mod_cast hb)).mpr (by exact_mod_cast Nat.div_mul_le_self T b)
  calc
    _ ≤ (2^2:ℝ)^(heads * epochs T b) := by gcongr; norm_num
    _ = (2:ℝ)^((2*(heads * epochs T b):ℕ):ℝ) := by rw [Real.rpow_natCast]; exact (pow_mul ..).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have c : (2:ℝ)*heads ≤ a := by exact_mod_cast ha
      simp only [epochs,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = (2*(heads:ℝ))*(((T/b:ℕ):ℝ)+1) := by ring
        _ ≤ _ := by rw [add_comm (1:ℝ)]; gcongr

local instance (M : Machine) : Fintype M.Tapes := @Fintype.ofFinite _ M.tapesFinite

/-- **G2 via a display machine.** -/
theorem transTraceBound_of_display (display : TransDisplayBound) : TransTraceBound := by
  intro M
  obtain ⟨M', a, disp⟩ := display M
  let heads := Fintype.card M'.Tapes
  let A := (3 + 2 * heads) * (1 + 2 * a)
  have hA : 0 < A := by positivity
  refine ⟨degreeFactor M', A, hA, 1, fun N hN T hdec => ?_⟩
  have hb : 0 < N := hN
  let T' := T + a * (N * N + 1)
  let y0 : Word (N * N) := fun _ => false
  have ex : ∀ x : Word (N * N), ∃ s : Fin (T' + 1) → M'.Choice,
      timely M' T' s x y0 (transposeWord x) := fun x => (disp N T hdec x).1
  choose seed hseed using ex
  let record (x : Word (N * N)) := traceOf M' hb T' (extendSeed (seed x)) (initial M' x y0)
  obtain ⟨code, keep⟩ := wordDensity_fiber record
  let start i := ((initial M' (n := N * N) (fun _ => false) (fun _ => false)).tape i).pos
  let base := bases M' start code
  let G := traceNetwork M' (N * N) N T' base
  obtain ⟨tables, sem⟩ := exists_trace_tables (M := M') (n := N * N) hb T' base (fun _ _ => True)
  have good : ∀ x, record x = code → TransGood G (tables y0) x := by
    intro x follows
    let s := seed x
    have hs : (fun i => ((initial M' x y0).tape i).pos) = start :=
      funext ((initial_controller M' x y0 (fun _ => false) (fun _ => false)).2)
    have fits : Follows N T' base (extendSeed s) (initial M' x y0) := by
      intro j hj
      have facts := traceOf_fits M' hb T' (extendSeed s) (initial M' x y0) hj
      change traceOf M' hb T' (extendSeed s) (initial M' x y0) = code at follows
      rwa [hs, follows] at facts
    obtain ⟨accept, write⟩ := (timely_path' s x y0 (transposeWord x)).mp (hseed x)
    refine ⟨(sem x y0 _).mpr (history_of_path hb base (fun _ _ => True) x y0 _ (extendSeed s)
      (fun _ => trivial) fits accept write), fun other hother => ?_⟩
    have initFits := fits 0 (Nat.zero_le _)
    simp only [RunAt, cut, Nat.zero_mul, Nat.zero_min, frozenRun] at initFits
    obtain ⟨f, _, ha, hw⟩ := path_of_history hb base (fun _ _ => True)
      ⟨extendSeed s, fun _ => trivial⟩ x y0 other initFits ((sem x y0 other).mp hother)
    obtain ⟨r, hr⟩ := seed_of_path' f ha hw
    exact (disp N T hdec x).2 r other hr
  refine ⟨G, traceNetwork_bounded .., ?_, tables y0, ?_⟩
  · -- size: vertices * N ≤ 3 (N + T' + N²) ≤ A (N + T + N²)
    have size : G.vertices * N ≤ 3 * (N + T' + N * N) := traceNetwork_size M' (N * N) N T' base
    have sizeR : (G.vertices : ℝ) * N ≤ 3 * ((N : ℝ) + (T + a * (N * N + 1)) + N * N) := by
      exact_mod_cast size
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have hh0 : (0 : ℝ) ≤ heads := Nat.cast_nonneg heads
    have hAR : (A : ℝ) = (3 + 2 * heads) * (1 + 2 * a) := by simp [A]
    rw [hAR]
    have hNN : (1:ℝ) ≤ N * N := by nlinarith
    have h1 : (a : ℝ) * (N * N + 1) ≤ 2 * a * (N * N) := by
      nlinarith [mul_le_mul_of_nonneg_left hNN ha0]
    have h2 : 3 * ((N : ℝ) + (T + a * (N * N + 1)) + N * N) ≤
        3 * (1 + 2 * a) * ((N : ℝ) + T + N * N) := by nlinarith
    have h3 : 3 * (1 + 2 * (a : ℝ)) * ((N : ℝ) + T + N * N) ≤
        (3 + 2 * heads) * (1 + 2 * a) * ((N : ℝ) + T + N * N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    linarith
  · -- density: 2^(-A(1+N+T/N)) ≤ 2^(-(2 heads)(1+T'/N)) ≤ 3^(-heads·epochs) ≤ density
    have one := keep (TransGood G (tables y0)) good
    have loss := trace_loss' hb heads T' (2 * heads) le_rfl
    set E := heads * epochs T' N with hE
    set L : ℝ := ((2 * heads : ℕ) : ℝ) * (1 + (T' : ℝ) / N) with hL
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ E := by positivity
    have hd : ((3 : ℝ) ^ E)⁻¹ ≤ wordDensity (TransGood G (tables y0)) := by
      rw [inv_le_iff_one_le_mul₀ h3pos, mul_comm]; exact one
    have h2L : (2 : ℝ) ^ (-L) ≤ ((3 : ℝ) ^ E)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
      exact inv_anti₀ h3pos loss
    have hexp : -(A : ℝ) * (1 + N + (T : ℝ) / N) ≤ -L := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      have hh0 : (0 : ℝ) ≤ heads := Nat.cast_nonneg heads
      have hT' : (T' : ℝ) / N ≤ (T : ℝ) / N + 2 * a * N := by
        have e1 : (T' : ℝ) = T + a * (N * N + 1) := by simp [T']
        have hNN : (1:ℝ) ≤ N * N := by nlinarith
        have h1 : (a : ℝ) * (N * N + 1) ≤ 2 * a * N * N := by
          nlinarith [mul_le_mul_of_nonneg_left hNN ha0]
        rw [e1, add_div]
        have h2 : (a : ℝ) * (N * N + 1) / N ≤ 2 * a * N := by
          rw [div_le_iff₀ hNpos]; linarith
        linarith
      have hTN : (0 : ℝ) ≤ (T : ℝ) / N := div_nonneg hT0 hNpos.le
      have hAR : (A : ℝ) = (3 + 2 * heads) * (1 + 2 * a) := by simp [A]
      rw [hL, hAR]
      push_cast
      have key : 2 * (heads : ℝ) * (1 + (T' : ℝ) / N) ≤
          (3 + 2 * heads) * (1 + 2 * a) * (1 + N + (T : ℝ) / N) := by
        have k1 : 2 * (heads : ℝ) * (1 + (T' : ℝ) / N) ≤
            2 * heads * (1 + (T : ℝ) / N + 2 * a * N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        have k2 : 2 * (heads : ℝ) * (1 + (T : ℝ) / N + 2 * a * N) ≤
            2 * heads * ((1 + 2 * a) * (1 + N + (T : ℝ) / N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
        have k3 : 2 * (heads : ℝ) * ((1 + 2 * a) * (1 + N + (T : ℝ) / N)) ≤
            (3 + 2 * heads) * (1 + 2 * a) * (1 + N + (T : ℝ) / N) := by
          have : 0 ≤ (1 + 2 * (a : ℝ)) * (1 + N + (T : ℝ) / N) := by positivity
          nlinarith
        linarith
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans (h2L.trans hd)

end

/-- **Case 1, assembled with the display machine** (characteristic two). Open inputs: the display
machine (G1'), the field table bound from `PriceTwo` (G3 + G4), the NTIME upper bound of coTRANS (C1). -/
theorem c1_of_priceTwo_of_display
    (display : TransDisplayBound)
    (fieldTable : PriceTwo → TransFieldTableBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog coTRANS)
    (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_priceTwo_of_parts (transTraceBound_of_display display) fieldTable upper price

end P1Case1
