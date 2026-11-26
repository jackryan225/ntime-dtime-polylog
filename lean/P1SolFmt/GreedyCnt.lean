import P1ChkFinal.GreedyCountTarget

namespace P1SolGreedyCnt.Sol

open Filter P1Wrap P1Wit P1Wit.SolSpace
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1ChkGreedy P1SolGreedy P1ChkFinal.C7R P1ChkFinal.FmtAgTarget
open private levelDims layoutRows layoutRows_length runPhases runPhases_OK runPhases_length
  CalendarOK slotCap slotCap_ge levelDims_bounds from P1Wit.SpaceFacts

private theorem levelDims_count_bounds {k : Type*} [Field k] (S : BlockSchedule k)
    {a g P : ℕ} (kind : Option Bool) (hslots : 2 ^ a ≤ slotCap S) :
    let L := levelDims S.expanderExponent a g P kind
    L.bases * 2 ^ L.laneW ≤ P ∧ 2 ^ L.slotW ≤ slotCap S ∧
      L.termKeys ≤ slotCap S * 2 ^ L.laneW := by
  obtain ⟨hlanes, _, _, _, hkeys, _⟩ := levelDims_bounds S kind (P := P) (g := g) hslots
  rw [hlanes] at hkeys
  exact ⟨Nat.div_mul_le_self P _, hslots, hkeys⟩

/-- Bound the product of bases and the lane radix by the starting number of positions. -/
private theorem layoutRows_count_bounds {k : Type*} [Field k] (S : BlockSchedule k)
    (P g : ℕ) (xs : List Phase) (ready : Bool) (hgood : CalendarOK S ready xs) :
    ∀ L ∈ layoutRows S P g xs,
      L.bases * 2 ^ L.laneW ≤ P ∧ 2 ^ L.slotW ≤ slotCap S ∧
        L.termKeys ≤ slotCap S * 2 ^ L.laneW := by
  induction xs generalizing P g ready with
  | nil =>
    intro L hL
    change L ∈ [levelDims S.expanderExponent (S.degreeExponent 0) g P none] at hL
    rw [List.mem_singleton] at hL
    subst L
    exact levelDims_count_bounds S none (slotCap_ge S 0)
  | cons ph xs ih =>
    intro L hL
    change L ∈ levelDims S.expanderExponent ph.exponent g P (some ph.shrink) ::
      layoutRows S (P / ph.divisor) (g - ph.laneLoss) xs at hL
    obtain ⟨hslots, hcal⟩ := hgood
    rcases List.mem_cons.mp hL with rfl | hL
    · exact levelDims_count_bounds S _ hslots
    · have htail : ∃ nextReady, CalendarOK S nextReady xs := by
        by_cases hs : ph.shrink = true
        · rw [ite_eq_left hs] at hcal
          exact ⟨true, hcal.2⟩
        · rw [ite_eq_right hs] at hcal
          exact ⟨false, hcal.2.2⟩
      obtain ⟨nextReady, hnext⟩ := htail
      obtain ⟨hP, hslot, hkeys⟩ := ih _ _ nextReady hnext L hL
      exact ⟨hP.trans (Nat.div_le_self _ _), hslot, hkeys⟩

/-- A fixed bound for the radix contributed by the packing overhead. -/
private def packingRadixCap {k : Type*} [Field k] (S : BlockSchedule k) : ℕ :=
  Finset.univ.sup fun a : Fin (slotCap S + 1) => 2 ^ packingLaneBits a 0

private theorem le_packingRadixCap {k : Type*} [Field k] (S : BlockSchedule k)
    {a : ℕ} (ha : a ≤ slotCap S) :
    2 ^ packingLaneBits a 0 ≤ packingRadixCap S :=
  Finset.le_sup (f := fun j : Fin (slotCap S + 1) => 2 ^ packingLaneBits j 0)
    (Finset.mem_univ ⟨a, Nat.lt_succ_of_le ha⟩)

private def rowCoeff {k : Type*} [Field k] (S : BlockSchedule k) : ℕ :=
  1 + slotCap S * packingRadixCap S

private theorem rowCoeff_pos {k : Type*} [Field k] (S : BlockSchedule k) : 0 < rowCoeff S := by
  unfold rowCoeff
  omega

private theorem row_count_bounds {k : Type*} [Field k] (S : BlockSchedule k)
    (D : Dims) (ℓ : ℕ) {P : ℕ}
    (hP : (D.lv ℓ).bases * 2 ^ (D.lv ℓ).laneW ≤ P)
    (hslots : 2 ^ (D.lv ℓ).slotW ≤ slotCap S)
    (hkeys : (D.lv ℓ).termKeys ≤ slotCap S * 2 ^ (D.lv ℓ).laneW) :
    (D.lv ℓ).bases ≤ rowCoeff S * P ∧
      ((termDims D (agG (fun _ => D) 0)).lv ℓ).bases ≤ rowCoeff S * P ∧
      ((refDims D).lv ℓ).bases ≤ rowCoeff S * P := by
  let L := D.lv ℓ
  have hslotW : L.slotW ≤ slotCap S := (Params.lt_two_pow' L.slotW).le.trans hslots
  have hcap := le_packingRadixCap S hslotW
  have hc : slotCap S ≤ rowCoeff S := by
    unfold rowCoeff
    have hpos := (Nat.two_pow_pos (packingLaneBits L.slotW 0)).trans_le hcap
    exact (Nat.le_mul_of_pos_right _ hpos).trans (Nat.le_add_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos L.laneW)).trans hP).trans
      (Nat.le_mul_of_pos_left _ (rowCoeff_pos S))
  · change L.bases * (2 ^ packingLaneBits L.slotW (L.laneW - packingLaneBits L.slotW 0) *
      2 ^ L.slotW) ≤ rowCoeff S * P
    rw [← packingLaneBits_add, pow_add]
    have hradix : 2 ^ (L.laneW - packingLaneBits L.slotW 0) ≤ 2 ^ L.laneW :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    calc
      _ ≤ L.bases * ((packingRadixCap S * 2 ^ L.laneW) * slotCap S) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hcap hradix) hslots)
      _ = (slotCap S * packingRadixCap S) * (L.bases * 2 ^ L.laneW) := by ring
      _ ≤ rowCoeff S * P := Nat.mul_le_mul (Nat.le_add_left _ _) hP
  · change L.bases * L.termKeys ≤ rowCoeff S * P
    calc
      _ ≤ L.bases * (slotCap S * 2 ^ L.laneW) := Nat.mul_le_mul_left _ hkeys
      _ = slotCap S * (L.bases * 2 ^ L.laneW) := by ring
      _ ≤ rowCoeff S * P := Nat.mul_le_mul hc hP

private theorem foldr_max_le (xs : List ℕ) {M : ℕ} (h : ∀ x ∈ xs, x ≤ M) :
    xs.foldr max 0 ≤ M := by
  induction xs with
  | nil => exact Nat.zero_le M
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem cntBase_le (D : Dims) {M : ℕ} (h : ∀ ℓ ≤ D.top, (D.lv ℓ).bases ≤ M) :
    cntBase D ≤ 2 ^ P1ChkGreedy.levBits D * M := by
  unfold cntBase maxBases
  apply Nat.mul_le_mul_left
  apply foldr_max_le
  intro x hx
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hx
  exact h ℓ (Nat.lt_succ_iff.mp (List.mem_range.mp hℓ))

private theorem levRadix_le (D : Dims) : 2 ^ P1ChkGreedy.levBits D ≤ 2 * (D.top + 1) := by
  change 2 ^ Params.lam (D.top + 1) ≤ _
  by_cases ht : D.top = 0
  · rw [ht]
    decide
  · exact (Params.two_pow_lam_lt (show 2 ≤ D.top + 1 by omega)).le

private theorem initialPositions_le (V : FiniteMultiTapeMachine) (t : ℕ) :
    initialPositions V 1 t ≤ (20 * locCoeff V) * ((Params.I 1 t * Params.N t) * (Params.p t + 1)) := by
  have hloc : P1Net.locCount V.K (Params.h t) ≤ locCoeff V * (Params.h t + 1) := P1Net.locCount_le
  have hloc' := hloc.trans (Nat.mul_le_mul_left (locCoeff V) (h_succ_le t))
  unfold initialPositions
  calc
    _ ≤ 2 * (Params.I 1 t * (locCoeff V * (10 * (Params.p t + 1)))) * Params.N t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hloc'))
    _ = _ := by ring

private def countCoeff {k : Type*} [Field k] (S : BlockSchedule k) (V : FiniteMultiTapeMachine) : ℕ :=
  2 * (S.steps + 1) * rowCoeff S * (20 * locCoeff V)

private theorem genuine_counts_le {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (K : Consts) (V : FiniteMultiTapeMachine) (t g d bigBias termBias : ℕ) (hI : 0 < Params.I 1 t) :
    let D := genuineDims A K V 1 t g d bigBias termBias
    let M := countCoeff S V * (Params.I 1 t * Params.N t) * (Params.p t + 1) ^ 2
    cntBase D ≤ M ∧ cntLev D ≤ M ∧ cnt7all D (agG (fun _ => D) 0) ≤ M := by
  let D := genuineDims A K V 1 t g d bigBias termBias
  let P := initialPositions V 1 t
  let M := rowCoeff S * P
  let xs := runPhases S (Params.T K t)
  let rows := layoutRows S P (Params.h t) xs
  have htop : D.top = (S.steps + 1) * Params.T K t := runPhases_length S _
  have hlen : rows.length = D.top + 1 := layoutRows_length S _ _ _
  have hrow (ℓ : ℕ) (hℓ : ℓ ≤ D.top) :
      (D.lv ℓ).bases ≤ M ∧ ((termDims D (agG (fun _ => D) 0)).lv ℓ).bases ≤ M ∧
        ((refDims D).lv ℓ).bases ≤ M := by
    have hℓ' : ℓ < rows.length := by omega
    have hmem : D.lv ℓ ∈ rows := by
      change (rows[ℓ]?).getD _ ∈ rows
      rw [List.getElem?_eq_getElem hℓ', Option.getD_some]
      exact List.getElem_mem hℓ'
    obtain ⟨hP, hslots, hkeys⟩ := layoutRows_count_bounds S P (Params.h t) xs true
      (runPhases_OK S _ true) (D.lv ℓ) hmem
    exact row_count_bounds S D ℓ hP hslots hkeys
  have hb := cntBase_le D (fun ℓ hℓ => (hrow ℓ hℓ).1)
  have ht : cntTerm D (agG (fun _ => D) 0) ≤ 2 ^ P1ChkGreedy.levBits D * M :=
    cntBase_le (termDims D _) (fun ℓ hℓ => (hrow ℓ hℓ).2.1)
  have hr : cntRef D ≤ 2 ^ P1ChkGreedy.levBits D * M :=
    cntBase_le (refDims D) (fun ℓ hℓ => (hrow ℓ hℓ).2.2)
  have hM : 0 < M := by
    have hloc : 0 < P1Net.locCount V.K (Params.h t) := Nat.succ_pos _
    exact Nat.mul_pos (rowCoeff_pos S)
      (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.mul_pos hI hloc)) (Nat.two_pow_pos _))
  have hl : cntLev D ≤ 2 ^ P1ChkGreedy.levBits D * M :=
    (Nat.le_pow_clog one_lt_two (D.top + 1)).trans (Nat.le_mul_of_pos_right _ hM)
  have htop' : D.top + 1 ≤ (S.steps + 1) * (Params.p t + 1) := by
    rw [htop, Nat.mul_succ]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Params.T_le_p K t)) (Nat.succ_pos _)
  have hcount : 2 ^ P1ChkGreedy.levBits D * M ≤
      countCoeff S V * (Params.I 1 t * Params.N t) * (Params.p t + 1) ^ 2 := by
    calc
      _ ≤ (2 * (D.top + 1)) * M := Nat.mul_le_mul_right _ (levRadix_le D)
      _ ≤ (2 * ((S.steps + 1) * (Params.p t + 1))) *
          (rowCoeff S * ((20 * locCoeff V) * ((Params.I 1 t * Params.N t) * (Params.p t + 1)))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ htop') (Nat.mul_le_mul_left _ (initialPositions_le V t))
      _ = _ := by unfold countCoeff; ring
  exact ⟨hb.trans hcount, hl.trans hcount, (max_le ht hr).trans hcount⟩

/-- The interval-width radix eventually absorbs the square in the count estimate. -/
private theorem eventually_index_budget (c : ℕ) :
    ∀ᶠ t in atTop, 0 < Params.I 1 t ∧
      c * (Params.I 1 t * Params.N t) * (Params.p t + 1) ^ 2 ≤ 2 ^ (Params.lam t - 4) := by
  have hhalf : Tendsto (fun q : ℕ => q / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro q
    exact ⟨q * 2, fun _ h => (Nat.le_div_iff_mul_le (by decide)).mpr h⟩
  have hpoly := (hhalf.comp Params.tendsto_p).eventually (Params.eventually_mul_pow_lt_two_pow (1024 * c) 2)
  filter_upwards [hpoly, Params.eventually_of_p (eventually_ge_atTop 2),
    Params.eventually_of_lam (eventually_ge_atTop 4), Params.eventually_Ib 1 le_rfl,
    eventually_ge_atTop 2] with t htPoly htP htLam htI ht
  have hI : 0 < Params.I 1 t := by
    have hlo := htI.1
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul, Nat.one_mul] at hlo
    omega
  refine ⟨hI, Nat.le_of_mul_le_mul_right ?_ (Params.B_pos t)⟩
  have hP : Params.p t + 1 ≤ 4 * (Params.p t / 2) := by omega
  have hB : 64 * c * (Params.p t + 1) ^ 2 ≤ Params.B t := by
    calc
      _ ≤ 64 * c * (4 * (Params.p t / 2)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2)
      _ = (1024 * c) * (Params.p t / 2) ^ 2 := by ring
      _ ≤ Params.B t := htPoly.le
  have hpow : (2 : ℕ) ^ Params.lam t = 16 * 2 ^ (Params.lam t - 4) := by
    calc
      _ = 2 ^ (4 + (Params.lam t - 4)) := congrArg (fun j : ℕ => (2 : ℕ) ^ j) (by omega)
      _ = _ := pow_add 2 4 _
  have hceil : Params.I 1 t * Params.bb t ≤ 4 * 2 ^ Params.lam t :=
    (by simpa only [Nat.mul_one] using htI.2 : _ ≤ 4 * t).trans
      (Nat.mul_le_mul_left _ (Params.t_le_two_pow_lam t))
  calc
    _ = (Params.I 1 t * Params.bb t) * (c * (Params.p t + 1) ^ 2) := by unfold Params.bb; ring
    _ ≤ (4 * 2 ^ Params.lam t) * (c * (Params.p t + 1) ^ 2) := Nat.mul_le_mul_right _ hceil
    _ = 2 ^ (Params.lam t - 4) * (64 * c * (Params.p t + 1) ^ 2) := by rw [hpow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hB

end P1SolGreedyCnt.Sol

open Filter P1Wrap P1Int P1Int.P11

theorem P1SolGreedyCnt.greedyCount.{u} : P1ChkFinal.GreedyCount.GreedyCountTarget.{u} := by
  intro k _ S Bt V a b d bigBias termBias _hb
  have he := (tendsto_lpTime a b).eventually
    (P1SolGreedyCnt.Sol.eventually_index_budget (P1SolGreedyCnt.Sol.countCoeff S (toOAI V)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp he
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hI, hbudget⟩ := hn₀ n hn
  obtain ⟨hbase, hlev, h7⟩ := P1SolGreedyCnt.Sol.genuine_counts_le Bt (portConsts Bt) (toOAI V)
    (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias hI
  exact ⟨hbase.trans hbudget, hlev.trans hbudget, h7.trans hbudget⟩

example : P1ChkFinal.GreedyCount.GreedyCountTarget.{0} := P1SolGreedyCnt.greedyCount

#print axioms P1SolGreedyCnt.greedyCount
