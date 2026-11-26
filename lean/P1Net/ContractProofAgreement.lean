import P1Net.ContractProofRun

/-! Two physical solutions with the same completed guess agree on the data entering every routing. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z z' : RoutedGood V B L I σ ha bset)

local notation "Wx" => strWidth V B
local notation "startW" => startWord V B L I σ ha bset
local notation "cent" => centerData V B L I σ ha bset
local notation "outW" => slotOut V B I σ ha
local notation "tbl" => tableAt V B L I σ ha bset
local notation "guess" => completedGuess V B L I σ ha bset

structure SourceAgreement : Prop where
  center : ∀ ι l, cent z ι l = cent z' ι l
  port : ∀ (ι : Fin I) (k : V.K) (δ : Fin 3) (l : BitWord h),
    outW z.val (ι,.portIn k δ) l 0 Wx = outW z'.val (ι,.portIn k δ) l 0 Wx
  start : ∀ ι j, startW z ι j = startW z' ι j

theorem unused_end (route : Routes bset) (ι : Fin I) (j : Fin (2 ^ h)) (hj : (j : ℕ) ≠ 0) :
    endWord V B L I σ ha bset z ι j = startW z ι j := by
  have e : stNext (h := h) (0,j) = (0,j) := by simp [stNext, hj]
  have H := state_delivery V B L I σ ha bset z ι (route _ _) (0,j)
  rwa [e, state_output_zero, state_input_zero] at H

theorem unused_start (route : Routes bset) (ι : Fin I) (j : Fin (2 ^ h)) (hj : (j : ℕ) ≠ 0) :
    startW z ι j = fun _ => false := by
  suffices H : ∀ n (i : Fin I), (i : ℕ) = n → startW z i j = fun _ => false from H ι ι rfl
  intro n
  induction n with
  | zero =>
    intro i hi
    have he : i = 0 := Fin.ext hi
    subst i
    have H := z.property ((((0 : Fin I), Loc.eIn), false), (laneEquiv h).symm j)
    simp only [rnSiteOK, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Equiv.apply_symm_apply, if_neg hj] at H
    simp only [startWord]
    exact H
  | succ n ih =>
    intro i hi
    let i' : Fin I := ⟨n, by have := i.isLt; omega⟩
    have hp : colPred i = some i' := by simp [colPred, hi, i']
    rw [boundary_copy V B L I σ ha bset z hp j, unused_end V B L I σ ha bset z route i' j hj]
    exact ih i' rfl

theorem same_seed_of_completion (b b' : UnownedBits V B L I σ) (hw : guess z b = guess z' b')
    (k : V.K) (Z : ℤ) (ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) :
    seedWord V B I σ ha z.val k Z = seedWord V B I σ ha z'.val k Z := by
  rw [(seedBlock_spec V B L I σ ha bset z k Z ex).2, (seedBlock_spec V B L I σ ha bset z' k Z ex).2,
    seedBlock_initial V B L I σ ha bset z b k Z ex, seedBlock_initial V B L I σ ha bset z' b' k Z ex, hw]

theorem agree_of_completion (route : Routes bset) (b b' : UnownedBits V B L I σ) (hw : guess z b = guess z' b') :
    SourceAgreement V B L I σ ha bset z z' := by
  have hr := (valid_unique (L.input (guess z b)) (valid_tables V B L I σ ha bset z route b)).2
  have hr' := (valid_unique (L.input (guess z' b')) (valid_tables V B L I σ ha bset z' route b')).2
  have ht (t : ℕ) (hlt : t < I * 2 ^ h) : tbl z t = tbl z' t := by
    rw [(hr t hlt).1, (hr' t hlt).1, hw]
  have hc (ι : Fin I) (l : BitWord h) : cent z ι l = cent z' ι l := by
    have H := ht ((ι : ℕ) * 2 ^ h + laneEquiv h l) (lane_time_lt I ι (laneEquiv h l))
    simpa only [tableAt_lane, Equiv.symm_apply_apply] using H
  have hall (t : ℕ) : tbl z t = tbl z' t := by simp only [tableAt, hc]
  have hwrite (k : V.K) (t : ℕ) (Z : ℤ) :
      writeWord V B L I σ ha bset z k t Z = writeWord V B L I σ ha bset z' k t Z := by
    simp only [writeWord, hall]
  refine ⟨hc, ?_, ?_⟩
  · intro ι k δ l
    let j := laneEquiv h l
    let Z := portBlock I σ ι k δ j
    have hQ : Z / 2 ^ h = portQ I σ k ι δ := portBlock_div V I σ ι k δ j
    have ho : Owns I σ k ι (Z / 2 ^ h) := by rw [hQ]; exact owns_portQ I σ k ι δ
    have hs := same_seed_of_completion V B L I σ ha bset z z' b b' hw k Z ⟨ι,ho⟩
    have h1 := (physical_port_values V B L I σ ha bset z ι k (fun i k' => route _ (accAddr I σ i k')) Z ho).1
    have h2 := (physical_port_values V B L I σ ha bset z' ι k (fun i k' => route _ (accAddr I σ i k')) Z ho).1
    simp only [hs, hwrite] at h1
    have he := h1.trans h2.symm
    rw [portInput_word V B L I σ ha bset z ι k Z ho, portInput_word V B L I σ ha bset z' ι k Z ho] at he
    have hj : portLane h Z = j := (portBlock_type_lane I σ ι k δ δ.isLt j).2
    simpa only [hQ, portSlot_portQ, hj, j, Equiv.symm_apply_apply] using he
  · intro ι j
    by_cases hj : (j : ℕ) = 0
    · have h0 : j = 0 := Fin.ext hj
      subst j
      rw [← first_lane V B L I σ ha bset z (route _ _) ι, ← first_lane V B L I σ ha bset z' (route _ _) ι]
      simp only [beforeState, hall]
    · exact (unused_start V B L I σ ha bset z route ι j hj).trans
        (unused_start V B L I σ ha bset z' route ι j hj).symm

end P1Net.AstraContract
