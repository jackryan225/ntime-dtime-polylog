import P1Net.ContractProofCompletion

/-! Source and destination rows for the accepting run, before packing physical edges. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (input : List Bool)

noncomputable def runWrite (k : V.K) (t : ℕ) (Z : ℤ) : Fin (strWidth V B) → Bool :=
  encC V B ((runOut (B := B) input t).blocks k (slotOf σ k t Z))

noncomputable def runHistory (k : V.K) (Z : ℤ) (t : ℕ) : Fin (strWidth V B) → Bool :=
  valueAt σ k Z (encC V B (initBlock (B := B) input k Z))
    (fun u => runWrite V B I σ input k u Z) t

noncomputable def runContentSource (ι : Fin I) (k : V.K) (x : Fin 8 × Fin (2 ^ h)) :
    Fin (strWidth V B) → Bool :=
  contentSource I σ ι k (fun Z => runHistory V B I σ input k Z ((ι : ℕ) * 2 ^ h))
    (runWrite V B I σ input k) (fun _ => false) x

noncomputable def runContentDest (ι : Fin I) (k : V.K) (y : Fin 8 × Fin (2 ^ h)) :
    Fin (strWidth V B) → Bool :=
  runContentSource V B I σ input ι k ((accPerm I σ ι k).symm y)

theorem lane_time_lt (ι : Fin I) (j : Fin (2 ^ h)) : (ι : ℕ) * 2 ^ h + j < I * 2 ^ h := by
  have ht := (intervalEquiv I h (ι, (laneEquiv h).symm j)).isLt
  simpa only [intervalEquiv_val, Equiv.apply_symm_apply] using ht

theorem runHistory_table (hsk : skeleton V input B (I * 2 ^ h) = σ) (k : V.K)
    (t : ℕ) (ht : t < I * 2 ^ h) (δ : Fin 3) :
    runHistory V B I σ input k (slotBlock σ k t δ) t =
      encC V B ((runIn (B := B) input t).blocks k δ) := by
  have H := run_wired (M := V) (B := B) (n := I * 2 ^ h) input t ht.le k δ
  rw [hsk] at H
  rw [H]
  unfold runHistory valueAt wired
  cases prevAccess σ k (slotBlock σ k t δ) t <;> rfl

theorem runContentDest_table (hsk : skeleton V input B (I * 2 ^ h) = σ)
    (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (δ : Fin 3) :
    runContentDest V B I σ input ι k (typ (3 + δ), j) =
      encC V B ((runIn (B := B) input ((ι : ℕ) * 2 ^ h + j)).blocks k δ) := by
  let t := (ι : ℕ) * 2 ^ h + j
  let Z := slotBlock σ k t δ
  have hacc : Acc I σ ι k j Z := acc_slot I σ ι k j δ δ.isLt
  have hs : slotAt I σ ι k j Z = (δ : ℕ) := slotAt_slot I σ ι k j δ δ.isLt
  change runContentDest V B I σ input ι k (typ (3 + δ), j) = encC V B ((runIn (B := B) input t).blocks k δ)
  rw [← runHistory_table V B I σ input hsk k t (lane_time_lt I ι j) δ]
  change runContentDest V B I σ input ι k (typ (3 + δ), j) = runHistory V B I σ input k Z t
  unfold runContentDest runContentSource
  rw [← hs, delivered_window I σ ι k _ _ _ hacc]
  exact (valueAt_lane I σ ι k Z (encC V B (initBlock (B := B) input k Z))
    (fun u => runWrite V B I σ input k u Z) j).symm

theorem runContentSource_table (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (δ : Fin 3) :
    runContentSource V B I σ input ι k (typ (3 + δ), j) =
      encC V B ((runOut (B := B) input ((ι : ℕ) * 2 ^ h + j)).blocks k δ) := by
  let Z := slotBlock σ k ((ι : ℕ) * 2 ^ h + j) δ
  have ha : Acc I σ ι k j Z := acc_slot I σ ι k j δ δ.isLt
  have hs : slotAt I σ ι k j Z = (δ : ℕ) := slotAt_slot I σ ι k j δ δ.isLt
  have hw := source_window I σ ι k (fun u => runHistory V B I σ input k u ((ι : ℕ) * 2 ^ h))
    (runWrite V B I σ input k) (fun _ => false) ha
  simpa only [runContentSource, hs, runWrite, Z, slotOf_slotBlock] using hw

/-- The coordinate read by a physical port, including ports on the negative half of a tape. -/
theorem portBlock_div (ι : Fin I) (k : V.K) (δ : Fin 3) (j : Fin (2 ^ h)) :
    portBlock I σ ι k δ j / 2 ^ h = portQ I σ k ι δ := by
  have hN : (0 : ℤ) < 2 ^ h := by positivity
  have hj : ((j : ℕ) : ℤ) < 2 ^ h := by exact_mod_cast j.isLt
  unfold portBlock portQ
  apply ediv_eq_of_bounds hN <;> nlinarith [show (0 : ℤ) ≤ (j : ℕ) by positivity]

theorem runContentSource_port (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (δ : Fin 3) :
    runContentSource V B I σ input ι k (typ δ, j) =
      runHistory V B I σ input k (portBlock I σ ι k δ j) ((ι : ℕ) * 2 ^ h) := by
  have hd := δ.isLt
  have hv := typ_val (n := (δ : ℕ)) (by omega)
  simp only [runContentSource, contentSource, hv, itemBlock, if_pos hd]

theorem runContentDest_port (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (δ : Fin 3) :
    runContentDest V B I σ input ι k (typ δ, j) =
      runHistory V B I σ input k (portBlock I σ ι k δ j) (((ι : ℕ) + 1) * 2 ^ h) := by
  let Z := portBlock I σ ι k δ j
  have ho : Owns I σ k ι (Z / 2 ^ h) := by
    rw [show Z / 2 ^ h = portQ I σ k ι δ from portBlock_div V I σ ι k δ j]
    exact owns_portQ I σ k ι δ
  obtain ⟨hlo, hhi⟩ := bounds_of_owns I σ ι k ho
  obtain ⟨hd, hj⟩ := portBlock_type_lane I σ ι k δ δ.isLt j
  have H := delivered_port I σ ι k (fun u => runHistory V B I σ input k u ((ι : ℕ) * 2 ^ h))
    (runWrite V B I σ input k) (fun _ => false) hlo hhi
  rw [show portType I σ ι k Z = (δ : ℕ) from hd, show portLane h Z = j from hj] at H
  exact H.trans (valueAt_end I σ ι k Z (encC V B (initBlock (B := B) input k Z))
    (fun u => runWrite V B I σ input k u Z)).symm

theorem runContentSource_dummy (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (d : Fin 8)
    (hd : 6 ≤ (d : ℕ)) : runContentSource V B I σ input ι k (d,j) = fun _ => false := by
  simp only [runContentSource, contentSource, if_neg (show ¬ (d : ℕ) < 3 by omega),
    if_neg (show ¬ (d : ℕ) < 6 by omega)]

theorem runContentDest_dummy (ι : Fin I) (k : V.K) (j : Fin (2 ^ h)) (d : Fin 8)
    (hd : 6 ≤ (d : ℕ)) : runContentDest V B I σ input ι k (d,j) = fun _ => false := by
  unfold runContentDest runContentSource
  exact delivered_dummy I σ ι k _ _ _ d j hd

theorem runHistory_first (ι : Fin I) (k : V.K) (Z : ℤ)
    (hp : prevOwner I σ k ι (Z / 2 ^ h) = none) :
    runHistory V B I σ input k Z ((ι : ℕ) * 2 ^ h) = encC V B (initBlock (B := B) input k Z) := by
  unfold runHistory
  rw [valueAt_owner I σ ι k Z, hp]

theorem runHistory_prev (ι i : Fin I) (k : V.K) (Z : ℤ)
    (hp : prevOwner I σ k ι (Z / 2 ^ h) = some i) :
    runHistory V B I σ input k Z ((ι : ℕ) * 2 ^ h) =
      runHistory V B I σ input k Z (((i : ℕ) + 1) * 2 ^ h) := by
  unfold runHistory
  rw [valueAt_owner I σ ι k Z, hp]

theorem run_pin {g : ℕ} (L : GuessLayout V g) (w : Fin g → Bool) (k : V.K) (Z : ℤ) :
    PinOK B L k Z (initBlock (B := B) (L.input w) k Z) := by
  intro o
  exact ⟨fun j hj => ⟨w j, L.init_some w k _ j hj⟩, fun hj => L.init_none w k _ hj⟩

theorem run_center {g : ℕ} (L : GuessLayout V g) (w : GoodGuess V B L I σ)
    (t : ℕ) (ht : t < I * 2 ^ h) :
    (evolve (runIn (M := V) (B := B) (L.input w.val) t)).move = σ ⟨t, ht⟩ ∧
      (t + 1 = I * 2 ^ h → Accepts B (evolve (runIn (M := V) (B := B) (L.input w.val) t))) := by
  have hv := run_valid (M := V) (B := B) (L.input w.val) (I * 2 ^ h)
  rw [w.property.2] at hv
  rw [evolve_runIn]
  refine ⟨hv.move t ht, ?_⟩
  intro he
  rw [accepts_runOut, he]
  exact (haltsIn_iff _ _ _).1 w.property.1

end P1Net.AstraContract
