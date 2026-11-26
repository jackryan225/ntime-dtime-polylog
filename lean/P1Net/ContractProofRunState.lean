import P1Net.ContractProofRun

/-! The state cycle has a single computational chain; every other boundary lane carries zero. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (h : ℕ) (input : List Bool)

noncomputable def runStateAt (t : ℕ) : Fin (strWidth V B) → Bool :=
  encS V B (runIn (B := B) input t).q (runIn (M := V) (B := B) input t).off

theorem runStateAt_succ (t : ℕ) :
    runStateAt V B input (t + 1) =
      encS V B (runOut (B := B) input t).q (runOut (M := V) (B := B) input t).off := rfl

noncomputable def runBoundary (t : ℕ) (j : Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  if (j : ℕ) = 0 then runStateAt V B input t else fun _ => false

noncomputable def runStateSource (ι : ℕ) (x : Fin 2 × Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  if x.1 = 0 then runBoundary V B h input (ι * 2 ^ h) x.2
  else runStateAt V B input ((ι * 2 ^ h + x.2) + 1)

noncomputable def runStateDest (ι : ℕ) (y : Fin 2 × Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  if y.1 = 0 then runBoundary V B h input ((ι + 1) * 2 ^ h) y.2
  else runStateAt V B input (ι * 2 ^ h + y.2)

theorem runStateDest_next (ι : ℕ) (x : Fin 2 × Fin (2 ^ h)) :
    runStateDest V B h input ι (stNext x) = runStateSource V B h input ι x := by
  obtain ⟨d, j⟩ := x
  fin_cases d
  · by_cases hj : (j : ℕ) = 0
    · simp [stNext, runStateDest, runStateSource, runBoundary, hj]
    · simp [stNext, runStateDest, runStateSource, runBoundary, hj]
  · by_cases hj : (j : ℕ) + 1 < 2 ^ h
    · simp [stNext, runStateDest, runStateSource, hj, Nat.add_assoc]
    · have he : (j : ℕ) + 1 = 2 ^ h := by have := j.isLt; omega
      simp [stNext, runStateDest, runStateSource, runBoundary, hj, Nat.succ_mul, Nat.add_assoc, he]

theorem runStateSource_symm (ι : ℕ) (y : Fin 2 × Fin (2 ^ h)) :
    runStateSource V B h input ι ((stPerm h).symm y) = runStateDest V B h input ι y := by
  have H := runStateDest_next V B h input ι ((stPerm h).symm y)
  change runStateDest V B h input ι ((stPerm h) ((stPerm h).symm y)) = _ at H
  rw [Equiv.apply_symm_apply] at H
  exact H.symm

theorem runBoundary_initial (j : Fin (2 ^ h)) :
    runBoundary V B h input 0 j =
      (if (j : ℕ) = 0 then encS V B V.initialState (fun _ => finOfInt B 0) else fun _ => false) := by
  have hv := run_valid (M := V) (B := B) input 1
  simp only [runBoundary, runStateAt, hv.start_q (by decide), hv.start_off (by decide)]

/-- Pulling an address through the compiled final column is exactly inverse permutation lookup. -/
theorem last_prefix_conjugate {m W : ℕ} [NeZero m] {X : Type*}
    (e : X ≃ Routing.Addr m) (p : Equiv.Perm X) (s : Routing.Settings m)
    (hs : Routing.route s = e.permCongr p) (src : X → Fin W → Bool) (y : X) :
    prefixWord s (fun x => src (e.symm x)) (2 * m - 1) (e y) = src (p.symm y) := by
  change src (e.symm ((Routing.route s).symm (e y))) = _
  have hp : (e.permCongr p).symm (e y) = e (p.symm y) := by
    apply (e.permCongr p).injective
    simp only [Equiv.apply_symm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hs, hp, Equiv.symm_apply_apply]

theorem last_arc_eq_prefix {m W : ℕ} [NeZero m] (s : Routing.Settings m)
    (src : Routing.Addr m → Fin W → Bool) (x : Routing.Addr m) :
    canonicalArc s src (2 * m - 1) x false = prefixWord s src (2 * m - 1) x := by
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [canonicalArc, if_pos (show 2 * m - 1 + 1 = 2 * m by omega), Bool.false_eq_true, ↓reduceIte]

end P1Net.AstraContract
