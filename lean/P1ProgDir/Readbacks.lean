import P1ChkDir.P6
import P1ChkDir.C14
import P1Batch.Statement

namespace P1ProgDir.SolReadbacks

open P1ChkDir P1Wit

variable {K : Type} (D : Dims) (tape : K ≃ Fin D.r) (u : List Bool)

theorem flat_index (i r : ℕ) (_hr : 0 < r) :
    i / r * r + i % r = i := by
  have h := Nat.mod_add_div i r
  rw [Nat.mul_comm] at h
  omega

theorem c1_readback (i : ℕ) :
    C1F D tape u i ↔ D.I * D.N * D.r ≤ i ∨ readField D u secTrit i < 3 := by
  by_cases hi : i < D.I * D.N * D.r
  · have hr : 0 < D.r := by
      by_contra! hz
      have hzero : D.r = 0 := by omega
      simp [hzero] at hi
    have aux (h : i < D.I * D.N * D.r) :
        C1 (dirP6 D tape) u
          ⟨i / D.r, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩
          (tape.symm ⟨i % D.r, Nat.mod_lt _ hr⟩) ↔ readField D u secTrit i < 3 := by
      rw [dirP6_C1_iff]
      simp only [rdTrit, Equiv.apply_symm_apply, flat_index _ _ hr]
    unfold C1F
    rw [or_iff_right (by omega)]
    exact ⟨fun h => (aux hi).mp (h hi), fun h hj => (aux hj).mpr h⟩
  · exact iff_of_true (C1F_out D tape u (by omega)) (Or.inl (by omega))

/-- The section-4 layout needed by the C14 readback. -/
def guessSection (kIn : K) (blk : Fin D.nGB → ℤ) : GuessDir K D.nGB where
  kIn := kIn
  blk := blk
  off q := D.off secGuess + (q : ℕ) * D.width secGuess

theorem c14_readback (kIn : K) (blk : Fin D.nGB → ℤ) (i : Fin D.nGB) :
    C14 (dirP6 D tape) (guessSection D kIn blk) u i ↔
      ∃ j : Fin D.I, rdGuess D u i = (j : ℕ) + 1 ∧
        ∃ δ : Fin 3,
          blk i = bigOf D.N (unzigzag (rdStart D u j (tape kIn))) - 1 + (δ : ℤ) ∧
          rdPrev D u j (tape kIn) δ = 0 := by
  have hg : gOwnS (dirP6 D tape) (guessSection D kIn blk) u i =
      ownOfN D.I (rdGuess D u i) := by
    have hw : D.width secGuess = D.bigW := rfl
    simp only [gOwnS, dirP6, guessSection, ownCode, numCode_read, rdGuess, readField, hw]
  unfold C14
  simp only [hg, dirP6_betaS, dirP6_prevS, Option.some.injEq]
  simp only [guessSection]
  constructor
  · rintro ⟨j, b, δ, hj, rfl, hd, hp⟩
    have hj' := ownOfN_eq hj
    have hp' := ownOfN_eq hp
    change (j : ℕ) + 1 = rdGuess D u i at hj'
    change 0 = rdPrev D u j (tape kIn) δ at hp'
    exact ⟨j, hj'.symm, δ, hd, hp'.symm⟩
  · rintro ⟨j, hj, δ, hd, hp⟩
    refine ⟨j, _, δ, ?_, rfl, hd, ?_⟩
    · rw [hj]
      exact ownOfN_toN (some j)
    · rw [hp]
      exact ownOfN_toN (none : Option (Fin D.I))

def tritDelta (v : ℕ) : ℤ := if v < 3 then (v : ℤ) - 1 else 0

theorem tritDelta_eq (j : Fin (D.I * D.N)) (k : K) :
    (((dirP6 D tape).sigmaS u j k : ℕ) : ℤ) - 1 =
      tritDelta (rdTrit D u j (tape k)) := by
  rw [dirP6_sigmaS]
  unfold tritOfN tritDelta
  split_ifs <;> rfl

theorem trSum_readback (j : Fin D.I) (k : K) :
    trSum D.N ((dirP6 D tape).sigmaS u) k j =
      ∑ g ∈ Finset.range D.N, tritDelta (rdTrit D u ((j : ℕ) * D.N + g) (tape k)) := by
  unfold trSum
  apply Finset.sum_congr rfl
  intro g hg
  have hg' := Finset.mem_range.mp hg
  have hJ : (j : ℕ) + 1 ≤ D.I := j.isLt
  have hj : (j : ℕ) * D.N + g < D.I * D.N := by
    calc
      _ < ((j : ℕ) + 1) * D.N := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hJ
  rw [sig, dite_eq_left hj]
  exact tritDelta_eq D tape u ⟨_, hj⟩ k

theorem c2_local_readback (j : Fin D.I) (k : K) :
    C2 (dirP6 D tape) u j k ↔
      if (j : ℕ) = 0 then unzigzag (rdStart D u j (tape k)) = 0 else
        unzigzag (rdStart D u j (tape k)) =
          unzigzag (rdStart D u ((j : ℕ) - 1) (tape k)) +
            ∑ g ∈ Finset.range D.N,
              tritDelta (rdTrit D u (((j : ℕ) - 1) * D.N + g) (tape k)) := by
  unfold C2
  split_ifs with hj
  · simp only [dirP6_betaS, Option.some.injEq]
  · have hs := trSum_readback D tape u (predFin j) k
    change trSum D.N ((dirP6 D tape).sigmaS u) k ((j : ℕ) - 1) = _ at hs
    simp only [dirP6_betaS, Option.some.injEq, hs]
    exact ⟨fun ⟨_, h, he⟩ => h.symm ▸ he, fun h => ⟨_, rfl, h⟩⟩

theorem c2_readback (i : ℕ) :
    C2F D tape u i ↔
      D.I * D.r ≤ i ∨
        if i / D.r = 0 then unzigzag (readField D u secStart i) = 0 else
          unzigzag (readField D u secStart i) =
            unzigzag (rdStart D u (i / D.r - 1) (i % D.r)) +
              ∑ g ∈ Finset.range D.N,
                tritDelta (rdTrit D u ((i / D.r - 1) * D.N + g) (i % D.r)) := by
  by_cases hi : i < D.I * D.r
  · have hr : 0 < D.r := by
      by_contra! hz
      have hzero : D.r = 0 := by omega
      simp [hzero] at hi
    have aux (h : i < D.I * D.r) :=
      c2_local_readback D tape u
        ⟨i / D.r, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩
        (tape.symm ⟨i % D.r, Nat.mod_lt _ hr⟩)
    unfold C2F
    rw [or_iff_right (by omega)]
    exact ⟨fun h => by
      simpa only [Equiv.apply_symm_apply, rdStart, flat_index _ _ hr] using
        (aux hi).mp (h hi),
      fun h hj => (aux hj).mpr (by
        simpa only [Equiv.apply_symm_apply, rdStart, flat_index _ _ hr] using h)⟩
  · exact iff_of_true (C2F_out D tape u (by omega)) (Or.inl (by omega))

/-- The C14 address derived from the stored fields is used only after its range
checks. The offset into the owner window is computed by integer subtraction. -/
def guessDelta (D : Dims) (t : ℕ) (u : List Bool) (Q : ℤ) (owner : ℕ) : ℤ :=
  Q - bigOf D.N (unzigzag (rdStart D u (owner - 1) t)) + 1

theorem c14_bounded_readback (kIn : K) (blk : Fin D.nGB → ℤ) (i : Fin D.nGB) :
    C14 (dirP6 D tape) (guessSection D kIn blk) u i ↔
      let owner := rdGuess D u i
      let delta := guessDelta D (tape kIn) u (blk i) owner
      0 < owner ∧ owner ≤ D.I ∧ 0 ≤ delta ∧ delta < 3 ∧
        rdPrev D u (owner - 1) (tape kIn) delta.toNat = 0 := by
  rw [c14_readback]
  dsimp only
  constructor
  · rintro ⟨j, hj, δ, hδ, hp⟩
    rw [hj]
    simp only [Nat.add_sub_cancel, guessDelta]
    have hval : blk i - bigOf D.N (unzigzag (rdStart D u j (tape kIn))) + 1 =
        ((δ : ℕ) : ℤ) := by omega
    rw [hval, Int.toNat_natCast]
    refine ⟨by omega, j.isLt, Int.natCast_nonneg _, ?_, hp⟩
    exact_mod_cast δ.isLt
  · rintro ⟨ho, hI, hδ0, hδ3, hp⟩
    let j : Fin D.I := ⟨rdGuess D u i - 1, by omega⟩
    let Δ := guessDelta D (tape kIn) u (blk i) (rdGuess D u i)
    let δ : Fin 3 := ⟨Δ.toNat, by
      have he : (Δ.toNat : ℤ) = Δ := Int.toNat_of_nonneg hδ0
      exact_mod_cast (he.trans_lt hδ3)⟩
    refine ⟨j, by change rdGuess D u i = rdGuess D u i - 1 + 1; omega, δ, ?_, hp⟩
    have he : (δ : ℤ) = Δ := Int.toNat_of_nonneg hδ0
    rw [he]
    unfold Δ guessDelta
    change blk i = bigOf D.N (unzigzag (rdStart D u j (tape kIn))) - 1 +
      (blk i - bigOf D.N (unzigzag (rdStart D u j (tape kIn))) + 1)
    omega

section Order

variable {I : ℕ}

/-- Local tests for the extrema computed by the directory definition. -/
theorem min_link (s : Finset (Fin I)) (a : Option (Fin I)) :
    (if hs : s.Nonempty then some (s.min' hs) else none) = a ↔
      match a with
      | none => ∀ j, j ∉ s
      | some j => j ∈ s ∧ ∀ k ∈ s, j ≤ k := by
  cases a with
  | none =>
    split_ifs with hs
    · obtain ⟨j, hj⟩ := hs
      simp only [false_iff]
      exact fun h => h j hj
    · exact ⟨fun _ j hj => hs ⟨j, hj⟩, fun _ => rfl⟩
  | some j =>
    split_ifs with hs
    · rw [Option.some.injEq]
      exact ⟨fun h => h ▸ ⟨Finset.min'_mem _ hs, fun k hk => Finset.min'_le _ _ hk⟩,
        fun ⟨hj, h⟩ => le_antisymm (Finset.min'_le _ _ hj) (h _ (Finset.min'_mem _ hs))⟩
    · simp only [false_iff]
      exact fun h => hs ⟨j, h.1⟩

theorem max_link (s : Finset (Fin I)) (a : Option (Fin I)) :
    (if hs : s.Nonempty then some (s.max' hs) else none) = a ↔
      match a with
      | none => ∀ j, j ∉ s
      | some j => j ∈ s ∧ ∀ k ∈ s, k ≤ j := by
  cases a with
  | none =>
    split_ifs with hs
    · obtain ⟨j, hj⟩ := hs
      simp only [false_iff]
      exact fun h => h j hj
    · exact ⟨fun _ j hj => hs ⟨j, hj⟩, fun _ => rfl⟩
  | some j =>
    split_ifs with hs
    · rw [Option.some.injEq]
      exact ⟨fun h => h ▸ ⟨Finset.max'_mem _ hs, fun k hk => Finset.le_max' _ _ hk⟩,
        fun ⟨hj, h⟩ => le_antisymm (h _ (Finset.max'_mem _ hs)) (Finset.le_max' _ _ hj)⟩
    · simp only [false_iff]
      exact fun h => hs ⟨j, h.1⟩

end Order

/-- Specification of the validation conditions for one full scan. -/
def linkValid {I : ℕ} (owns : Fin I → Prop) (i : Fin I) (nx : Bool)
    (o : Option (Fin I)) : Prop :=
  let onSide := fun j => if nx then i < j else j < i
  match o with
  | none => ∀ j, onSide j → ¬ owns j
  | some v =>
    onSide v ∧ owns v ∧
      ∀ j, onSide j → (if nx then j < v else v < j) → ¬ owns j

theorem scans_iff {I N : ℕ} (β : Fin I → Option ℤ) (i : Fin I) (Q : ℤ) (nx : Bool)
    (o : Option (Fin I)) :
    (if nx then nextScan β N i Q else prevScan β N i Q) = o ↔
      linkValid (fun j => ownsTab β N j Q = true) i nx o := by
  cases nx
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold prevScan
    rw [max_link]
    cases o with
    | none =>
      simp only [linkValid, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter,
        Finset.mem_univ, true_and, not_and]
    | some v =>
      simp only [linkValid, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hv, hown⟩, h⟩
        exact ⟨hv, hown, fun j hj hjv hjown => (not_le_of_gt hjv) (h j ⟨hj, hjown⟩)⟩
      · rintro ⟨hv, hown, h⟩
        refine ⟨⟨hv, hown⟩, fun j hj => ?_⟩
        exact le_of_not_gt fun hjv => h j hj.1 hjv hj.2
  · simp only [↓reduceIte]
    unfold nextScan
    rw [min_link]
    cases o with
    | none =>
      simp only [linkValid, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    | some v =>
      simp only [linkValid, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hv, hown⟩, h⟩
        exact ⟨hv, hown, fun j hj hjv hjown => (not_le_of_gt hjv) (h j ⟨hj, hjown⟩)⟩
      · rintro ⟨hv, hown, h⟩
        refine ⟨⟨hv, hown⟩, fun j hj => ?_⟩
        exact le_of_not_gt fun hjv => h j hj.1 hjv hj.2

theorem c3_local_readback (i : Fin D.I) (k : K) (δ : Fin 3) (nx : Bool) :
    C3 (dirP6 D tape) u i k δ nx ↔
      ∃ o : Option (Fin D.I),
        (if nx then rdNext D u i (tape k) δ else rdPrev D u i (tape k) δ) = ownToN o ∧
        linkValid (fun j =>
          OwnsB D.N (unzigzag (rdStart D u j (tape k)))
            (bigOf D.N (unzigzag (rdStart D u i (tape k))) - 1 + (δ : ℤ))) i nx o := by
  let β := fun j : Fin D.I => (dirP6 D tape).betaS u j k
  let Q := bigOf D.N (unzigzag (rdStart D u i (tape k))) - 1 + (δ : ℤ)
  let code := if nx then rdNext D u i (tape k) δ else rdPrev D u i (tape k) δ
  have he : (fun j => ownsTab β D.N j Q = true) =
      (fun j : Fin D.I => OwnsB D.N (unzigzag (rdStart D u j (tape k))) Q) := by
    funext j
    simp only [β, dirP6_betaS, ownsTab, decide_eq_true_eq]
  have hcheck : C3 (dirP6 D tape) u i k δ nx ↔
      ownOfN D.I code = some (if nx then nextScan β D.N i Q else prevScan β D.N i Q) := by
    cases nx <;> simp only [C3, dirP6_betaS, Option.some.injEq, exists_eq_left',
      dirP6_nextS, dirP6_prevS, code, Bool.false_eq_true, ↓reduceIte, β, Q]
  rw [hcheck]
  constructor
  · intro h
    refine ⟨_, (ownOfN_eq h).symm, ?_⟩
    rw [← he]
    exact (scans_iff _ _ _ _ _).mp rfl
  · rintro ⟨o, hcode, hvalid⟩
    rw [← he] at hvalid
    have hs := (scans_iff _ _ _ _ _).mpr hvalid
    change code = ownToN o at hcode
    rw [hcode, hs, ownOfN_toN]


/-- Check ownership using two comparisons on the stored start block, with fixed
thresholds for the whole scan. The upper threshold is exclusive. -/
theorem ownsB_linear (N : ℕ) (hN : 0 < N) (b Q : ℤ) :
    OwnsB N b Q ↔ (N : ℤ) * (Q - 1) ≤ b ∧ b < (N : ℤ) * (Q + 2) := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  unfold OwnsB bigOf
  have h1 : (N : ℤ) * (Q - 1) ≤ b ↔ Q - 1 ≤ b / (N : ℤ) := by
    rw [mul_comm, Int.le_ediv_iff_mul_le hNz]
  have h2 : b < (N : ℤ) * (Q + 2) ↔ b / (N : ℤ) < Q + 2 := by
    rw [mul_comm, Int.ediv_lt_iff_lt_mul hNz]
  rw [h1, h2]
  omega

#print axioms c1_readback
#print axioms c2_readback
#print axioms c3_local_readback
#print axioms c14_bounded_readback

end P1ProgDir.SolReadbacks
