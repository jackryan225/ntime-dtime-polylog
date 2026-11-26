import P1Net.AccessPerm

/-! A single block history for the access permutation and the links between big intervals. -/

namespace P1Net.AstraContract

section History

variable {K : Type} {P : Type*} {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (Z : ℤ)
  (initial : P) (write : ℕ → P)

/-- The content just before small interval `t`, given every table's write to this block. -/
def valueAt (t : ℕ) : P :=
  match prevAccess σ k Z t with
  | none => initial
  | some j => write j

theorem valueAt_zero : valueAt σ k Z initial write 0 = initial := rfl

theorem valueAt_hit {t : ℕ} (hw : InWindow (betaOf σ k t) Z) :
    valueAt σ k Z initial write (t + 1) = write t := by
  simp only [valueAt, prevAccess, if_pos hw]

theorem valueAt_miss {t : ℕ} (hw : ¬ InWindow (betaOf σ k t) Z) :
    valueAt σ k Z initial write (t + 1) = valueAt σ k Z initial write t := by
  simp only [valueAt, prevAccess, if_neg hw]

/-- In a time interval with no access the two boundary values agree. -/
theorem valueAt_gap (lo : ℕ) : ∀ hi, lo ≤ hi →
    (∀ t, lo ≤ t → t < hi → ¬ InWindow (betaOf σ k t) Z) →
    valueAt σ k Z initial write hi = valueAt σ k Z initial write lo := by
  intro hi
  induction hi with
  | zero =>
    intro hle _
    have h : lo = 0 := by omega
    rw [h]
  | succ hi ih =>
    intro hle hgap
    by_cases h : lo = hi + 1
    · rw [h]
    · have hle' : lo ≤ hi := by omega
      rw [valueAt_miss σ k Z initial write (hgap hi hle' (by omega))]
      exact ih hle' (fun t ht ht' => hgap t ht (by omega))

theorem valueAt_map {P' : Type*} (f : P → P') (t : ℕ) :
    valueAt σ k Z (f initial) (fun j => f (write j)) t = f (valueAt σ k Z initial write t) := by
  unfold valueAt
  cases prevAccess σ k Z t <;> rfl

end History

section BigInterval

variable {K : Type} [Fintype K] [DecidableEq K] {P : Type*} {h : ℕ}
  (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K) (Z : ℤ)
  (initial : P) (write : ℕ → P)

/-- Evaluate a cut inside a big interval from its last earlier accessing lane. -/
private theorem valueAt_cut (cut : ℕ) (hcut : cut ≤ 2 ^ h) (p : Option (Fin (2 ^ h)))
    (hnone : p = none → ∀ j : Fin (2 ^ h), (j : ℕ) < cut → ¬ Acc I σ ι k j Z)
    (hsome : ∀ j : Fin (2 ^ h), p = some j →
      (j : ℕ) < cut ∧ Acc I σ ι k j Z ∧
        ∀ j' : Fin (2 ^ h), (j' : ℕ) < cut → Acc I σ ι k j' Z → j' ≤ j) :
    valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h + cut) =
      match (generalizing := false) p with
      | some j => write ((ι : ℕ) * 2 ^ h + j)
      | none => valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h) := by
  let start : ℕ := (ι : ℕ) * 2 ^ h
  have lane {t : ℕ} (hlo : start ≤ t) (hhi : t < start + cut) :
      ∃ j : Fin (2 ^ h), (j : ℕ) < cut ∧ start + j = t := by
    exact ⟨⟨t - start, by omega⟩, by dsimp only; omega, by dsimp only; omega⟩
  cases p with
  | none =>
    apply valueAt_gap σ k Z initial write start (start + cut) (by omega)
    intro t hlo hhi hw
    obtain ⟨j, hj, hjt⟩ := lane hlo hhi
    apply hnone rfl j hj
    change InWindow (betaOf σ k (start + j)) Z
    rwa [hjt]
  | some j =>
    obtain ⟨hj, hw, hmax⟩ := hsome j rfl
    calc
      valueAt σ k Z initial write (start + cut) =
          valueAt σ k Z initial write ((start + j) + 1) := by
        apply valueAt_gap σ k Z initial write _ _ (by omega)
        intro t hlo hhi ht
        obtain ⟨j', hj', hjt⟩ := lane (by omega : start ≤ t) hhi
        have ha : Acc I σ ι k j' Z := by
          change InWindow (betaOf σ k (start + j')) Z
          rwa [hjt]
        have hm : (j' : ℕ) ≤ j := hmax j' hj' ha
        omega
      _ = write (start + j) := valueAt_hit σ k Z initial write hw

/-- A table input sees the previous access within this big interval, or the incoming port. -/
theorem valueAt_lane (j : Fin (2 ^ h)) :
    valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h + j) =
      match prevAcc I σ ι k Z j with
      | some u => write ((ι : ℕ) * 2 ^ h + u)
      | none => valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h) := by
  apply valueAt_cut I σ ι k Z initial write j j.isLt.le (prevAcc I σ ι k Z j)
  · exact fun hp u hu => prevAcc_none hp u hu
  · exact fun _ hp => prevAcc_spec hp

/-- An outgoing port sees the last table write, or the unchanged incoming port. -/
theorem valueAt_end :
    valueAt σ k Z initial write (((ι : ℕ) + 1) * 2 ^ h) =
      match lastAcc I σ ι k Z with
      | some u => write ((ι : ℕ) * 2 ^ h + u)
      | none => valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h) := by
  rw [Nat.succ_mul]
  apply valueAt_cut I σ ι k Z initial write (2 ^ h) le_rfl (lastAcc I σ ι k Z)
  · exact fun hp u _ => lastAcc_none hp u
  · intro u hp
    obtain ⟨hw, hmax⟩ := lastAcc_spec hp
    exact ⟨u.isLt, hw, fun j _ ha => hmax j ha⟩

/-- Ownership at the quotient time of an access. The small block number may be negative. -/
theorem owns_at_time {t : ℕ} (ht : t < I * 2 ^ h) (hw : InWindow (betaOf σ k t) Z) :
    Owns I σ k (t / 2 ^ h) (Z / 2 ^ h) := by
  have hN := Nat.two_pow_pos h
  let owner : Fin I := ⟨t / 2 ^ h, (Nat.div_lt_iff_lt_mul hN).2 ht⟩
  let j : Fin (2 ^ h) := ⟨t % 2 ^ h, Nat.mod_lt _ hN⟩
  have ha : Acc I σ owner k j Z := by
    change InWindow (betaOf σ k (t / 2 ^ h * 2 ^ h + t % 2 ^ h)) Z
    rwa [Nat.div_add_mod']
  obtain ⟨hlo, hhi⟩ := window_in_owned I σ owner k j ha
  have hNZ : (0 : ℤ) < 2 ^ h := by positivity
  change bigQ I σ k owner - 1 ≤ Z / 2 ^ h ∧ Z / 2 ^ h ≤ bigQ I σ k owner + 1
  have hb : Z / 2 ^ h < bigQ I σ k owner + 2 := (Int.ediv_lt_iff_lt_mul hNZ).2 hhi
  exact ⟨(Int.le_ediv_iff_mul_le hNZ).2 hlo, by omega⟩

/-- Skipping big intervals that do not own this block preserves its contents. -/
theorem valueAt_owner_gap (lo hi : ℕ) (hle : lo ≤ hi) (hI : hi ≤ I)
    (hgap : ∀ j : Fin I, lo ≤ (j : ℕ) → (j : ℕ) < hi → ¬ Owns I σ k j (Z / 2 ^ h)) :
    valueAt σ k Z initial write (hi * 2 ^ h) = valueAt σ k Z initial write (lo * 2 ^ h) := by
  apply valueAt_gap σ k Z initial write _ _ (Nat.mul_le_mul_right _ hle)
  intro t hlo hhi hw
  have hN := Nat.two_pow_pos h
  have hq : t / 2 ^ h < hi := (Nat.div_lt_iff_lt_mul hN).2 hhi
  have hq' : lo ≤ t / 2 ^ h := (Nat.le_div_iff_mul_le hN).2 hlo
  have ht : t < I * 2 ^ h := lt_of_lt_of_le hhi (Nat.mul_le_mul_right _ hI)
  exact hgap ⟨t / 2 ^ h, by omega⟩ hq' hq (owns_at_time I σ k Z ht hw)

theorem no_owner_before_of_none {Q : ℤ} (hp : prevOwner I σ k ι Q = none) (j : Fin I)
    (hj : j < ι) : ¬ Owns I σ k j Q := by
  intro howns
  have hex : (Finset.univ.filter fun u : Fin I => u < ι ∧ Owns I σ k u Q).Nonempty :=
    ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj, howns⟩⟩
  rw [prevOwner, dif_pos hex] at hp
  cases hp

/-- Value at the start of an owner, including intervening owners that never access the block. -/
theorem valueAt_owner :
    valueAt σ k Z initial write ((ι : ℕ) * 2 ^ h) =
      match prevOwner I σ k ι (Z / 2 ^ h) with
      | some j => valueAt σ k Z initial write (((j : ℕ) + 1) * 2 ^ h)
      | none => initial := by
  cases hp : prevOwner I σ k ι (Z / 2 ^ h) with
  | none =>
    have e := valueAt_owner_gap I σ k Z initial write 0 ι (Nat.zero_le _) ι.isLt.le
      (fun j _ hj => no_owner_before_of_none I σ ι k hp j hj)
    simpa only [Nat.zero_mul, valueAt_zero] using e
  | some j =>
    obtain ⟨hlt, _, hmax⟩ := prevOwner_spec hp
    apply valueAt_owner_gap I σ k Z initial write ((j : ℕ) + 1) ι hlt ι.isLt.le
    intro j' hlo hhi ho
    have hm : (j' : ℕ) ≤ j := hmax j' hhi ho
    omega

end BigInterval

end P1Net.AstraContract
