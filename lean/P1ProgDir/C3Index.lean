import P1ProgDir.Readbacks

namespace P1ProgDir.SolC3Index

open P1ChkDir P1Wit P1ProgDir.SolReadbacks

theorem interval_lt (D : Dims) {z : ℕ} (h : z < D.I * D.r * 3 * 2) :
    z / 2 / 3 / D.r < D.I := by
  apply Nat.div_lt_of_lt_mul
  rw [Nat.mul_comm]
  apply Nat.div_lt_of_lt_mul
  apply Nat.div_lt_of_lt_mul
  calc
    z < D.I * D.r * 3 * 2 := h
    _ = 2 * (3 * (D.I * D.r)) := by ring

theorem c3_readback {K : Type} (D : Dims) (tape : K ≃ Fin D.r) (u : List Bool)
    {z : ℕ} (h : z < D.I * D.r * 3 * 2) :
    C3F D tape u z ↔
      let i : Fin D.I := ⟨z / 2 / 3 / D.r, interval_lt D h⟩
      let k := z / 2 / 3 % D.r
      let δ := z / 2 % 3
      let nx := decide (z % 2 = 1)
      ∃ link : Option (Fin D.I),
        readField D u (if nx then secNext else secPrev) (z / 2) = ownToN link ∧
        linkValid (fun j =>
          OwnsB D.N (unzigzag (rdStart D u j k))
            (bigOf D.N (unzigzag (readField D u secStart (z / 2 / 3))) - 1 + (δ : ℤ))) i nx link := by
  have hr : 0 < D.r := by
    by_contra! hz
    have hzero : D.r = 0 := by omega
    simp [hzero] at h
  let i : Fin D.I := ⟨z / 2 / 3 / D.r, interval_lt D h⟩
  let k : Fin D.r := ⟨z / 2 / 3 % D.r, Nat.mod_lt _ hr⟩
  let δ : Fin 3 := ⟨z / 2 % 3, Nat.mod_lt _ (by decide)⟩
  let nx := decide (z % 2 = 1)
  have hc : C3F D tape u z ↔ C3 (dirP6 D tape) u i (tape.symm k) δ nx :=
    ⟨fun hh => hh h, fun hh _ => hh⟩
  rw [hc, c3_local_readback]
  dsimp only
  have hi : (i : ℕ) * D.r + (k : ℕ) = z / 2 / 3 :=
    flat_index _ _ hr
  have hz : z / 2 / 3 * 3 + (δ : ℕ) = z / 2 :=
    flat_index _ _ (by decide)
  simp only [Equiv.apply_symm_apply, rdStart, hi, rdNext, rdPrev, hz]
  change (∃ link : Option (Fin D.I),
    (if nx then readField D u secNext (z / 2) else readField D u secPrev (z / 2)) = _ ∧ _) ↔ _
  have hread (b : Bool) :
      (if b then readField D u secNext (z / 2) else readField D u secPrev (z / 2)) =
        readField D u (if b then secNext else secPrev) (z / 2) := by
    cases b <;> rfl
  rw [hread]

end P1ProgDir.SolC3Index
