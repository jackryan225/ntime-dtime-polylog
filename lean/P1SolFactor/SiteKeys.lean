import P1SolFactor.HalfPacking
import P1SolFactor.RowLookup

namespace P1SolFactor.SolHalf

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open scoped Classical

noncomputable section

private theorem binaryValue_inj_of_length {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hval : SolRows.binaryValue id xs = SolRows.binaryValue id ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      have hlen' : xs.length = ys.length := Nat.succ.inj hlen
      cases b <;> cases c <;>
        simp only [SolRows.binaryValue, id_eq, Bool.toNat_true, Bool.toNat_false] at hval
      · exact congrArg (List.cons false) (ih hlen' (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hlen' (by omega))

/-- Fixed-width little-endian decoding recovers every list of the prescribed width. -/
theorem testBits_binaryValue (xs : List Bool) (w : ℕ) (hlen : xs.length = w) :
    (List.ofFn fun i : Fin w => (SolRows.binaryValue id xs).testBit i.val) = xs := by
  subst w
  apply binaryValue_inj_of_length List.length_ofFn
  exact SolRows.binaryValue_testBits id id (fun _ => rfl) _ _ (SolRows.binaryValue_lt id xs)

/-- The table index of a fixed-width word. -/
def wordIndex (w : ℕ) (xs : List Bool) (hlen : xs.length = w) : Fin (2 ^ w) :=
  ⟨SolRows.binaryValue id xs, hlen ▸ SolRows.binaryValue_lt id xs⟩

theorem testBits_wordIndex (w : ℕ) (xs : List Bool) (hlen : xs.length = w) :
    (List.ofFn fun j : Fin w => (wordIndex w xs hlen).val.testBit j.val) = xs :=
  testBits_binaryValue xs w hlen

section Half

variable {a h : ℕ} (X : State a h) (u : X.network.Site)

/-- The half-label at a table index, in the order read by the level-0 evaluator. -/
def halfOfIndex (i : Fin (2 ^ halfWidthSum X u)) : X.network.Half u :=
  unpackHalf X u (List.ofFn fun j : Fin (halfWidthSum X u) => i.val.testBit j.val)

theorem halfOfIndex_wordIndex (xs : List Bool) (hlen : xs.length = halfWidthSum X u) :
    halfOfIndex X u (wordIndex (halfWidthSum X u) xs hlen) = unpackHalf X u xs := by
  rw [halfOfIndex, testBits_wordIndex]

theorem halfOfIndex_surjective : Function.Surjective (halfOfIndex X u) := by
  intro z
  refine ⟨wordIndex _ (packHalf X u z) (packHalf_length X u z), ?_⟩
  exact (halfOfIndex_wordIndex X u _ _).trans (unpackHalf_packHalf X u z)

theorem halfOfIndex_injective : Function.Injective (halfOfIndex X u) := by
  let e : Fin (2 ^ halfWidthSum X u) ≃ X.network.Half u :=
    Fintype.equivOfCardEq ((Fintype.card_fin _).trans (card_half_exact X u).symm)
  have hsurj : Function.Surjective (e.symm ∘ halfOfIndex X u) :=
    e.symm.surjective.comp (halfOfIndex_surjective X u)
  have hinj : Function.Injective (e.symm ∘ halfOfIndex X u) :=
    Finite.injective_iff_surjective.mpr hsurj
  intro i j heq
  exact hinj (congrArg e.symm heq)

theorem packHalf_unpackHalf (xs : List Bool) (hlen : xs.length = halfWidthSum X u) :
    packHalf X u (unpackHalf X u xs) = xs := by
  let z := unpackHalf X u xs
  let ys := packHalf X u z
  have hy : ys.length = halfWidthSum X u := packHalf_length X u z
  have he :
      halfOfIndex X u (wordIndex _ ys hy) = halfOfIndex X u (wordIndex _ xs hlen) := by
    rw [halfOfIndex_wordIndex, halfOfIndex_wordIndex]
    exact unpackHalf_packHalf X u z
  have hi := halfOfIndex_injective X u he
  calc
    ys = (List.ofFn fun j : Fin (halfWidthSum X u) => (wordIndex _ ys hy).val.testBit j.val) :=
      (testBits_wordIndex _ ys hy).symm
    _ = (List.ofFn fun j : Fin (halfWidthSum X u) => (wordIndex _ xs hlen).val.testBit j.val) :=
      congrArg (fun i : Fin (2 ^ halfWidthSum X u) =>
        List.ofFn fun j : Fin (halfWidthSum X u) => i.val.testBit j.val) hi
    _ = xs := testBits_wordIndex _ xs hlen

theorem siteKeys_length : (siteKeys X u).length = 2 ^ halfWidthSum X u := List.length_ofFn

theorem siteKeys_nodup : (siteKeys X u).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact halfOfIndex_injective X u (eq_of_heq (Sigma.mk.inj hij).2)

theorem siteKeys_mem (z : X.network.Half u) : (⟨u, z⟩ : P1P5.Key X.network) ∈ siteKeys X u := by
  obtain ⟨i, hi⟩ := halfOfIndex_surjective X u z
  apply List.mem_ofFn.mpr
  exact ⟨i, congrArg (fun q : X.network.Half u => (⟨u, q⟩ : P1P5.Key X.network)) hi⟩

theorem siteKeys_only (k : P1P5.Key X.network) (hk : k ∈ siteKeys X u) : k.1 = u := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hk
  exact (congrArg Sigma.fst hi).symm

theorem siteKeys_getElem (i : Fin (2 ^ halfWidthSum X u)) :
    (siteKeys X u)[i.val]'(by rw [siteKeys_length]; exact i.isLt) = ⟨u, halfOfIndex X u i⟩ := by
  simp only [siteKeys, List.getElem_ofFn, halfOfIndex]

end Half

end

end P1SolFactor.SolHalf
