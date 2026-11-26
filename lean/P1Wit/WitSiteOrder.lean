import P1Wit.Decode
import OAI.Computability.VPVNP.CompressionState
import OAI.Computability.VPVNP.BitSlotIndex

namespace P1Wit

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression

namespace SolWitfill

theorem lanes_pos {bases lanes : ℕ} (i : Fin (bases * lanes)) : 0 < lanes :=
  Nat.pos_of_ne_zero fun hz => by simpa [hz] using i.isLt

theorem div_lt {bases lanes : ℕ} (i : Fin (bases * lanes)) : i.val / lanes < bases :=
  (Nat.div_lt_iff_lt_mul (lanes_pos i)).mpr i.isLt

end SolWitfill

/-- D9: site numbers are in base-major order, with lane the inner coordinate. -/
def ord (bases lanes : ℕ) : Fin bases × Fin lanes ≃ Fin (bases * lanes) where
  toFun p := ⟨p.1.val * lanes + p.2.val, idx_lt p.1.isLt p.2.isLt⟩
  invFun i := (⟨i.val / lanes, SolWitfill.div_lt i⟩,
    ⟨i.val % lanes, Nat.mod_lt _ (SolWitfill.lanes_pos i)⟩)
  left_inv p := Prod.ext (Fin.ext (idx_div p.2.isLt)) (Fin.ext (idx_mod p.2.isLt))
  right_inv i := Fin.ext (div_mul_add_mod i.val lanes)

theorem ord_apply (bases lanes : ℕ) (p : Fin bases × Fin lanes) :
    (ord bases lanes p).val = p.1.val * lanes + p.2.val := rfl

theorem ord_symm_apply (bases lanes : ℕ) (i : Fin (bases * lanes)) :
    ((ord bases lanes).symm i).1.val = i.val / lanes ∧
      ((ord bases lanes).symm i).2.val = i.val % lanes :=
  ⟨rfl, rfl⟩

theorem ord_bijective (bases lanes : ℕ) : Function.Bijective (ord bases lanes) :=
  (ord bases lanes).bijective

/-- D9 on the actual final sites used by `P1Count.NetData.ofExec`. -/
noncomputable def stateOrd {a g : ℕ} (X : State a g) :
    X.network.Site ≃ Fin (Fintype.card X.network.Site) :=
  ((X.baseIndex.prodCongr (bitWordFinEquiv g)).trans (ord _ _)).trans
    (finCongr (by
      change Fintype.card X.Base * 2 ^ g = Fintype.card (X.Base × BitWord g)
      rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv g), Fintype.card_fin]))

theorem stateOrd_apply {a g : ℕ} (X : State a g) (y : X.Base) (l : BitWord g) :
    (stateOrd X (y, l)).val = (X.baseIndex y).val * 2 ^ g + (bitWordFinEquiv g l).val :=
  rfl

theorem stateOrd_symm_apply {a g : ℕ} (X : State a g) (i : Fin (Fintype.card X.network.Site)) :
    (X.baseIndex ((stateOrd X).symm i).1).val = i.val / 2 ^ g ∧
      (bitWordFinEquiv g ((stateOrd X).symm i).2).val = i.val % 2 ^ g := by
  change (X.baseIndex (X.baseIndex.symm _)).val = _ ∧
    (bitWordFinEquiv g ((bitWordFinEquiv g).symm _)).val = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩


theorem stateOrd_bijective {a g : ℕ} (X : State a g) :
    Function.Bijective (stateOrd X) :=
  (stateOrd X).bijective

end P1Wit

#print axioms P1Wit.ord
#print axioms P1Wit.ord_apply
#print axioms P1Wit.ord_symm_apply
#print axioms P1Wit.ord_bijective
#print axioms P1Wit.stateOrd
#print axioms P1Wit.stateOrd_apply
#print axioms P1Wit.stateOrd_symm_apply
#print axioms P1Wit.stateOrd_bijective
