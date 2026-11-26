import P1Int.FormDefs

/-!
# The genuine level parameters `ag` (P1-lean-integ, 2026-11-25)

The families `C6fam`, `C7fam`, `C8fam` and the format facts `FmtHypTags`, `FmtHypMotif` take
`ag : ℕ → ℕ → ℕ × ℕ`, `ag n ℓ = (a, g)`, with the state of a shrinking level `ℓ` of type
`State a (packingLaneBits a g)`.

At the genuine dims every row is `levelDims e degree laneCount positions shrink` (`P1Wit.SolSpace`), so
`slotW = degree = a` and `laneW = laneCount`; at a shrinking level the lane count of the state is
`packingLaneBits a g` with `g` the lane count of the next level (`shrinkPassAt`, `packingLaneBits_add`).
Hence `ag n ℓ := ((dims n).lv ℓ).slotW, ((dims n).lv ℓ).laneW - packingLaneBits ((dims n).lv ℓ).slotW 0)`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP.Compression

/-- The level parameters `(a, g)` of level `ℓ` of the dims `D`. -/
def agOf (D : P1Wit.Dims) (ℓ : ℕ) : ℕ × ℕ :=
  ((D.lv ℓ).slotW, (D.lv ℓ).laneW - packingLaneBits (D.lv ℓ).slotW 0)

/-- **The genuine `ag`** for a dims function (`dims n` = the genuine dims at input length `n`). -/
def genuineAg (dims : ℕ → P1Wit.Dims) : ℕ → ℕ → ℕ × ℕ := fun n ℓ => agOf (dims n) ℓ

/-- Sanity: the lane count of the state type is the stored lane width, when the width holds the packing loss. -/
theorem packingLaneBits_agOf (D : P1Wit.Dims) (ℓ : ℕ)
    (h : packingLaneBits (D.lv ℓ).slotW 0 ≤ (D.lv ℓ).laneW) :
    packingLaneBits (agOf D ℓ).1 (agOf D ℓ).2 = (D.lv ℓ).laneW := by
  unfold agOf
  dsimp only
  rw [← packingLaneBits_add]
  exact Nat.add_sub_cancel' h

/-- Sanity: `ag` at the fixed parameters is `agOf fixedDims` (the dims function of the checks lane is `fixedDims` at
`n = |x|`). -/
example {k : Type*} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) (ℓ : ℕ) :
    genuineAg (fun n => P1Wit.SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1 (lpTime a b n)
        (a * (n ^ 2 + 1)) d bigBias termBias) x.length ℓ =
      agOf (fixedDims Bt V a b x d bigBias termBias) ℓ := rfl

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
  (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)

/-- **Group `c4` (C4, the level-0 panel)**: some tuple agrees with `u` on the trit section and on the panel sections
of level `0` (the premise of the greedy step at level `0`, as `c10G (l - 1)` is for level `l ≥ 1`). -/
def c4G (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∃ t : (fixedCD Bt κ hκ V a b x).Tup d, SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit ∧
    ∀ kk : P1Wit.Mem, panelKind kk = true →
      SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev 0 kk)

end

end P11

end P1Int
