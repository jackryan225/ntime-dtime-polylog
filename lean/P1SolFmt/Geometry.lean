import P1SolFmt.ScheduleMath

namespace P1SolFmt.SolGeometry

open SolSchedule

variable {A L : Type*}

/-- Evaluate a row from the full blocks and the prefix of the block preceding its phase. -/
def indexedBlockRow (block : List A) (build : ℕ → ℕ → Option A → L)
    (divisor loss : A → ℕ) (fallback : L) (p g t i : ℕ) : L :=
  let blockPrefix := block.take (i % block.length)
  let laneLoss := (block.map loss).sum * (i / block.length) + (blockPrefix.map loss).sum
  let positionDivisor := (block.map divisor).prod ^ (i / block.length) * (blockPrefix.map divisor).prod
  if i ≤ block.length * t then
    build (p / positionDivisor) (g - laneLoss) ((blocks block t)[i]?)
  else fallback

theorem indexedBlockRows (block : List A) (build : ℕ → ℕ → Option A → L)
    (rows : ℕ → ℕ → List A → List L) (divisor loss : A → ℕ)
    (hnil : ∀ p g, rows p g [] = [build p g none])
    (hcons : ∀ p g ph xs, rows p g (ph :: xs) =
      build p g (some ph) :: rows (p / divisor ph) (g - loss ph) xs)
    (fallback : L) (p g t i : ℕ) :
    ((rows p g (blocks block t))[i]?).getD fallback =
      indexedBlockRow block build divisor loss fallback p g t i := by
  rw [indexedRows build rows divisor loss hnil hcons, blocks_length, indexedBlockRow]
  by_cases hi : i ≤ block.length * t
  · simp only [hi, ite_true]
    rw [blocks_take _ _ _ hi, List.map_append, List.map_append, List.sum_append, List.prod_append,
      blocks_sum, blocks_prod]
  · simp only [hi, ite_false]

end P1SolFmt.SolGeometry
