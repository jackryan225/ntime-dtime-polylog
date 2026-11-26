import P1SolFmt.Geometry
import P1SolFmt.LayoutFigures
import P1SolFmt.ScheduleProgram

namespace P1SolFmt.SolGeometry

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open P1Wit SolFigure SolSchedule

variable {X A : Type} {r : Regime X} {p g t i : X → ℕ}

/-- Field equations for a level builder evaluated by the row program. -/
def LevelBuilderSpec (expand : ℕ) (tagBits : ℕ → ℕ)
    (build : ℕ → ℕ → ℕ → Option Bool → LevelDims) : Prop :=
  ∀ degree laneCount positions kind, build degree laneCount positions kind =
    { bases := positions / 2 ^ laneCount
      slots := 2 ^ degree
      slotW := degree
      lanes := 2 ^ laneCount
      laneW := laneCount
      shrink := kind == some true
      colW := if kind = some true then Nat.clog 2 (2 * 2 ^ degree + 1) else 0
      tagW := if kind = some true then tagBits (2 ^ degree) else 0
      termKeys := match kind with
        | some true => 2 ^ laneCount * 2 ^ degree
        | some false => 2 ^ (laneCount - degree)
        | none => 0
      termArity := match kind with
        | some true => 8
        | some false => 2 ^ degree * 2 ^ expand
        | none => 0 }

/-- Evaluate any level row by computing the geometry of the schedule prefix at its index. -/
theorem rowFigures (block : List A) (hBlock : 0 < block.length)
    (degree lossFactor divisorFactor : A → ℕ) (shrink : A → Bool)
    (finalDegree expand : ℕ) (tagBits : ℕ → ℕ)
    (build : ℕ → ℕ → ℕ → Option Bool → LevelDims) (hBuild : LevelBuilderSpec expand tagBits build)
    (hp : Figure r p) (hg : Realizes r g) (ht : Realizes r t) (hi : Realizes r i) :
    LevelFigures r (fun x => indexedBlockRow block
      (fun p g phase => build (phase.elim finalDegree degree) g p (phase.map shrink))
      divisorFactor lossFactor (build 0 0 0 none) (p x) (g x) (t x) (i x)) := by
  unfold LevelBuilderSpec at hBuild
  let num := fun n => Carry.Figure.natural (r := r) n
  let fix := fun n => Staff.Realizes.fix (r := r) n
  let phase := fun x => (blocks block (t x))[i x]?
  let blockPrefix := fun x => block.take (i x % block.length)
  let loss := fun x => (block.map lossFactor).sum * (i x / block.length) +
    ((blockPrefix x).map lossFactor).sum
  let divisor := fun x => (block.map divisorFactor).prod ^ (i x / block.length) *
    ((blockPrefix x).map divisorFactor).prod
  let exponent := fun x => (phase x).elim finalDegree degree
  let lane := fun x => g x - loss x
  let pos := fun x => p x / divisor x
  let raw := fun x => build (exponent x) (lane x) (pos x)
    ((phase x).map shrink)
  have hExp : Realizes r exponent := realizes_phase block degree finalDegree ht hi
  have hLane : Realizes r lane := hg.minused (realizes_prefixLoss block lossFactor hBlock hi)
  have hPos : Figure r pos := hp.quotients (figure_prefixDivisor block divisorFactor hBlock hi)
  have hLanes := (num 2).repeated hLane
  have hSlots := (num 2).repeated hExp
  let code := fun ph : A => if shrink ph then 1 else 2
  have hCode : Figure r (fun x => (phase x).elim 0 code) := figure_phase block code 0 ht hi
  have hShr := classified_eq hCode (num 1)
  have hRef := classified_eq hCode (num 2)
  have hValid : Classified r (fun x => i x ≤ block.length * t x) :=
    classified_congr (hi.below (((fix block.length).times ht).plus (fix 1))) (fun _ => Nat.lt_succ_iff)
  have project (f : LevelDims → ℕ) (hf : Figure r (fun x => f (raw x))) :
      Figure r (fun x => f (indexedBlockRow block
        (fun p g phase => build (phase.elim finalDegree degree) g p (phase.map shrink))
        divisorFactor lossFactor (build 0 0 0 none) (p x) (g x) (t x) (i x))) := by
    convert hf.variant (num (f (build 0 0 0 none))) hValid using 1
    funext x
    unfold indexedBlockRow
    by_cases h : i x ≤ block.length * t x
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  refine ⟨project LevelDims.bases ?_, project LevelDims.slots ?_, project LevelDims.slotW ?_,
    project LevelDims.lanes ?_, project LevelDims.laneW ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [raw, hBuild] using hPos.quotients hLanes
  · simpa only [raw, hBuild] using hSlots
  · simpa only [raw, hBuild] using Carry.Figure.of_spoken hExp
  · simpa only [raw, hBuild] using hLanes
  · simpa only [raw, hBuild] using Carry.Figure.of_spoken hLane
  · apply project (fun l => l.shrink.toNat)
    convert (num 1).variant (num 0) hShr using 1
    funext x
    cases hx : phase x with
    | none =>
      simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_none, Option.none_beq_some,
        reduceCtorEq, false_and, exists_false, ↓reduceIte, Bool.toNat_false, Option.elim_none, zero_ne_one, raw]
    | some ph =>
      cases hs : shrink ph
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_some, hs, Option.some_beq_some, beq_true,
          Option.some.injEq, exists_eq_left', Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Option.elim_some,
          OfNat.ofNat_ne_one, raw, code]
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_some, hs, BEq.rfl, Option.some.injEq,
          exists_eq_left', ↓reduceIte, Bool.toNat_true, Option.elim_some, raw, code]
  · apply project LevelDims.colW
    let col := fun ph : A => if shrink ph then Nat.clog 2 (2 * 2 ^ (degree ph) + 1) else 0
    have hc : Figure r (fun x => (phase x).elim 0 col) := figure_phase block col 0 ht hi
    convert hc using 1
    funext x
    cases hx : phase x with
    | none =>
      simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_none, Option.none_beq_some,
        reduceCtorEq, false_and, exists_false, ↓reduceIte, Option.elim_none, raw]
    | some ph =>
      cases hs : shrink ph
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.elim_some, Option.map_some, hs,
          Option.some_beq_some, beq_true, Option.some.injEq, exists_eq_left', Bool.false_eq_true,
          ↓reduceIte, raw, exponent, col]
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.elim_some, Option.map_some, hs, BEq.rfl,
          Option.some.injEq, exists_eq_left', ↓reduceIte, raw, exponent, col]
  · apply project LevelDims.tagW
    let tag := fun ph : A => if shrink ph then tagBits (2 ^ (degree ph)) else 0
    have htag : Figure r (fun x => (phase x).elim 0 tag) := figure_phase block tag 0 ht hi
    convert htag using 1
    funext x
    cases hx : phase x with
    | none =>
      simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_none, Option.none_beq_some,
        reduceCtorEq, false_and, exists_false, ↓reduceIte, Option.elim_none, raw]
    | some ph =>
      cases hs : shrink ph
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.elim_some, Option.map_some, hs,
          Option.some_beq_some, beq_true, Option.some.injEq, exists_eq_left', Bool.false_eq_true,
          ↓reduceIte, raw, exponent, tag]
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.elim_some, Option.map_some, hs, BEq.rfl,
          Option.some.injEq, exists_eq_left', ↓reduceIte, raw, exponent, tag]
  · apply project LevelDims.termKeys
    have hRefresh := ((num 2).repeated (hLane.minused hExp)).variant (num 0) hRef
    convert (hLanes.multiplied hSlots).variant hRefresh hShr using 1
    funext x
    cases hx : phase x with
    | none =>
      simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_none, Option.none_beq_some,
        reduceCtorEq, false_and, exists_false, ↓reduceIte, Option.elim_none, zero_ne_one, OfNat.zero_ne_ofNat, raw]
    | some ph =>
      cases hs : shrink ph
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_some, hs, Option.some_beq_some, beq_true,
          Option.some.injEq, exists_eq_left', Bool.false_eq_true, ↓reduceIte, Option.elim_some,
          OfNat.ofNat_ne_one, raw, exponent, code]
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_some, hs, BEq.rfl, Option.some.injEq,
          exists_eq_left', ↓reduceIte, Option.elim_some, raw, exponent, code]
  · apply project LevelDims.termArity
    let arity := fun ph : A => if shrink ph then 8 else 2 ^ (degree ph) * 2 ^ expand
    have ha : Figure r (fun x => (phase x).elim 0 arity) := figure_phase block arity 0 ht hi
    convert ha using 1
    funext x
    cases hx : phase x with
    | none =>
      simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_none, Option.none_beq_some,
        reduceCtorEq, false_and, exists_false, ↓reduceIte, Option.elim_none, raw]
    | some ph =>
      cases hs : shrink ph
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.map_some, hs, Option.some_beq_some, beq_true,
          Option.some.injEq, exists_eq_left', Bool.false_eq_true, ↓reduceIte, Option.elim_some,
          raw, exponent, arity]
      · simp only [hBuild, Option.map_eq_some_iff, hx, Option.elim_some, Option.map_some, hs, BEq.rfl,
          Option.some.injEq, exists_eq_left', ↓reduceIte, raw, exponent, arity]

end P1SolFmt.SolGeometry
