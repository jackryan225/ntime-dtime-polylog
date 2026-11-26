import P1ProgDir.Readbacks
import P1ProgDir.Signed

namespace P1ProgDir.SolC3Step

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolReadbacks P1ProgDir.SolSigned

/-- Local check over a directory scan row. The link owner was already checked
to be a valid index when its code was nonzero. -/
def rowOK (null side nearer here owns : Bool) : Bool :=
  if null then !(side && owns)
  else (!here || (side && owns)) && !(side && nearer && owns)

theorem rowOK_null (side nearer here owns : Bool) :
    rowOK true side nearer here owns = true ↔ (side = true → owns = false) := by
  cases side <;> cases nearer <;> cases here <;> cases owns <;> decide

theorem rowOK_some (side nearer here owns : Bool) :
    rowOK false side nearer here owns = true ↔
      (here = true → side = true ∧ owns = true) ∧
        (side = true → nearer = true → owns = false) := by
  cases side <;> cases nearer <;> cases here <;> cases owns <;> decide

theorem linkValid_iff_rowOK {I : ℕ} (owns : Fin I → Bool) (i : Fin I) (nx : Bool)
    (link : Option (Fin I)) :
    linkValid (fun j => owns j = true) i nx link ↔
      ∀ j : Fin I,
        rowOK link.isNone
          (decide (if nx then i < j else j < i))
          (decide (if nx then j < link.getD i else link.getD i < j))
          (decide (some j = link)) (owns j) = true := by
  cases link with
  | none =>
    simp only [Option.isNone_none, rowOK_null, decide_eq_true_eq, linkValid]
    exact forall_congr' fun j => imp_congr_right fun _ => by cases owns j <;> decide
  | some v =>
    simp only [Option.isNone_some, Option.getD_some, Option.some.injEq,
      rowOK_some, decide_eq_true_eq, linkValid]
    constructor
    · rintro ⟨hside, hv, hall⟩ j
      refine ⟨fun hj => hj ▸ ⟨hside, hv⟩, fun hs hn => ?_⟩
      have h := hall j hs hn
      cases hj : owns j
      · rfl
      · exact (h hj).elim
    · intro hall
      have hsel := (hall v).1 rfl
      refine ⟨hsel.1, hsel.2, fun j hs hn => ?_⟩
      rw [(hall j).2 hs hn]
      decide

/-- One row uses signed interval membership and comparisons on binary indices. -/
def entryStep (p : Bool × Bool × Word × Word × Word × Word × Word × Word) : Bool :=
  let nx := p.1
  let null := p.2.1
  let i := p.2.2.1
  let link := p.2.2.2.1
  let j := p.2.2.2.2.1
  let lo := p.2.2.2.2.2.1
  let hi := p.2.2.2.2.2.2.1
  let b := p.2.2.2.2.2.2.2
  let side := bif nx then more (j, i) else more (i, j)
  let nearer := bif nx then more (link, j) else more (j, link)
  let here := !(more (link, j)) && !(more (j, link))
  let owns := !(ltSigned (b, lo)) && !(ltSigned (hi, b))
  rowOK null side nearer here owns

theorem easy_entryStep : Easy entryStep := by
  let P := Bool × Bool × Word × Word × Word × Word × Word × Word
  have hnx : Easy (fun p : P => p.1) := Easy.fst
  have hnull : Easy (fun p : P => p.2.1) := Easy.snd.compose Easy.fst
  have hi : Easy (fun p : P => p.2.2.1) := Easy.snd.compose (Easy.snd.compose Easy.fst)
  have hlink : Easy (fun p : P => p.2.2.2.1) := Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
  have hj : Easy (fun p : P => p.2.2.2.2.1) :=
    Easy.snd.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst)))
  have hlo : Easy (fun p : P => p.2.2.2.2.2.1) :=
    Easy.snd.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))))
  have hhi : Easy (fun p : P => p.2.2.2.2.2.2.1) :=
    Easy.snd.compose (Easy.snd.compose (Easy.snd.compose
      (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst)))))
  have hb : Easy (fun p : P => p.2.2.2.2.2.2.2) :=
    Easy.snd.compose (Easy.snd.compose (Easy.snd.compose
      (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd)))))
  have hchoose {f g : P → Bool} (hf : Easy f) (hg : Easy g) :
      Easy (fun p => bif p.1 then g p else f p) :=
    (hnx.pair Easy.identity).compose (Easy.ifst hf hg)
  have hnotAnd {f g : P → Bool} (hf : Easy f) (hg : Easy g) :
      Easy (fun p => !(f p) && !(g p)) :=
    (hf.pair hg).compose (Easy.finite (fun p : Bool × Bool => !p.1 && !p.2))
  have hside := hchoose (easy_more (hi.pair hj)) (easy_more (hj.pair hi))
  have hbefore := hchoose (easy_more (hj.pair hlink)) (easy_more (hlink.pair hj))
  have heq := hnotAnd (easy_more (hlink.pair hj)) (easy_more (hj.pair hlink))
  have hown := hnotAnd ((hb.pair hlo).compose easy_ltSigned) ((hhi.pair hb).compose easy_ltSigned)
  exact (hnull.pair (hside.pair (hbefore.pair (heq.pair hown)))).compose
    (Easy.finite (fun x : Bool × Bool × Bool × Bool × Bool => rowOK x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))

theorem entryStep_eq (nx null : Bool) (i link j lo hi b : Word) :
    entryStep (nx, null, i, link, j, lo, hi, b) =
      rowOK null
        (decide (if nx then value i < value j else value j < value i))
        (decide (if nx then value j < value link else value link < value j))
        (decide (value j = value link))
        (decide (signedValue lo ≤ signedValue b ∧ signedValue b ≤ signedValue hi)) := by
  have hn (x y : Word) : more (x, y) = decide (value y < value x) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, more_lt]
  have hf (v : Bool) : (!v) = true ↔ ¬ v = true := by cases v <;> decide
  have he : (!more (link, j) && !more (j, link)) = decide (value j = value link) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    simp only [Bool.and_eq_true, hf, more_lt]
    omega
  have ho : (!ltSigned (b, lo) && !ltSigned (hi, b)) =
      decide (signedValue lo ≤ signedValue b ∧ signedValue b ≤ signedValue hi) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    simp only [Bool.and_eq_true, hf, ltSigned_eq, not_lt]
  change rowOK null (bif nx then more (j, i) else more (i, j))
    (bif nx then more (link, j) else more (j, link)) _ _ = _
  rw [he, ho]
  cases nx <;> simp only [Bool.cond_false, Bool.cond_true, Bool.false_eq_true, ↓reduceIte, hn]

end P1ProgDir.SolC3Step
