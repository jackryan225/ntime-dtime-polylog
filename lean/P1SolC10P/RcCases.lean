import P1C10.Prog
import P1ChkFinal.C10RcPoly

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1C10 P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

namespace P1SolC10P.SolC10prog

private theorem poly_lt {X : Type} [Codec X] {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := by
  have h : Poly (fun x => (binary (f x), binary (g x))) := hf.pair hg
  simpa only [Carry.lt_r, value_binary] using h.compose Carry.ltPoly

private theorem poly_eq {X : Type} [Codec X] {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := by
  have h := ((poly_lt hf hg).pair (poly_lt hg hf)).compose
    (Easy.finite (fun b : Bool × Bool => !(b.1 || b.2))).poly
  convert h using 1
  funext x
  by_cases hfg : f x = g x
  · simp only [hfg, lt_self_iff_false, decide_false, Bool.or_false, Bool.not_false, decide_true]
  · rcases lt_or_gt_of_ne hfg with hl | hl
    · simp only [hl, decide_true, Bool.true_or, Bool.not_true, hfg, decide_false]
    · simp only [hl, decide_true, Bool.or_true, Bool.not_true, hfg, decide_false]

private theorem poly_matchKey (key : ℕ × ℕ) :
    Poly (fun q : (ℕ × ℕ) × ShrinkIn => key == q.1) := by
  have ha : Poly (fun q : (ℕ × ℕ) × ShrinkIn => q.1.1) :=
    Easy.fst.poly.fstCompose
  have hb : Poly (fun q : (ℕ × ℕ) × ShrinkIn => q.1.2) :=
    Easy.fst.poly.sndCompose
  have h := ((poly_eq (poly_const key.1) ha).pair (poly_eq (poly_const key.2) hb)).compose
    (Easy.finite (fun b : Bool × Bool => b.1 && b.2)).poly
  exact h

end P1SolC10P.SolC10prog

theorem P1SolC10P.rcCasesPoly : P1C10.RcCasesTarget := by
  intro L
  induction L with
  | nil =>
    intro _
    exact poly_const (none : Option PanelCode)
  | cons e L ih =>
    intro hL
    have hHead := hL e (List.mem_cons_self ..)
    have hTail := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha))
    have h := Code.Poly.choose (P1SolC10P.SolC10prog.poly_matchKey e.1)
      (Easy.snd.poly.compose hHead) hTail
    convert h using 1
    funext q
    simp only [rcCases, List.find?_cons]
    cases hq : e.1 == q.1 <;> rfl

#print axioms P1SolC10P.rcCasesPoly
