import P1ProgDir.C4ProgPublicPlan
import P1ProgDir.C4ProgWiredTask
import P1ProgDir.C4ProgD8

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ChkDir P1Net P1Wit NatCode P1Int

variable {K : Type} [Fintype K] [DecidableEq K] {a : ℕ}

theorem poly_prepare_of_fmt (τ : K → ℕ) (dims : ℕ → C4Dims) (hf : FmtHyp4 dims) :
    Poly ((wiredFormat τ dims).prepare a) := by
  have hfmt : Poly (fun q : C4Query => publicData (dims (value q.1))) :=
    Easy.fst.poly.compose (publicData_of_fmt dims hf)
  have hq : Poly (fun q : C4Query => (publicData (dims (value q.1)), value q.2.1, value q.2.2)) :=
    hfmt.pair ((Easy.snd.poly.compose Easy.fst.poly).compose poly_value
      |>.pair ((Easy.snd.poly.compose Easy.snd.poly).compose poly_value))
  have hc := hq.compose (poly_numericPrepare τ a (Fintype.card K) (Fintype.card (Ext K)))
  convert hc using 1
  funext q
  exact (numericPrepare_eq τ (dims (value q.1)) a (value q.2.1) (value q.2.2)).symm

private theorem size_tally_le (t : Tally) : t.length ≤ size t := by
  rw [size_tally]
  omega

private theorem le_sum_of_mem (x : ℕ) (xs : List ℕ) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hy
    · exact Nat.le_add_right _ _
    · exact (ih hy).trans (Nat.le_add_left _ _)

private theorem fmtWidth (P : C4Dims) (s : ℕ) (hs : s < 13) :
    P.D.width s ≤ 2 + (fmtSmall P).sum := by
  have hw5 : P.D.width 5 = 1 := by
    have ht : 5 < 5 + 12 * (P.D.top + 1) := by omega
    simp only [Dims.width, Dims.kind, ht, ↓reduceIte, Dims.levWidth]
    rfl
  have hw0 : P.D.width 0 = 2 := rfl
  have hw4 : P.D.width 4 = P.D.width 1 := rfl
  suffices h : P.D.width s ≤ 2 ∨ P.D.width s ∈ fmtSmall P by
    rcases h with h | h
    · exact h.trans (Nat.le_add_right _ _)
    · exact (le_sum_of_mem _ _ h).trans (Nat.le_add_left _ _)
  interval_cases s <;>
    simp [fmtSmall, secStart, secPrev, secNext, secLev, Mem.toNat, hw0, hw4, hw5]

private theorem fmtSmall_total (P : C4Dims) :
    (publicData P).2.flatten.length = (fmtSmall P).sum := by
  change ((fmtSmall P).map tally).flatten.length = (fmtSmall P).sum
  generalize fmtSmall P = widths
  induction widths with
  | nil => rfl
  | cons w ws ih => simp [ih, tally_length]

theorem widths_of_fmt (τ : K → ℕ) (dims : ℕ → C4Dims) (hf : FmtHyp4 dims) :
    Dom size (fun q : C4Query => allFieldWidths ((wiredFormat τ dims).prepare a q)) := by
  have hfmt : Poly (fun q : C4Query => publicData (dims (value q.1))) :=
    Easy.fst.poly.compose (publicData_of_fmt dims hf)
  have ht : Poly (fun q : C4Query => (publicData (dims (value q.1))).2.flatten) :=
    hfmt.compose (Easy.snd.poly.compose Easy.flatten.poly)
  have hL : Poly (fun q : C4Query => small (publicData (dims (value q.1))) 0) :=
    hfmt.compose (poly_small 0)
  apply C4Format.widths_dom (W := fun n => 2 + (fmtSmall (dims n)).sum)
  · exact fun n s hs => fmtWidth (dims n) s hs
  · apply (Dom.const _ 2).add (ht.length.mono ?_)
    intro q
    rw [← fmtSmall_total]
    apply size_tally_le
  · apply hL.length.mono
    intro q
    change 2 ^ (dims (value q.1)).h ≤ size (small (publicData (dims (value q.1))) 0)
    exact (tally_length _).symm.le.trans (size_tally_le _)

theorem progC4 (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (hf : FmtHyp4 dims) :
    ProgC4 ha τ dims :=
  progC4_of_publicPlan ha τ dims (poly_prepare_of_fmt τ dims hf) (widths_of_fmt τ dims hf)

open scoped Classical in
theorem progC4_D8 (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (hf : FmtHyp4 dims)
    (s : ℝ) (hs : s ≤ 1) (aClock bClock : ℕ) (hb : 1 ≤ bClock) :
    ∃ (Rc : Prog Ltr) (c : ℕ), ∀ x : List Bool, 16 ≤ x.length →
      ∃ bnd : ℕ, 1 ≤ bnd ∧ 4 * 4 + bnd ≤ lpCost2 c s aClock bClock x.length ∧
        ∀ (u : Fin (lpM2 s aClock bClock x.length) → Bool) (ρ : List Bool),
          ρ.length = lpK2 aClock bClock x.length - 4 →
          ProgAnswers Rc P1Dispatch.answer (inputRegs Ltr.bit x (List.ofFn u) ρ)
            (decide (C4w ha τ dims x (List.ofFn u) (P1Batch.bval ρ))) bnd :=
  progC4F (wiredFormat τ dims) ha (poly_prepare_of_fmt τ dims hf) (widths_of_fmt τ dims hf) s hs aClock bClock hb

end P1ProgDir.SolC4

#print axioms P1ProgDir.SolC4.progC4
#print axioms P1ProgDir.SolC4.progC4_D8
