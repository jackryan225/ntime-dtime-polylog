import P1Int.D5AsmDefs
import P1Int.FormAg
import P1ChkFinal.C7RFam
import P1ChkFinal.Wired
import P1ChkGreedy.LocalC6
import P1SolGreedy.GreedyFamilies
import P1C10.Code
import P1C10.Fix

/-!
# P1Int.DispCk: the deciders of the 16 families (lane P1-lean-disp, item p11_dispatch)

`dispCk c x u i`: the Bool decider of family `c`, exactly the family Props of integ's `DispIn` (FinalInputs.lean):
0 C1F, 1 C2F, 2 C3F (fixed dims, tape `fixedTapeOrder`), 3 C4w (`c4dims`, numbering `Fintype.equivFin`), 4 C5fam,
5 C6fam, 6 C7all (D15), 7 C8fam, 8 C9fam (`gdims`, `genuineAg`, `Bt.shrink`, `Bt.refresh`), 9 C10w (`fx10 Bt`, `gdims`),
10 C11w, 11 C12w, 12 C13linkw (the cone term `Wof`, a parameter here), 13 C13endsw, 14 C14F; 15 (and beyond): `true`.
`dispCk_iff`: the 15 decider equivalences of `DispIn`, for every input.
-/

namespace P1Int

namespace P11

namespace Disp

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
  (a b d bigBias termBias : ℕ)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
  (Wof : List Bool → List Bool → ℕ → F)

open Classical in
/-- **The deciders of the 16 families** (`Wof` = the cone's term for family 12). -/
def dispCk (c : ℕ) : List Bool → List Bool → ℕ → Bool :=
  match c with
  | 0 => fun x u i => decide (P1ChkDir.C1F (fixedDims Bt V a b x d bigBias termBias)
      (fixedTapeOrder Bt V a b x d bigBias termBias) u i)
  | 1 => fun x u i => decide (P1ChkDir.C2F (fixedDims Bt V a b x d bigBias termBias)
      (fixedTapeOrder Bt V a b x d bigBias termBias) u i)
  | 2 => fun x u i => decide (P1ChkDir.C3F (fixedDims Bt V a b x d bigBias termBias)
      (fixedTapeOrder Bt V a b x d bigBias termBias) u i)
  | 3 => fun x u i => decide (P1ChkDir.C4w (four_le_baseDegree S)
      (fun kk => ((Fintype.equivFin (toOAI V).K kk : Fin _) : ℕ)) (c4dims Bt V a b d bigBias termBias) x u i)
  | 4 => fun x u i => decide (P1ChkGreedy.C5fam (gdims Bt V a b d bigBias termBias) x u i)
  | 5 => fun x u i => decide (P1ChkGreedy.C6fam (gdims Bt V a b d bigBias termBias)
      (genuineAg (gdims Bt V a b d bigBias termBias)) x u i)
  | 6 => fun x u i => decide (P1ChkFinal.C7R.C7all S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink (gdims Bt V a b d bigBias termBias)
      (genuineAg (gdims Bt V a b d bigBias termBias)) x u i)
  | 7 => fun x u i => decide (P1SolGreedy.C8fam Bt.shrink (gdims Bt V a b d bigBias termBias)
      (genuineAg (gdims Bt V a b d bigBias termBias)) x u i)
  | 8 => fun x u i => decide (P1ChkGreedy.C9fam (gdims Bt V a b d bigBias termBias) x u i)
  | 9 => fun x u i => decide (P1C10.C10w (P1C10.fx10 Bt) (gdims Bt V a b d bigBias termBias) x u i)
  | 10 => fun x u i => decide (P1ChkFinal.C11w (gdims Bt V a b d bigBias termBias) x u i)
  | 11 => fun x u i => decide (P1ChkFinal.C12w (gdims Bt V a b d bigBias termBias) x u i)
  | 12 => fun x u i => decide (P1ChkFinal.C13linkw bs (gdims Bt V a b d bigBias termBias) Wof x u i)
  | 13 => fun x u i => decide (P1ChkFinal.C13endsw bs l (gdims Bt V a b d bigBias termBias) x u i)
  | 14 => fun x u i => decide (P1ChkDir.C14F (fixedDims Bt V a b x d bigBias termBias)
      (fixedTapeOrder Bt V a b x d bigBias termBias) (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) u i)
  | _ => fun _ _ _ => true

open Classical in
/-- **The 15 decider equivalences of `DispIn`**, for every input `x`. -/
theorem dispCk_iff (x : List Bool) :
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 0 x u i = true ↔
      P1ChkDir.C1F (fixedDims Bt V a b x d bigBias termBias) (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 1 x u i = true ↔
      P1ChkDir.C2F (fixedDims Bt V a b x d bigBias termBias) (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 2 x u i = true ↔
      P1ChkDir.C3F (fixedDims Bt V a b x d bigBias termBias) (fixedTapeOrder Bt V a b x d bigBias termBias) u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 3 x u i = true ↔ P1ChkDir.C4w (four_le_baseDegree S)
      (fun kk => ((Fintype.equivFin (toOAI V).K kk : Fin _) : ℕ)) (c4dims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 4 x u i = true ↔
      P1ChkGreedy.C5fam (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 5 x u i = true ↔
      P1ChkGreedy.C6fam (gdims Bt V a b d bigBias termBias) (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 6 x u i = true ↔
      P1ChkFinal.C7R.C7all S.graph (Nat.two_pow_pos S.expanderExponent)
        (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink (gdims Bt V a b d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 7 x u i = true ↔
      P1SolGreedy.C8fam Bt.shrink (gdims Bt V a b d bigBias termBias)
        (genuineAg (gdims Bt V a b d bigBias termBias)) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 8 x u i = true ↔
      P1ChkGreedy.C9fam (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 9 x u i = true ↔
      P1C10.C10w (P1C10.fx10 Bt) (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 10 x u i = true ↔
      P1ChkFinal.C11w (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 11 x u i = true ↔
      P1ChkFinal.C12w (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 12 x u i = true ↔
      P1ChkFinal.C13linkw bs (gdims Bt V a b d bigBias termBias) Wof x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 13 x u i = true ↔
      P1ChkFinal.C13endsw bs l (gdims Bt V a b d bigBias termBias) x u i) ∧
    (∀ u i, dispCk Bt V a b d bigBias termBias bs l Wof 14 x u i = true ↔
      P1ChkDir.C14F (fixedDims Bt V a b x d bigBias termBias) (fixedTapeOrder Bt V a b x d bigBias termBias)
        (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) u i) :=
  ⟨fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff,
   fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff,
   fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff,
   fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff,
   fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff, fun _ _ => decide_eq_true_iff⟩

/-- Family 15 accepts everything. -/
theorem dispCk_15 (x u : List Bool) (i : ℕ) : dispCk Bt V a b d bigBias termBias bs l Wof 15 x u i = true := rfl

end

end Disp

end P11

end P1Int

#print axioms P1Int.P11.Disp.dispCk_iff
