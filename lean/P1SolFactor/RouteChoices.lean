import P1SolFactor.FactorSpec

namespace P1SolFactor

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open scoped Classical

noncomputable section

/-- Select the cross incoming arc precisely when the preceding switch crosses. -/
def routeInChoice {m : ℕ} [NeZero m] (s : Routing.Settings m) (column : ℕ)
    (address : Routing.Addr m) : Bool :=
  if column = 0 then false else s (column - 1) (Routing.rep m (column - 1) address)

/-- At the last column there is one output arc. Otherwise the switch selects one of two arcs. -/
def routeOutChoice {m : ℕ} [NeZero m] (s : Routing.Settings m) (column : ℕ)
    (address : Routing.Addr m) : Option Bool :=
  if column + 1 = 2 * m then none else some (s column (Routing.rep m column address))

/-- Local routing test using exactly the two choices recorded by the input header. -/
def chosenRouteOK {W : ℕ} (crossIn : Bool) (crossOut : Option Bool)
    (in2 in3 out0 out1 : Fin W → Bool) : Prop :=
  let item := if crossIn then in3 else in2
  match crossOut with
  | none => out0 = item
  | some false => out0 = item ∧ out1 = fun _ => false
  | some true => out1 = item ∧ out0 = fun _ => false

theorem routeOK_iff_chosen {m W : ℕ} [NeZero m] (s : Routing.Settings m) (column : ℕ)
    (address : Routing.Addr m) (in2 in3 out0 out1 : Fin W → Bool) :
    routeOK s column address in2 in3 out0 out1 ↔
      chosenRouteOK (routeInChoice s column address) (routeOutChoice s column address) in2 in3 out0 out1 := by
  have hitem : (if column = 0 then in2 else if s (column - 1) (Routing.rep m (column - 1) address)
      then in3 else in2) = (if routeInChoice s column address then in3 else in2) := by
    by_cases hi : column = 0 <;> simp [routeInChoice, hi]
  simp only [routeOK, chosenRouteOK, routeOutChoice, hitem]
  by_cases ho : column + 1 = 2 * m
  · simp [ho]
  · cases s column (Routing.rep m column address) <;> simp [ho]

def routeOutCode (crossOut : Option Bool) : ℕ :=
  crossOut.elim 0 fun b => if b then 2 else 1

/-- The header stores the incoming choice as a bit token, and the outgoing choice as 0, 1 or 2. -/
def encodeRouteChoices {R : Type} (crossIn : Bool) (crossOut : Option Bool) : List (P1P5.EvalSym R) :=
  P1P5.encPtr 5 ++ (inputBit crossIn :: P1P5.encPtr (routeOutCode crossOut))

private theorem encodeRouteChoices_header {R : Type} (column m : ℕ) (crossIn crossOut : Bool) :
    (P1P5.encPtr 5 ++ [.inr (if crossIn then P1P5.Tok.one else P1P5.Tok.endPtr)] ++
      P1P5.encPtr (if column + 1 = 2 * m then 0 else if crossOut then 2 else 1) : List (P1P5.EvalSym R)) =
      encodeRouteChoices crossIn (if column + 1 = 2 * m then none else some crossOut) := by
  by_cases ho : column + 1 = 2 * m <;> simp [encodeRouteChoices, inputBit, routeOutCode, ho]

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  {R : Type} [CommRing R] (bset : RouteSettings)

theorem factorRegsWith_rt_header (ι : Fin I) (k : V.K) (column : Fin (2 * (h + 3)))
    (π : BitWord 3) (lane : BitWord h) (c : R) :
    factorRegsWith V B L I σ ha bset (((ι, .rt k column π), false), lane) c 2 =
      encodeRouteChoices (routeInChoice (bset (3 + h) (accAddr I σ ι k)) column (addrOf π lane))
        (routeOutChoice (bset (3 + h) (accAddr I σ ι k)) column (addrOf π lane)) := by
  simp only [factorRegsWith, Bool.false_eq_true, ite_false, Function.update_self]
  exact encodeRouteChoices_header column.val (3 + h) _ _

theorem factorRegsWith_st_header (ι : Fin I) (column : Fin (2 * (h + 1)))
    (π : BitWord 1) (lane : BitWord h) (c : R) :
    factorRegsWith V B L I σ ha bset (((ι, .st column π), false), lane) c 2 =
      encodeRouteChoices (routeInChoice (bset (1 + h) (stAddr h)) column (addrOf π lane))
        (routeOutChoice (bset (1 + h) (stAddr h)) column (addrOf π lane)) := by
  simp only [factorRegsWith, Bool.false_eq_true, ite_false, Function.update_self]
  exact encodeRouteChoices_header column.val (1 + h) _ _

end RoutedSite

end

end P1SolFactor
