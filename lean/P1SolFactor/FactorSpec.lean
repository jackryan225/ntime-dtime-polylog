import P1SolFactor.Specification

namespace P1SolFactor

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel P1Net
open scoped Classical

noncomputable section

abbrev RouteSettings :=
  ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m

/-- Evaluator letter for a bit in a packed query or a routing header. -/
def inputBit {R : Type} (b : Bool) : P1P5.EvalSym R :=
  .inr (if b then P1P5.Tok.one else P1P5.Tok.endPtr)

private def routeHeader {R : Type} (bset : RouteSettings) {m : ℕ} [NeZero m]
    (π : Equiv.Perm (Routing.Addr m)) (column : ℕ) (address : Routing.Addr m) : List (P1P5.EvalSym R) :=
  let s := bset m π
  let incoming := if column = 0 then false else s (column - 1) (Routing.rep m (column - 1) address)
  let outgoing := if column + 1 = 2 * m then 0 else if s column (Routing.rep m column address) then 2 else 1
  P1P5.encPtr 5 ++ [inputBit incoming] ++ P1P5.encPtr outgoing

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  {R : Type} [CommRing R]

/-- The site header has a caller-supplied scalar. Routing headers contain the two bits of `bset`. -/
def factorRegsWith (bset : RouteSettings) (u : (rnState V B I σ ha).network.Site) (c : R) :
    Reg (P1P5.EvalSym R) :=
  let r := Function.update (factor0Regs V B L I σ ha R u) 3 [.inl c]
  if u.1.2 then r else
    match u.1.1.2 with
    | .rt k j π => Function.update r 2 (routeHeader bset (accAddr I σ u.1.1.1 k) j.val (addrOf π u.2))
    | .st j π => Function.update r 2 (routeHeader bset (stAddr h) j.val (addrOf π u.2))
    | _ => r

/-- One site of the P5 state, with the supplied scalar multiplying every entry of that site. -/
def factorStateWith (bset : RouteSettings) (u : (rnState V B I σ ha).network.Site) (c : R) :
    List (P1P5.EvalSym R) :=
  P1P5.encState (P1P5.stateOfO (siteKeys (rnState V B I σ ha) u)
    (fun v z => c * (if rnSiteOK V B L I σ ha bset v z then 1 else 0)))

end RoutedSite

/-- Proposed part (c) contract for one key, following owner board message 1978. -/
def factor0_entry_with_scalar_spec (V : FiniteMultiTapeMachine) (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (R : Type) [CommRing R] [Fintype R] : Prop :=
  ∃ (Prg : Prog (P1P5.EvalSym R)) (C : ℕ),
    ∀ {g h : ℕ} (B : ℕ) [NeZero B] (L : GuessLayout V g) (I : ℕ) [NeZero I]
      (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (bset : RouteSettings) (u : (rnState V B I σ ha).network.Site)
      (c : R) (z : (rnState V B I σ ha).network.Half u),
      let X := rnState V B I σ ha
      let regs := Function.update (factorRegsWith V B L I σ ha bset u c) 4 ((packHalf X u z).map inputBit)
      ∃ (n : ℕ) (r : Reg (P1P5.EvalSym R)), Prog.Run [] Prg regs n r ∧
        (r 0).head? = some (.inl (c * (if rnSiteOK V B L I σ ha bset u z then 1 else 0))) ∧
        n ≤ C * (halfWidthSum X u + 1) ^ C

/-- Proposed part (c) contract for the explicit evaluator state of one site. -/
def factor0_table_with_scalar_spec (V : FiniteMultiTapeMachine) (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (R : Type) [CommRing R] [Fintype R] : Prop :=
  ∃ (Prg : Prog (P1P5.EvalSym R)) (C : ℕ),
    ∀ {g h : ℕ} (B : ℕ) [NeZero B] (L : GuessLayout V g) (I : ℕ) [NeZero I]
      (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (bset : RouteSettings) (u : (rnState V B I σ ha).network.Site) (c : R),
      let W := halfWidthSum (rnState V B I σ ha) u
      ∃ (n : ℕ) (r : Reg (P1P5.EvalSym R)),
        Prog.Run [] Prg (factorRegsWith V B L I σ ha bset u c) n r ∧
        r 0 = factorStateWith V B L I σ ha bset u c ∧
        n ≤ C * 2 ^ W * (W + 1) ^ C

end

end P1SolFactor
