import P1Net.Factors
import P1Benes.Tab
import P1Benes.NetBridge
import P1P5.EvalOrder
import P1P5.EvalSyms

namespace P1SolFactor

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel P1Net
open scoped BigOperators

noncomputable section

/-! Round-one proposed interfaces. The specifications below are propositions. -/

/-- The input alphabet for permutation tables. A right letter separates rows. -/
abbrev SwitchSym := Bool ⊕ Unit

/-- Each permutation row contains its image in exactly `m` bits, least significant bit first. -/
def encPermRows {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) : List SwitchSym :=
  (List.ofFn fun i => (List.ofFn fun b : Fin m => Sum.inl ((π i).val.testBit b.val)) ++
    [Sum.inr ()]).flatten

/-- First row, low-bit-zero subnetwork, low-bit-one subnetwork, last row, recursively.
The known address width determines all row and subnetwork lengths. -/
def settingsBits : {n : ℕ} → P1Benes.Net.Settings n → List Bool
  | _, .leaf b => [b]
  | _, .node f t g => List.ofFn f ++ settingsBits (t false) ++ settingsBits (t true) ++ List.ofFn g

/-- Output register 0 starts empty. Registers 1 and 2 contain the forward and inverse tables. -/
def switchRegs {m : ℕ} (π : Equiv.Perm (Fin (2 ^ m))) : Reg SwitchSym := fun j =>
  if j = 1 then encPermRows π else if j = 2 then encPermRows π.symm else []

/-- Part (b). Here the address width is `m + 1` and the number of addresses is `2 ^ (m + 1)`. -/
def switch_bits_spec : Prop :=
  ∃ (Prg : Prog SwitchSym) (c : ℕ), ∀ (m : ℕ) (π : Equiv.Perm (Fin (2 ^ (m + 1)))),
    ∃ (n : ℕ) (r : Reg SwitchSym), Prog.Run [] Prg (switchRegs π) n r ∧
      r 0 = (settingsBits (P1Benes.Net.settings m π)).map Sum.inl ∧
      n ≤ c * (m + 1) * (2 ^ (m + 1)) ^ 3

section HalfWords

variable {a h : ℕ} (X : State a h) (u : X.network.Site)

def edgeWidth (e : X.network.Edge) : ℕ := X.width ((e.1.1, e.2), e.1.2)

/-- The width at each numbered slot, with `false` for outgoing and `true` for incoming. -/
def slotWidth (dir : Bool) (j : Fin (2 ^ a)) : ℕ :=
  edgeWidth X (if dir then inEdge X u j else (u, j))

/-- The sum of the actual incoming and outgoing payload widths. -/
def halfWidthSum : ℕ := ∑ dir : Bool, ∑ j, slotWidth X u dir j

private def slotOffset (dir : Bool) (j : Fin (2 ^ a)) : ℕ :=
  (if dir then ∑ i, slotWidth X u false i else 0) +
    ((List.ofFn (slotWidth X u dir)).take j.val).sum

/-- The bit string for an independent half-assignment, outgoing slots followed by incoming slots. -/
def packHalf (z : X.network.Half u) : List Bool :=
  (List.ofFn fun j : Fin (2 ^ a) => List.ofFn (z.1 (u, j) rfl)).flatten ++
  (List.ofFn fun j : Fin (2 ^ a) => List.ofFn (z.2 (inEdge X u j) (inEdge_dst X u j))).flatten

/-- Read each actual arc at the offset of its slot on the relevant side of the site. -/
def unpackHalf (bits : List Bool) : X.network.Half u :=
  (fun e _ j => bits.getD (slotOffset X u false e.2 + j.val) false,
   fun e _ j => bits.getD (slotOffset X u true (X.slots.actualGraph.target e).2 + j.val) false)

/-- Packed words in increasing binary index order.
The level using the resulting table uses these keys in `P1P5.LevelOrd.old`. -/
def siteKeys : List (P1P5.Key X.network) :=
  List.ofFn fun i : Fin (2 ^ halfWidthSum X u) =>
    ⟨u, unpackHalf X u (List.ofFn fun j : Fin (halfWidthSum X u) => i.val.testBit j.val)⟩

end HalfWords

/-- Local data for the factor test. In `pins`, `none` allows either verifier input symbol.
In `route`, the first bit selects the incoming arc and the optional bit selects the outgoing arc.
In `fixed`, the supplied initial state word is extended by zero bits. -/
inductive SiteRule (V : FiniteMultiTapeMachine) where
  | free
  | table (blockSize : ℕ) (last : Bool) (moves : List (Fin 3))
  | path (linked : Bool) (c : Ext V.K)
  | pins (allowed : List (Option V.Γ))
  | copy (outSlot inSlot : Fin 4)
  | route (crossIn : Bool) (crossOut : Option Bool)
  | fixed (word : List Bool)

def routeRule {V : FiniteMultiTapeMachine} {m : ℕ} [NeZero m]
    (π : Equiv.Perm (Routing.Addr m)) (c : ℕ) (p : Routing.Addr m) : SiteRule V :=
  let s := P1Benes.NetBridge.bset m π
  .route (if c = 0 then false else s (c - 1) (Routing.rep m (c - 1) p))
    (if c + 1 = 2 * m then none else some (s c (Routing.rep m c p)))

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)

private theorem intervalIndex_lt {J l : ℕ} (ι : Fin J) (lane : BitWord l) :
    ι.val * 2 ^ l + (laneEquiv l lane).val < J * 2 ^ l := by
  calc
    _ < ι.val * 2 ^ l + 2 ^ l := Nat.add_lt_add_left (laneEquiv l lane).isLt _
    _ = (ι.val + 1) * 2 ^ l := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ J * 2 ^ l := Nat.mul_le_mul_right _ ι.isLt

/-- Local data derived from the public skeleton, owner links, initial pins and switch tables.
Extraction of these data precedes the local table-writing program. -/
def siteRule (u : (rnState V B I σ ha).network.Site) : SiteRule V := by
  classical
  let ι := u.1.1.1
  let lane := laneEquiv h u.2
  let i : Fin (I * 2 ^ h) := ⟨ι.val * 2 ^ h + lane.val, intervalIndex_lt ι u.2⟩
  let linked := decide (netMate I σ (u.1.1, 1) ≠ none)
  exact if u.1.2 then .free else
    match u.1.1.2 with
    | .tabC => .table B (decide (i.val + 1 = I * 2 ^ h))
        ((List.ofFn fun j => σ i ((kIdx V.K).symm j)))
    | .tabP c => .path linked c
    | .portIn k δ => if linked then .copy 0 1 else
        let Z := portBlock I σ ι k δ lane
        .pins (List.ofFn fun o : Fin B =>
          let cell := Z * (B : ℤ) + (o : ℤ)
          if (L.guessAt k cell).isSome then none else some (L.base k cell))
    | .portOut _ _ | .eOut => if linked then .copy 1 0 else .free
    | .rt k c π => routeRule (accAddr I σ ι k) c.val (addrOf π u.2)
    | .st c π => routeRule (stAddr h) c.val (addrOf π u.2)
    | .eIn => if ι.val = 0 then
        .fixed (if lane.val = 0 then List.ofFn (encS V B V.initialState (fun _ => finOfInt B 0)) else [])
      else .copy 0 1

variable {R : Type}

private def encNat (q : ℕ) : List (P1P5.EvalSym R) := P1P5.encPtr q

private def encBit (b : Bool) : P1P5.EvalSym R :=
  .inr (if b then P1P5.Tok.one else P1P5.Tok.endPtr)

/-- The level-0 rule header, in the evaluator alphabet. -/
def encRule : SiteRule V → List (P1P5.EvalSym R)
  | .free => encNat 0
  | .table B last moves => encNat 1 ++ encNat B ++ [encBit last] ++ moves.flatMap (fun m => encNat m.val)
  | .path b c => encNat 2 ++ [encBit b, encBit (Ext.isIn V c)] ++ encNat (extIdx V.K c).val
  | .pins p => encNat 3 ++ p.flatMap (fun s => encNat (s.elim 0 fun t => (Fintype.equivFin V.Γ t).val + 1))
  | .copy o i => encNat 4 ++ encNat o.val ++ encNat i.val
  | .route i o => encNat 5 ++ [encBit i] ++ encNat (o.elim 0 fun b => if b then 2 else 1)
  | .fixed word => encNat 6 ++ word.map encBit

variable (R) [CommRing R]

/-- Registers 1–3 contain slot widths, the local rule, and the one scalar letter.
Register 0 starts empty. The scalar letter is shared by the whole table. -/
def factor0Regs (u : (rnState V B I σ ha).network.Site) : Reg (P1P5.EvalSym R) := by
  classical
  let X := rnState V B I σ ha
  exact fun j =>
    if j = 1 then (List.ofFn (slotWidth X u false)).flatMap encNat ++
      (List.ofFn (slotWidth X u true)).flatMap encNat
    else if j = 2 then encRule V (siteRule V B L I σ ha u)
    else if j = 3 then [.inl (if u = scalarSite V B I σ ha then (2 : R) ^ uOwned V B L I σ else 1)]
    else []

/-- The table output is already in the encoding of evaluator register 1. -/
def factor0State (u : (rnState V B I σ ha).network.Site) : List (P1P5.EvalSym R) :=
  P1P5.encState (P1P5.stateOfO (siteKeys (rnState V B I σ ha) u)
    (rnFactors V B L I σ ha P1Benes.NetBridge.bset R))

theorem factor0State_length (u : (rnState V B I σ ha).network.Site) :
    (factor0State V B L I σ ha R u).length = 2 ^ halfWidthSum (rnState V B I σ ha) u := by
  simp only [factor0State, P1P5.encState, P1P5.stateOfO, siteKeys, List.length_map, List.length_ofFn]

end RoutedSite

/-- Part (c), full table. The polynomial in `W` multiplies the required number of output entries. -/
def factor0_table_spec (V : FiniteMultiTapeMachine) (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (R : Type) [CommRing R] [Fintype R] : Prop :=
  ∃ (Prg : Prog (P1P5.EvalSym R)) (c : ℕ),
    ∀ {g h : ℕ} (B : ℕ) [NeZero B] (L : GuessLayout V g) (I : ℕ) [NeZero I]
      (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (u : (rnState V B I σ ha).network.Site),
      let W := halfWidthSum (rnState V B I σ ha) u
      ∃ (n : ℕ) (r : Reg (P1P5.EvalSym R)),
        Prog.Run [] Prg (factor0Regs V B L I σ ha R u) n r ∧
        r 0 = factor0State V B L I σ ha R u ∧
        n ≤ c * 2 ^ W * (W + 1) ^ c

/-- Part (c), one entry. Register 4 supplies the packed query word. -/
def factor0_entry_spec (V : FiniteMultiTapeMachine) (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (R : Type) [CommRing R] [Fintype R] : Prop :=
  ∃ (Prg : Prog (P1P5.EvalSym R)) (c : ℕ),
    ∀ {g h : ℕ} (B : ℕ) [NeZero B] (L : GuessLayout V g) (I : ℕ) [NeZero I]
      (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (u : (rnState V B I σ ha).network.Site)
      (z : (rnState V B I σ ha).network.Half u),
      let X := rnState V B I σ ha
      let regs := Function.update (factor0Regs V B L I σ ha R u) 4
        ((packHalf X u z).map encBit)
      ∃ (n : ℕ) (r : Reg (P1P5.EvalSym R)), Prog.Run [] Prg regs n r ∧
        (r 0).head? = some (.inl (rnFactors V B L I σ ha P1Benes.NetBridge.bset R u z)) ∧
        n ≤ c * (halfWidthSum X u + 1) ^ c

end

end P1SolFactor
