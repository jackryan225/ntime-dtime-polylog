import P1Net.AccessPerm
import P1Net.Network

/-!
# P3 (lane P1-lean-net, copy A): the 0/1 factors of the routed lane network and the statement of P4

Payload words of `stateNet` are read through `asWord W` (pad with `false` / truncate to the expected width `W`),
so a half-edge of width `0` (unmated, twin, padding) reads as the zero word.
* String width `Wx` (block contents one-hot per cell: `B * |Γ|` bits; state: one-hot state, one-hot offset per
  tape), tuple width `Wt = |Ext K| * Wx` (the strings of all external half-edges of a table, in path order).
* Lanes in binary (`laneEquiv`, little endian); routing addresses `addrOf π g` (type bits `0..2`, lane bits
  `3..h+2`), content permutation `accAddr` (the access permutation `accPerm`), state permutation `stAddr`
  (chain end lane `0` → table lane `0` → … → table lane `N-1` → chain end lane `0`; other chain-end lanes fixed).
* `routeOK`: a routing position copies its selected in-arc to its selected out-arc and puts zero on the other
  out-arc (switch settings `bset m π` of the benes lane, a parameter).
* `rnSiteOK`: tables (`evolve`, skeleton entry, acceptance at the last small interval), path ties, ports (pins of
  the initial contents at the first owner, ties otherwise), routing, chain ends (initial state at big interval
  `0`, lane `0`); twins and last owners: no condition.
* `rnFactors`: `0/1` indicators, times `2 ^ uOwned` (guess cells in big blocks owned by no big interval) at the
  chain start.
* `ContractEqCount`: the statement of P4 for this network (a `Prop`, not yet proved).
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel

/-! ## Words -/

/-- A word read at width `W` (padded with `false` or truncated). -/
def asWord (W : ℕ) {w : ℕ} (x : Fin w → Bool) : Fin W → Bool :=
  fun j => if hj : (j : ℕ) < w then x ⟨j, hj⟩ else false

/-- One-hot code of an element of a finite type. -/
noncomputable def oneHot {α : Type} [Fintype α] (x : α) : Fin (Fintype.card α) → Bool :=
  fun j => decide (j = Fintype.equivFin α x)

/-! ## Lanes and routing addresses -/

/-- Lane numbers in binary (bit `j` has weight `2 ^ j`). -/
def laneEquiv (h : ℕ) : BitWord h ≃ Fin (2 ^ h) := finFunctionFinEquiv

/-- Type numbers in binary. -/
def typeEquiv : BitWord 3 ≃ Fin 8 := (finFunctionFinEquiv : BitWord 3 ≃ Fin (2 ^ 3)).trans (finCongr (by norm_num))

/-- State type numbers. -/
def type1Equiv : BitWord 1 ≃ Fin 2 := (finFunctionFinEquiv : BitWord 1 ≃ Fin (2 ^ 1)).trans (finCongr (by norm_num))

/-- The routing address of type bits `π` (bits `0 .. t-1`) and lane `g` (bits `t ..`). -/
def addrOf {t h : ℕ} (π : BitWord t) (g : BitWord h) : Routing.Addr (t + h) :=
  fun b => if hb : (b : ℕ) < t then π ⟨b, hb⟩ else g ⟨b - t, by have := b.isLt; omega⟩

/-- Type and lane bits of an address. -/
def addrSplit {t h : ℕ} (a : Routing.Addr (t + h)) : BitWord t × BitWord h :=
  (fun j => a ⟨j, by have := j.isLt; omega⟩, fun j => a ⟨j + t, by have := j.isLt; omega⟩)

/-- Addresses are pairs (type bits, lane bits). -/
def addrEquiv (t h : ℕ) : BitWord t × BitWord h ≃ Routing.Addr (t + h) where
  toFun p := addrOf p.1 p.2
  invFun := addrSplit
  left_inv p := by
    obtain ⟨π, g⟩ := p
    simp only [addrSplit, addrOf, Prod.mk.injEq]
    constructor
    · funext j
      simp [j.isLt]
    · funext j
      simp
  right_inv a := by
    funext b
    simp only [addrSplit, addrOf]
    split_ifs with hb
    · rfl
    · congr 1
      exact Fin.ext (by simp; omega)

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-- Items of the content routing as addresses. -/
def itemEquiv (h : ℕ) : Fin 8 × Fin (2 ^ h) ≃ Routing.Addr (3 + h) :=
  ((typeEquiv.prodCongr (laneEquiv h)).symm).trans (addrEquiv 3 h)

/-- Items of the state routing as addresses. -/
def stItemEquiv (h : ℕ) : Fin 2 × Fin (2 ^ h) ≃ Routing.Addr (1 + h) :=
  ((type1Equiv.prodCongr (laneEquiv h)).symm).trans (addrEquiv 1 h)

/-- The content permutation of big interval `ι` and tape `k` on routing addresses. -/
noncomputable def accAddr (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K) :
    Equiv.Perm (Routing.Addr (3 + h)) :=
  (itemEquiv h).permCongr (accPerm I σ ι k)

/-- The state chain inside one big interval: chain start (type `0`, lane `0`) → table lane `0` → … → table lane
`N - 1` → chain end (type `0`, lane `0`); the other chain lanes are fixed. -/
def stNext (x : Fin 2 × Fin (2 ^ h)) : Fin 2 × Fin (2 ^ h) :=
  if x.1 = 0 then (if (x.2 : ℕ) = 0 then (1, x.2) else x)
  else if hx : (x.2 : ℕ) + 1 < 2 ^ h then (1, ⟨x.2 + 1, hx⟩) else (0, ⟨0, Nat.two_pow_pos h⟩)

/-- Inverse of `stNext`. -/
def stPrev (y : Fin 2 × Fin (2 ^ h)) : Fin 2 × Fin (2 ^ h) :=
  if y.1 = 0 then (if (y.2 : ℕ) = 0 then (1, ⟨2 ^ h - 1, by have := Nat.two_pow_pos h; omega⟩) else y)
  else if hy : (y.2 : ℕ) = 0 then (0, y.2) else (1, ⟨y.2 - 1, by have := y.2.isLt; omega⟩)

theorem stPrev_stNext (x : Fin 2 × Fin (2 ^ h)) : stPrev (stNext x) = x := by
  obtain ⟨t, j⟩ := x
  have hj := j.isLt
  have hN := Nat.two_pow_pos h
  fin_cases t
  · by_cases h0 : (j : ℕ) = 0
    · simp [stNext, stPrev, h0, Fin.ext_iff] <;> omega
    · simp [stNext, stPrev, h0]
  · by_cases hs : (j : ℕ) + 1 < 2 ^ h
    · simp [stNext, stPrev, hs]
    · simp [stNext, stPrev, hs, Fin.ext_iff] <;> omega

/-- The state permutation. -/
noncomputable def stPerm (h : ℕ) : Equiv.Perm (Fin 2 × Fin (2 ^ h)) :=
  Equiv.ofBijective (stNext (h := h))
    ⟨Function.LeftInverse.injective stPrev_stNext,
      Finite.injective_iff_surjective.1 (Function.LeftInverse.injective stPrev_stNext)⟩

/-- The state permutation on routing addresses. -/
noncomputable def stAddr (h : ℕ) : Equiv.Perm (Routing.Addr (1 + h)) := (stItemEquiv h).permCongr (stPerm h)

/-! ## Routing positions -/

/-- A routing position at column `c` (of `2m` columns) with address `a`: its item comes from the selected in-arc
(the source at column `0`); it goes to the selected out-arc (the destination at the last column); the other
out-arc carries zero. `in2`/`in3`: straight/cross in-words, `out0`/`out1`: straight/cross out-words. -/
def routeOK {m W : ℕ} [NeZero m] (s : Routing.Settings m) (c : ℕ) (a : Routing.Addr m)
    (in2 in3 out0 out1 : Fin W → Bool) : Prop :=
  let item := if c = 0 then in2 else if s (c - 1) (Routing.rep m (c - 1) a) then in3 else in2
  if c + 1 = 2 * m then out0 = item
  else if s c (Routing.rep m c a) then out1 = item ∧ out0 = fun _ => false
  else out0 = item ∧ out1 = fun _ => false

/-! ## The factors -/

section Factors

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

/-- Width of a string (contents of a small block, or state and offsets). -/
def strWidth : ℕ := B * Fintype.card V.Γ + (Fintype.card V.Q + Fintype.card V.K * B)

/-- Width of a table tuple. -/
def tupWidth : ℕ := Fintype.card (Ext V.K) * strWidth V B

/-- Code of the contents of a small block. -/
noncomputable def encC (b : Fin B → V.Γ) : Fin (strWidth V B) → Bool :=
  asWord (strWidth V B) (fun j : Fin (B * Fintype.card V.Γ) =>
    oneHot (b (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)

/-- Code of a state with the offsets of all heads. -/
noncomputable def encS (q : V.Q) (off : V.K → Fin B) : Fin (strWidth V B) → Bool :=
  asWord (strWidth V B) (Fin.append (oneHot q) (fun j : Fin (Fintype.card V.K * B) =>
    decide ((finProdFinEquiv.symm j).2 = off ((Fintype.equivFin V.K).symm (finProdFinEquiv.symm j).1))))

/-- The string of an external half-edge of a table with local data `d` and `o`. -/
noncomputable def extData (d : LocalIn V B) (o : LocalOut V B) : Ext V.K → Fin (strWidth V B) → Bool
  | .stIn => encS V B d.q d.off
  | .stOut => encS V B o.q o.off
  | .cIn k δ => encC V B (d.blocks k δ)
  | .cOut k δ => encC V B (o.blocks k δ)

/-- A table tuple: the strings of all external half-edges, in path order. -/
noncomputable def tupleWord (f : Ext V.K → Fin (strWidth V B) → Bool) : Fin (tupWidth V B) → Bool :=
  fun j => f ((extIdx V.K).symm (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

/-- The segment of external string `c` in a tuple. -/
noncomputable def segment (c : Ext V.K) (T : Fin (tupWidth V B) → Bool) : Fin (strWidth V B) → Bool :=
  fun o => T (finProdFinEquiv (extIdx V.K c, o))

/-- External strings that enter the table. -/
def Ext.isIn : Ext V.K → Bool
  | .stIn => true
  | .cIn _ _ => true
  | _ => false

/-- The network `N_{x,σ}` with the widths of this file. -/
noncomputable abbrev rnState : State a h :=
  stateNet (K := V.K) I σ ha (strWidth V B) (strWidth V B) (tupWidth V B)

/-- The edge arriving at in-slot `j` of site `u`. -/
def inEdge (X : State a h) (u : X.Base × BitWord h) (j : Fin (2 ^ a)) :
    (X.Base × BitWord h) × Fin (2 ^ a) :=
  ((((X.slots.base.target.symm (u.1, j)).1, u.2 - X.slots.displacement (X.slots.base.target.symm (u.1, j))),
    (X.slots.base.target.symm (u.1, j)).2))

theorem inEdge_dst (X : State a h) (u : X.Base × BitWord h) (j : Fin (2 ^ a)) :
    u = X.network.dst (inEdge X u j) := by
  obtain ⟨x, l⟩ := u
  simp [inEdge, State.network, Refresh.actualWireGraph, LiftedSlots.actualGraph_target]

/-- The word on out-slot `i` of site `u`, read at width `W`. -/
noncomputable def outWord (X : State a h) (u : X.Base × BitWord h) (z : X.network.Half u)
    (i : Fin (2 ^ a)) (W : ℕ) : Fin W → Bool :=
  asWord W (z.1 (u, i) rfl)

/-- The word on in-slot `j` of site `u`, read at width `W`. -/
noncomputable def inWord (X : State a h) (u : X.Base × BitWord h) (z : X.network.Half u)
    (j : Fin (2 ^ a)) (W : ℕ) : Fin W → Bool :=
  asWord W (z.2 (inEdge X u j) (inEdge_dst X u j))

/-- Local predicate of a site of `N_{x,σ}`. -/
def rnSiteOK (u : (rnState V B I σ ha).Base × BitWord h) (z : (rnState V B I σ ha).network.Half u) :
    Prop :=
  let X := rnState V B I σ ha
  let Wx := strWidth V B
  let Wt := tupWidth V B
  let O := fun (s : Fin 4) (W : ℕ) => outWord X u z (s.castLE ha) W
  let In := fun (s : Fin 4) (W : ℕ) => inWord X u z (s.castLE ha) W
  let ι : Fin I := u.1.1.1
  let i : ℕ := ι * 2 ^ h + laneEquiv h u.2
  let linked : Prop := netMate I σ (u.1.1, 1) ≠ none
  if u.1.2 then True else
  match u.1.1.2 with
  | .tabC => ∃ d : LocalIn V B, O 0 Wt = tupleWord V B (extData V B d (evolve d)) ∧
      (∀ hi : i < I * 2 ^ h, (evolve d).move = σ ⟨i, hi⟩) ∧
      (i + 1 = I * 2 ^ h → Accepts B (evolve d))
  | .tabP c => (linked → O 1 Wt = In 0 Wt) ∧
      (if Ext.isIn V c then In 2 Wx = segment V B c (In 0 Wt) else O 2 Wx = segment V B c (In 0 Wt))
  | .portIn k δ =>
      if netMate I σ (u.1.1, 1) = none then
        ∃ p : Fin B → V.Γ, PinOK B L k (portBlock I σ ι k δ (laneEquiv h u.2)) p ∧ O 0 Wx = encC V B p
      else O 0 Wx = In 1 Wx
  | .portOut _ _ => linked → O 1 Wx = In 0 Wx
  | .rt k c π =>
      routeOK (bset (3 + h) (accAddr I σ ι k)) c (addrOf π u.2) (In 2 Wx) (In 3 Wx) (O 0 Wx) (O 1 Wx)
  | .st c π =>
      routeOK (bset (1 + h) (stAddr h)) c (addrOf π u.2) (In 2 Wx) (In 3 Wx) (O 0 Wx) (O 1 Wx)
  | .eIn =>
      if (ι : ℕ) = 0 then
        O 0 Wx = (if (laneEquiv h u.2 : ℕ) = 0 then encS V B V.initialState (fun _ => finOfInt B 0)
          else fun _ => false)
      else O 0 Wx = In 1 Wx
  | .eOut => linked → O 1 Wx = In 0 Wx

/-- A guess cell in a big block that no big interval owns. -/
def UnownedCell (j : Fin g) : Prop :=
  ¬ ∃ ι : Fin I, Owns I σ (L.cellOf j).1 ι ((L.cellOf j).2 / (B : ℤ) / ((2 ^ h : ℕ) : ℤ))

/-- The number of guess cells in big blocks that no big interval owns. -/
noncomputable def uOwned : ℕ :=
  @Fintype.card {j : Fin g // UnownedCell V B L I σ j} (by classical exact inferInstance)

/-- The site of the scalar: the chain start of big interval `0`, lane `0`. -/
def scalarSite : (rnState V B I σ ha).Base × BitWord h := ((((0 : Fin I), Loc.eIn), false), 0)

open scoped Classical in
/-- **The factors of `N_{x,σ}`.** -/
noncomputable def rnFactors (R : Type*) [CommRing R] : Factors R (rnState V B I σ ha).network :=
  fun u z => (if u = scalarSite V B I σ ha then (2 : R) ^ uOwned V B L I σ else 1) *
    (if rnSiteOK V B L I σ ha bset u z then 1 else 0)

open scoped Classical in
/-- **Statement of P4** for the routed network (task P4, `contract_eq_count`): with canonical switch settings,
the contraction is the number of guesses whose run accepts within `I N B` steps with skeleton `σ`. -/
def ContractEqCount (R : Type*) [CommRing R] : Prop :=
  (∀ (m : ℕ) [NeZero m] (π : Equiv.Perm (Routing.Addr m)), Routing.route (bset m π) = π) →
  contract (rnState V B I σ ha).network (rnFactors V B L I σ ha bset R) =
    ((Finset.univ.filter fun w : Fin g → Bool =>
        MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧
          skeleton V (L.input w) B (I * 2 ^ h) = σ).card : R)

end Factors

end P1Net
