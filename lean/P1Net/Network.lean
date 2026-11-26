import P1Net.Access
import OAI.Computability.VPVNP.NetworkKernel

/-!
# P4 (lane P1-lean-net): the access network of a deterministic verifier and its 0/1 factors

This is the network `N_{x,σ}` of the paper (`subsec:network`) BEFORE routing and degree padding: every
content wire goes directly from the previous access of a small block to its next access (`block_eq_prev`),
first accesses read from an initial-contents site, and the state chain links consecutive small intervals.
It is an OpenAI `NetworkKernel.Network`; its contraction is `contract_eq_count` (file `P1Net.Count`).
The routed form (Beneš stages, ports, lanes, degree padding: task P3) has the same contraction by
`unique_internal` of lane P1-lean-benes; that glue is not in this file.

Verifier model (`GuessLayout`): the input word depends on a guess `w : Fin g → Bool`; the initial cell `(k, c)`
holds `inputSymbol (w j)` if `guessAt k c = some j` and a fixed symbol `base k c` otherwise.
Guess cells whose block no small interval accesses (for the skeleton candidate `σ`) have no wire; their number
is `unseenCount`, and the factor of the first interval carries the scalar `2 ^ unseenCount` (approved by
G3-chief 09:05Z). Over `F_2` this scalar is `[unseenCount = 0]`.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP NetworkKernel WireTensor
open scoped Classical

/-! ## A generic contraction lemma -/

/-- The contraction of 0/1 factors, scaled by site constants, counts the edge labellings at which every
factor is one. -/
theorem contract_scaled_indicator {R : Type*} [CommRing R] (N : Network) (c : N.Site → R)
    (P : ∀ u, N.Half u → Prop) :
    contract N (fun u h => c u * (if P u h then 1 else 0)) =
      (∏ u, c u) * ((Finset.univ.filter fun z : (e : N.Edge) → N.Payload e =>
        ∀ u, P u (edgeAssignment N.src N.dst z u)).card : R) := by
  rw [contract_edgeSum]
  simp only [Finset.prod_mul_distrib, Fintype.prod_boole]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.natCast_card_filter]

/-! ## The verifier's input -/

variable (M : FiniteMultiTapeMachine)

/-- How the input word of the verifier depends on the guess. -/
structure GuessLayout (g : ℕ) where
  input : (Fin g → Bool) → List Bool
  guessAt : M.K → ℤ → Option (Fin g)
  base : M.K → ℤ → M.Γ
  init_some : ∀ w k c j, guessAt k c = some j → (absRun M (input w) 0).cells k c = M.inputSymbol (w j)
  init_none : ∀ w k c, guessAt k c = none → (absRun M (input w) 0).cells k c = base k c
  guessAt_inj : ∀ k c k' c' j, guessAt k c = some j → guessAt k' c' = some j → k = k' ∧ c = c'
  cellOf : Fin g → M.K × ℤ
  guessAt_cellOf : ∀ j, guessAt (cellOf j).1 (cellOf j).2 = some j

variable {M}

/-! ## The network -/

/-- Content wires are indexed by their destination: window `δ` of small interval `i` on tape `k`. -/
abbrev CEdge (M : FiniteMultiTapeMachine) (n : ℕ) := Fin n × M.K × Fin 3

/-- State wires: from small interval `i` to `i + 1`. -/
abbrev SEdge (n : ℕ) := {i : Fin n // i.val + 1 < n}

/-- `i'` as an element of `Fin n`, exact when `i' ≤ i`. -/
def toFinLt {n : ℕ} (i : Fin n) (i' : ℕ) : Fin n :=
  ⟨min i' i, lt_of_le_of_lt (min_le_right _ _) i.isLt⟩

theorem toFinLt_val {n : ℕ} (i : Fin n) {i' : ℕ} (h : i' ≤ i) : (toFinLt i i' : ℕ) = i' := by
  simp [toFinLt, min_eq_left h]

variable {n : ℕ}

/-- Source of a wire: the previous access of the block, or the initial-contents site of the edge. -/
def netSrc (σ : Fin n → M.K → Fin 3) : CEdge M n ⊕ SEdge n → Fin n ⊕ CEdge M n
  | .inl (i, k, δ) =>
    match prevAccess σ k (slotBlock σ k i δ) i with
    | some i' => .inl (toFinLt i i')
    | none => .inr (i, k, δ)
  | .inr s => .inl s.1

/-- Destination of a wire. -/
def netDst : CEdge M n ⊕ SEdge n → Fin n ⊕ CEdge M n
  | .inl (i, _, _) => .inl i
  | .inr s => .inl ⟨s.1.val + 1, s.2⟩

variable (M) (B : ℕ)

/-- Payloads: a small block of contents, or a state with all in-block offsets. -/
def netPayload (n : ℕ) : CEdge M n ⊕ SEdge n → Type :=
  Sum.elim (fun _ => Fin B → M.Γ) (fun _ => M.Q × (M.K → Fin B))

instance netPayloadFintype (n : ℕ) (e : CEdge M n ⊕ SEdge n) : Fintype (netPayload M B n e) :=
  match e with
  | .inl _ => show Fintype (Fin B → M.Γ) from inferInstance
  | .inr _ => show Fintype (M.Q × (M.K → Fin B)) from inferInstance

variable {M}

/-- The access network of the skeleton candidate `σ`. -/
noncomputable abbrev net (σ : Fin n → M.K → Fin 3) : Network where
  Site := Fin n ⊕ CEdge M n
  siteFintype := inferInstance
  Edge := CEdge M n ⊕ SEdge n
  edgeFintype := inferInstance
  src := netSrc σ
  dst := netDst
  Payload := netPayload M B n
  payloadFintype := netPayloadFintype M B n

/-! ## Factors -/

variable [NeZero B] {σ : Fin n → M.K → Fin 3}

theorem dst_state_pred (i : Fin n) (hi : 0 < i.val) :
    (Sum.inl i : Fin n ⊕ CEdge M n) =
      netDst (M := M) (.inr ⟨⟨i.val - 1, by omega⟩, by simp only; omega⟩) := by
  simp only [netDst, Sum.inl.injEq]
  ext
  simp only
  omega

/-- The incoming state and offsets of small interval `i`: the initial ones at `i = 0`, else the state wire. -/
def stateIn : (i : Fin n) → (net B σ).Half (.inl i) → M.Q × (M.K → Fin B)
  | ⟨0, _⟩, _ => (M.initialState, fun _ => finOfInt B 0)
  | ⟨j + 1, hj⟩, h => h.2 (.inr ⟨⟨j, by omega⟩, hj⟩) rfl

/-- The incoming local data at small interval `i`, read from the wires (initial state at `i = 0`). -/
def ivIn (i : Fin n) (h : (net B σ).Half (.inl i)) : LocalIn M B :=
  ⟨(stateIn B i h).1, (stateIn B i h).2, fun k δ => h.2 (.inl (i, k, δ)) rfl⟩

/-- Local data at the end of a small interval describe a halted, accepting configuration (the head of tape
`k` reads offset `off k` of window slot `move k`). -/
def Accepts (o : LocalOut M B) : Prop :=
  M.code o.q (fun k => o.blocks k (o.move k) (o.off k)) = none ∧ M.accept o.q = true

/-- The table of small interval `i` (0/1): `B` steps of `V` with block changes `σ i`, the outgoing state and
contents on the outgoing wires, acceptance at the last interval. -/
def ivOK (i : Fin n) (h : (net B σ).Half (.inl i)) : Prop :=
  (evolve (ivIn B i h)).move = σ i ∧
  (∀ hi : i.val + 1 < n,
    h.1 (.inr ⟨i, hi⟩) rfl = ((evolve (ivIn B i h)).q, (evolve (ivIn B i h)).off)) ∧
  (∀ (e : CEdge M n) (he : (Sum.inl i : Fin n ⊕ CEdge M n) = netSrc σ (.inl e)),
    h.1 (.inl e) he =
      (evolve (ivIn B i h)).blocks e.2.1 (slotOf σ e.2.1 i (slotBlock σ e.2.1 e.1 e.2.2))) ∧
  (i.val + 1 = n → Accepts B (evolve (ivIn B i h)))

/-- A block of initial contents is consistent with the input: fixed symbols outside the guess, any input
symbol on guess cells. -/
def PinOK {g : ℕ} (L : GuessLayout M g) (k : M.K) (Z : ℤ) (p : Fin B → M.Γ) : Prop :=
  ∀ o : Fin B, (∀ j, L.guessAt k (Z * B + o) = some j → ∃ b, p o = M.inputSymbol b) ∧
    (L.guessAt k (Z * B + o) = none → p o = L.base k (Z * B + o))

/-- The initial-contents site of a first access (vacuous when the window was accessed before). -/
def initOK {g : ℕ} (L : GuessLayout M g) (c : CEdge M n) (h : (net B σ).Half (.inr c)) : Prop :=
  ∀ he : (Sum.inr c : Fin n ⊕ CEdge M n) = netSrc σ (.inl c),
    PinOK B L c.2.1 (slotBlock σ c.2.1 c.1 c.2.2) (h.1 (.inl c) he)

/-- The predicate of every site. -/
def siteOK {g : ℕ} (L : GuessLayout M g) : ∀ u, (net B σ).Half u → Prop
  | .inl i => ivOK B i
  | .inr c => initOK B L c

variable (σ)

/-- Guess cell `j` lies in a small block that some small interval accesses. -/
def Seen {g : ℕ} (L : GuessLayout M g) (j : Fin g) : Prop :=
  ∃ i : Fin n, ∃ δ : Fin 3, (L.cellOf j).2 / B = slotBlock σ (L.cellOf j).1 i δ

/-- The number of guess cells in blocks that no small interval accesses. -/
noncomputable def unseenCount {g : ℕ} (L : GuessLayout M g) : ℕ :=
  Fintype.card {j : Fin g // ¬ Seen B σ L j}

/-- The site constants: `2 ^ unseenCount` at the first small interval, `1` elsewhere. -/
noncomputable def siteConst {g : ℕ} (L : GuessLayout M g) (R : Type*) [CommRing R] :
    Fin n ⊕ CEdge M n → R
  | .inl i => if i.val = 0 then (2 : R) ^ unseenCount B σ L else 1
  | .inr _ => 1

/-- The factors of the network. -/
noncomputable def fac {g : ℕ} (L : GuessLayout M g) (R : Type*) [CommRing R] : Factors R (net B σ) :=
  fun u h => siteConst B σ L R u * (if siteOK B L u h then 1 else 0)

theorem prod_siteConst [NeZero n] {g : ℕ} (L : GuessLayout M g) (R : Type*) [CommRing R] :
    ∏ u, siteConst B σ L R u = (2 : R) ^ unseenCount B σ L := by
  rw [Fintype.prod_sum_type]
  simp only [siteConst, Finset.prod_const_one, mul_one]
  rw [Finset.prod_eq_single (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The contraction counts the labellings at which every site predicate holds, times `2 ^ unseenCount`. -/
theorem contract_net [NeZero n] {g : ℕ} (L : GuessLayout M g) (R : Type*) [CommRing R] :
    contract (net B σ) (fac B σ L R) =
      (2 : R) ^ unseenCount B σ L * ((Finset.univ.filter fun z : (e : (net B σ).Edge) → (net B σ).Payload e =>
        ∀ u, siteOK B L u (edgeAssignment (net B σ).src (net B σ).dst z u)).card : R) := by
  rw [← prod_siteConst B σ L R]
  convert contract_scaled_indicator (net B σ) (siteConst B σ L R) (siteOK B L) using 3
  · funext h
    first | rfl | (simp only [fac]; congr)
  · congr 1
    ext z
    simp

end P1Net
