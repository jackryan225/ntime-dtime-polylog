import P1P5.Main

/-!
# P1, task P8a: local evaluation of one pushed factor (data layer)

The pushed factor `W_v = chainPush chain F v` (lane P5) is computed by a level-by-level table
algorithm on the CONE of `v` only (the sites of each level whose image under the later placements
is `v`; their number over all levels is `chainAncestors ≤ C^T`).

Data (`EvalData R`), fixed format, independent of the network:
* a STATE is a list of ring elements: the factor tables of the cone sites of one level, concatenated
  (site order, then half-assignment order: `keysOf`);
* a LEVEL is a list of ENTRIES, one per pair (new cone site `w`, new half-assignment `z`); an entry is a
  list of PAIRS `(K, ptrs)`, one per old half-assignment `x` placed at `w`: `K` = the actual kernel entry
  `t.kernel w x z`, `ptrs` = the positions in the old state of the entries `(u, x_u)` of the old
  sites `u` placed at `w`;
* `stepEval L st` = for each entry, `∑ (K * ∏ st[ptr])`; `runLevels` iterates it.

`encLevels chain v` and `stateOf N S F` give the canonical encoding of a chain cone and of the original
factors (the "oracle tables" of the level-0 cone sites). Correctness: `P1P5.Wv_eq_run` (EvalCorrect).
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression

open scoped Classical

noncomputable section

/-! ### The abstract evaluator (no networks) -/

/-- One level of the table algorithm: entries of pairs (kernel value, pointers into the old state). -/
abbrev Level (R : Type) := List (List (R × List ℕ))

variable {R : Type} [CommRing R]

/-- One level: each entry becomes `∑ K * ∏ st[ptr]` (missing positions read as 0). -/
def entryEval (st : List R) (e : List (R × List ℕ)) : R :=
  (e.map fun p => (p.2.map fun i => st.getD i 0).prod * p.1).sum

/-- One level: each entry becomes `∑ K * ∏ st[ptr]`. -/
def stepEval (L : Level R) (st : List R) : List R :=
  L.map (entryEval st)

/-- All levels, first level first. -/
def runLevels : List (Level R) → List R → List R
  | [], st => st
  | L :: Ls, st => runLevels Ls (stepEval L st)

/-! ### Canonical encoding of a cone -/

/-- A fixed enumeration of a finite type. -/
def enumL (α : Type) [Fintype α] : List α := Finset.univ.toList

/-- Keys of a state: (site, half-assignment). -/
abbrev Key (N : Network) := Σ u : N.Site, N.Half u

/-- The keys of the state of the sites satisfying `S`, in the fixed order. -/
def keysOf (N : Network) (S : N.Site → Prop) : List (Key N) :=
  ((enumL N.Site).filter fun u => decide (S u)).flatMap fun u =>
    (enumL (N.Half u)).map fun x => (⟨u, x⟩ : Key N)

/-- The state of the factors `F` on the sites satisfying `S`. -/
def stateOf (N : Network) (S : N.Site → Prop) (F : Factors R N) : List R :=
  (keysOf N S).map fun key => F key.1 key.2

/-- Pointers of one old half-assignment `x` placed at `w`: positions of `(u, x_u)` in the old state. -/
def pointers {N : Network} (t : Term R N) (S : N.Site → Prop) (w : t.output.Site)
    (x : Placed t.place N.Half w) : List ℕ :=
  (enumL (t.Preimage w)).map fun u => (keysOf N S).idxOf (⟨u.1, x u.1 u.2⟩ : Key N)

/-- The entry of the new key `(w, z)`: one pair (actual kernel entry, pointers) per placed `x`. -/
def levelEntry {N : Network} (t : Term R N) (S : N.Site → Prop) (key : Key t.output) :
    List (R × List ℕ) :=
  (enumL (Placed t.place N.Half key.1)).map fun x => (t.kernel key.1 x key.2, pointers t S key.1 x)

/-- The level data of one selected term `t`: old cone `S`, new cone `S'`. -/
def levelData {N : Network} (t : Term R N) (S : N.Site → Prop) (S' : t.output.Site → Prop) :
    Level R :=
  (keysOf t.output S').map (levelEntry t S)

/-- Composite placement of a site of the first network to a site of the last network. -/
def toFinal : {N Y : Network} → TermChain R N Y → N.Site → Y.Site
  | _, _, .done _ => id
  | _, _, .more t _ tail => fun u => toFinal tail (t.place u)

/-- The levels of the cone of the final site `v`. -/
def encLevels : {N Y : Network} → TermChain R N Y → Y.Site → List (Level R)
  | _, _, .done _, _ => []
  | _, _, .more t _ tail, v =>
      levelData t (fun u => toFinal tail (t.place u) = v) (fun w => toFinal tail w = v) ::
        encLevels tail v

/-- Position of the half-assignment `z` of `v` in the final state. -/
def finalIndex (Y : Network) (v : Y.Site) (z : Y.Half v) : ℕ :=
  (keysOf Y fun w => w = v).idxOf (⟨v, z⟩ : Key Y)

/-! ### Size of the data (the cost parameter of the stack program) -/

/-- Size of a state: its length. Size of a level: one per pair plus the unary pointer lengths. -/
def levelSize (L : Level R) : ℕ :=
  (L.map fun e => (e.map fun p => 1 + (p.2.map fun i => i + 1).sum).sum + 1).sum

/-- Total input size of an evaluation (levels, state, final index). -/
def dataSize (Ls : List (Level R)) (st : List R) (i : ℕ) : ℕ :=
  (Ls.map levelSize).sum + Ls.length + st.length + i

end

end P1P5
