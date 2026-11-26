import OAI.Computability.VPVNP.IteratedCompression

/-!
# P1, task P5: push form of OpenAI's iterated compression (definitions)

Problem P1, Case 2, task P5 of research/g3/leanplan/PLAN.md (lane P1-lean-P5).

OpenAI's Theorem 7.1 (`OAI.Computability.VPVNP.Compression.exists_iterated_compression`,
VPVNP/IteratedCompression.lean:115) gives, for `E := B.execute κ hκ T hn X`, the global identity
`contract X.network F = ∑ p : E.history.Path, E.history.weight F p`, and bounds on the records of
the selected chain `E.termChain (B.records κ hκ T hn X) ι` of every branch `ι : E.Choices`.

Here the factors are pushed through the actual selected terms of a chain (`Term.push`,
NetworkKernel.lean:135): `chainPush`. The pushed factor at a final site is a finite sum over
`chainDom` of the products `chainSummand`. The domain consists of the old half-wire assignments of
all sites placed below the final site, level by level (the actual `Term.place`), and the summand is
the product of the original factors at the sites of level 0 and of the actual kernels
(`Term.kernel`) at all later sites. `chainAncestors` counts the sites of that placement tree.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression

open scoped Classical

noncomputable section

section Chain

variable {k : Type*} [CommSemiring k]

/-- Push the original factors through every selected term of the chain: iterated `Term.push`. -/
def chainPush : {N Y : Network} → TermChain k N Y → Factors k N → Factors k Y
  | _, _, .done _, F => F
  | _, _, .more t _ tail, F => chainPush tail (t.push F)

/-- The enumeration domain of the unrolled pushed factor at each site of the last network.
`D u` is the domain of the initial factor at `u`. A selected term `t` adds, at each new site `w`,
the old half-wire assignments of the old sites placed at `w` (`Placed t.place N.Half w`) and the
domains of these old sites (`Placed t.place D w`). -/
def chainDom : {N Y : Network} → TermChain k N Y → (N.Site → Type) → Y.Site → Type
  | _, _, .done _, D => D
  | _, _, @TermChain.more _ N _ t _ tail, D =>
      chainDom tail (fun w => Placed t.place N.Half w × Placed t.place D w)

/-- The enumeration domains are finite. -/
def chainDomFintype : {N Y : Network} → (c : TermChain k N Y) → (D : N.Site → Type) →
    (∀ u, Fintype (D u)) → ∀ v, Fintype (chainDom c D v)
  | _, _, .done _, _, h => h
  | _, _, @TermChain.more _ N _ t _ tail, D, h =>
      chainDomFintype tail (fun w => Placed t.place N.Half w × Placed t.place D w)
        (fun _ => by haveI := h; infer_instance)

instance chainDomInst {N Y : Network} (c : TermChain k N Y) (D : N.Site → Type)
    [h : ∀ u, Fintype (D u)] (v : Y.Site) : Fintype (chainDom c D v) :=
  chainDomFintype c D h v

/-- The summand of the unrolled pushed factor. `G u d` is the summand of the initial factor at `u`
for `d : D u`. Every later site `w` contributes the actual kernel of its selected term, read at the
old half-wire assignment placed at `w`. -/
def chainSummand : {N Y : Network} → (c : TermChain k N Y) → (D : N.Site → Type) →
    (∀ u, D u → N.Half u → k) → ∀ v, chainDom c D v → Y.Half v → k
  | _, _, .done _, _, G => G
  | _, _, @TermChain.more _ N _ t _ tail, D, G =>
      chainSummand tail (fun w => Placed t.place N.Half w × Placed t.place D w)
        (fun w d z => (∏ u, if h : w = t.place u then G u (d.2 u h) (d.1 u h) else 1) *
          t.kernel w d.1 z)

/-- The number of sites, over all levels, of the placement tree of a final site, the final site
included (`init u` counts the initial site `u`). With `init = 1` this is the number of local
factors of each summand `chainSummand`. -/
def chainAncestors : {N Y : Network} → TermChain k N Y → (N.Site → ℕ) → Y.Site → ℕ
  | _, _, .done _, init => init
  | _, _, .more t _ tail, init =>
      chainAncestors tail (fun w => 1 + ∑ u : t.Preimage w, init u.val)

/-- At every level, the old half-wire assignments placed at a new site fit into the field widths
recorded at that site: their number is at most `2 ^ (sum of the recorded widths)`. -/
def ChainHalfCovered : {N Y : Network} → TermChain k N Y → Prop
  | _, _, .done _ => True
  | _, _, @TermChain.more _ N _ t recs tail =>
      (∀ w, ∏ u : t.Preimage w, Fintype.card (N.Half u.val) ≤ 2 ^ ∑ f, (recs w).width f) ∧
        ChainHalfCovered tail

/-- Every wire of every network along the chain has at most `2 ^ M` payloads (`M` bits). -/
def ChainPayloadLe : {N Y : Network} → TermChain k N Y → ℕ → Prop
  | _, _, .done N, M => ∀ e : N.Edge, Fintype.card (N.Payload e) ≤ 2 ^ M
  | _, _, @TermChain.more _ N _ _ _ tail, M =>
      (∀ e : N.Edge, Fintype.card (N.Payload e) ≤ 2 ^ M) ∧ ChainPayloadLe tail M

end Chain

section Exec

variable {R : Type*} [CommSemiring R] {b n : ℕ}

/-- The branches (sequences of selected terms) of an execution form a finite type. -/
def choicesFintype : {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) →
    Fintype E.Choices
  | _, _, _, .done _ => inferInstanceAs (Fintype Unit)
  | _, _, _, .more p tail =>
      letI : ∀ i, Fintype (tail i).Choices := fun i => choicesFintype (tail i)
      inferInstanceAs (Fintype ((i : p.step.Choice) × (tail i).Choices))

instance choicesInst {a g : ℕ} {X : State a g} (E : StateExecution R b n X) :
    Fintype E.Choices :=
  choicesFintype E

end Exec

end

end P1P5
