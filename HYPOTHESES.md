# The twelve inputs H1 to H12

The theorem is proved on paper **relative to H1 to H12**. Each Hi is our restatement of results, constructions or proof facts
of three OpenAI preprints dated 24 November 2026 (public repository `github.com/openai/math`, folder `preprints/`):

- **EG** = *Euclidean geometry in the asymptotic spectrum of tensors*, folder
  `preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/`
- **CL** = *Circuit lower bounds for Hamiltonian cycle and the permanent*, folder
  `preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/`
- **T** = *The logarithmic exponent of integer multiplication on tapes*, folder
  `preprints/The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026/build/`

Lean names refer to OpenAI's Lean library in the same repository, folder `lean/`, commit `3344da5`, paths below
`lean/OAI/Computability/`. "In OpenAI's Lean" means that a theorem with this statement (at the level of statements, compared by
reading) exists there; we did **not** build these files. "Paper only" means that we identified no Lean statement that covers the
form we use; where Lean construction files exist but were not compared with the text, this is said.

Marks: **EXACT** = the cited lines say what the hypothesis says. **TRANSFER** = the cited lines state it for the rationals (or under
Weak ETH) and we use a characteristic-2 form derived from their proof; the change is written into the hypothesis in the paper.

| H | Content (short) | Source lines | Mark | OpenAI's Lean | Used in |
|---|---|---|---|---|---|
| H1(a) | definition: a field *has ports* (one uniform nonlinear Poincare inequality for a bounded-degree regular graph family of unbounded order, in all spectral spaces over the field) | EG `port-graphs.tex` l.20-29 | EXACT | definition; the dyadic form (a)+(d) is `VPVNP.SpectralGeometry.HasWireExpanders k` (`VPVNP/WireExpanders.lean` l.35) | both cases |
| H1(b) | having ports depends only on the characteristic | EG `port-graphs.tex` l.30-31 (EG `lem:comparison`, `prices.tex` l.239) | EXACT | paper only (no Lean statement identified) | both cases |
| H1(c) | one may test finite spectral points or complete CAT(0) spectral spaces | EG `port-graphs.tex` l.32-33 | EXACT | used in Lean as `exists_catZero_completion` (called at `VPVNP/WireExpanders.lean` l.65) | Case 1 |
| H1(d) | with ports, the family can be taken connected, loop-free, of one power-of-two degree and power-of-two orders | EG `port-graphs.tex` l.33-55 | EXACT (stated for every field) | characteristic 0 only: `wireExpanders_of_port` (`MultitapeWeakETH/PortTemplates.lean` l.45); characteristic 2: paper only (no Lean statement identified) | Case 2 |
| H2 | the class X_2 of Hadamard spaces with spectral prices in characteristic 2; "admits ports" equals ports in the sense of H1; price comparison: a network's wire costs bound the price of any product of equality wires obtained from it by local linear maps | CL `prices.tex` l.107-113 and l.129-149; T `graphs.tex` l.14-50 | EXACT against CL (T states the comparison for rational tensors; CL l.107-113 for every field) | price comparison: `wire_cost_le` (`MultitapeWeakETH/Geometry.lean` l.12, every field); class: characteristic-0 analogue `SpectralTarget` (`MultitapeWeakETH/Cloud.lean` l.12) | Case 1 |
| H3 | logarithmic Poincare obstruction: in a class of Hadamard spaces without ports, the Poincare constant of a d-regular graph on n vertices is at least c log n / log(d+1) | CL `entropy.tex` l.54-66 (CL `thm:loggraph`) | EXACT (proof is field-free) | general class: paper only (no Lean statement identified); a characteristic-0 instance inside `common_placement (price : PriceZero)` (`MultitapeWeakETH/Placement.lean` l.13) | Case 1 (via H4) |
| H4 | short edges and distant terminals: a placement in X_2 with total edge cost O(bP/sqrt(log P)), terminal distances near 1 on average, and a central-point bound | T `lower.tex` l.42-116 (T `lem:geometry`) | TRANSFER: T assumes Weak ETH, used only at l.70-73 to get a class without ports; we use "characteristic 2 has no ports" (via H1, H3) | characteristic 0 only: `padded_graph_geometry (price : PriceZero)` (`MultitapeWeakETH/GraphGeometry.lean` l.13); characteristic 2: paper only (no Lean statement identified) | Case 1 |
| H5 | entropy at paired terminals: if pins make the network contract to the product of basis vectors at pairs (a_j, t_j), the chain-rule entropy weighted by the pair distances is at most the wire cost plus a central term | T `lower.tex` l.130-202 (T `lem:entropy`) | TRANSFER: "over the rationals" and "nonzero scalar multiple" become "over F_2" and "equal to" | `paired_entropy_at_placement` (`MultitapeWeakETH/EntropyPrice.lean` l.164) and `paired_entropy` (l.125), stated for every field `[Field K]`; K = ZMod 2 gives H5 | Case 1 |
| H6 | conversion of a fixed motif: an exact sum identity with supply widths bounded by the spectral energy ratio, parameters solving fixed integer equations in the field | EG `compressor.tex` l.16-31 and l.36-63 (EG `thm:conversion`) | EXACT | `MotifConversion.exists_conversion` (`VPVNP/MotifConversion.lean` l.327), every field | Case 2 |
| H7 | wire networks of the stated form (base graph, lanes, displacements, widths) and the local identities of one substep | EG `compressor.tex` l.267-312 | EXACT | paper only (Lean definitions `NetworkKernel`, `State` exist; not compared) | Case 2 |
| H8 | iterated compression: with ports, T blocks of local identities give final width at most 2^-T (sqrt(L_0) + O(P_0)), fields of length at most C_2^T (W_0 + 1), at most C_2^T occurrences per final position, one parameter solution in the field; plus two facts of the proof (block structure, local hidden sums); scope: every proper colouring, every valid tag offsets, every even payload split and either layout tie rule | EG `compressor.tex` l.314-340, l.524-527, l.548-551 (EG `thm:compressor`) | EXACT | OpenAI's Lean proves these bounds for its own construction: `Compression.exists_iterated_compression` (`VPVNP/IteratedCompression.lean` l.115-136), every field with `HasWireExpanders k`; this is not literally H8 with the scope used here (EG's text construction, all admissible choices); the step "F_2 has ports => HasWireExpanders (ZMod 2)" is H1(d) in characteristic 2: paper only | Case 2 |
| H9 | the packing of a shrinking substep (greedy colouring, lane split, bundles, tag offsets with the exclusion conditions, role counts, slot identifiers) | EG `compressor-appendix.tex` l.9-105 (EG `lem:compressor-slots` and its construction) | EXACT | paper only (Lean construction files exist, e.g. `VPVNP/SlotGreedyScan.lean`; compared datum by datum by an independent reader, CHECKS.md row 28: H9 holds as used, up to the identifier key; our colour and offset rules follow `orderedColor` and `orderedTagOffsets` exactly) | Case 2 |
| H10 | the shrinking substep (motifs, the two supply groups, one global layout, surviving arcs, kernels) | EG `compressor.tex` l.344-445 | EXACT | paper only as a theorem; compared datum by datum with OpenAI's executed Lean construction by an independent reader (CHECKS.md row 28): holds as used, up to the identifier key | Case 2 |
| H11 | the refresh substep (port blocks, external wires, port-graph ties) | EG `compressor.tex` l.447-509 | EXACT | paper only as a theorem; compared datum by datum with OpenAI's executed Lean construction by an independent reader (CHECKS.md row 28): holds as used, up to the identifier key | Case 2 |
| H12 | descriptors: the records that the construction schedules and how they are computed (term encodings, layout rule, identifiers, refresh lists) | EG `compressor.tex` l.561-666 (EG `lem:descriptors`) | EXACT (the RAM itself is not run; only its construction is used) | paper only as a theorem; the descriptor data were compared with OpenAI's Lean by the same reader (CHECKS.md row 28): local, up to the identifier key | Case 2 |

Case 1 (characteristic 2 has no ports) uses H1(a)-(c), H2, H3, H4, H5. Case 2 (characteristic 2 has ports) uses H1(a), (b), (d) and
H6-H12. The stronger form for nondeterministic, parity and unambiguous machines (Section 8 of the paper) uses exactly the same inputs.
The two inputs in a characteristic-2 form derived by us from T's proofs are H4 and H5.

**Identifiers in OpenAI's Lean (second check, 25 November 2026).** The paper names slots and orders the demands of a bundle by EG's
identifiers, with lanes taken relative to the numbered vertex (H9(vii), H12). OpenAI's Lean construction instead uses a mixed-radix key
of the lane-0 representative. An independent reader found that both are translation invariant and computed from local data, so the
locality radii 3/6/7/1 and the uniqueness argument are unchanged; a proof tied to OpenAI's Lean must use the Lean key in checks C7 and
C10 (see CHECKS.md, row 28).

**Weakest inputs**, in the order of the independent reader: (1) H8 together with H9-H11, because the paper's locality lemma is about
EG's text construction, while the Lean theorem certifies OpenAI's Lean construction (the two fix some free choices differently;
the paper follows the Lean greedy scans exactly); (2) H4 in characteristic 2 (audited, no Lean); (3) H1(d) in characteristic 2
(short duplication argument, paper only); (4) H3 in the general-class form (paper only, field-free).

The full text of every hypothesis is in Section 4 of the paper; a self-contained description of the statement and of every
hypothesis is in `STATEMENT.md`.
