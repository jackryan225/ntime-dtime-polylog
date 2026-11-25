# Linear nondeterministic time with 2 log n guesses is not in deterministic time n (log n)^sigma (conditional paper proof)

**Status: paper proof, not machine-checked. Conditional on twelve stated inputs (H1 to H12) taken from three OpenAI preprints of
24 November 2026.**

Archived at Zenodo: https://doi.org/10.5281/zenodo.24527297
Repository: https://github.com/jackryan225/ntime-dtime-polylog

## The claim

Assuming twelve stated inputs taken from three OpenAI preprints of 24 November 2026 (two of them in a characteristic-2 form that we
derived from their proofs), we give a paper proof, not machine-checked, that for some constant sigma > 0 that we cannot compute, a
language decidable by multitape Turing machines in linear time with 2 log n nondeterministic bits is not decidable by any
deterministic multitape Turing machine in time O(n (log n)^sigma).

## The exact statement

**Theorem.** Assume H1, ..., H12. There is sigma > 0 such that

    NTIME[n; floor(2 log n)]  is not contained in  DTIME(n (log n)^sigma)

for multitape Turing machines. Consequently NTIME(n) is not contained in DTIME(n (log n)^sigma).

- NTIME[n; g]: languages A with a deterministic multitape verifier V and a constant c such that V, given x (|x| = n) on tape 1 and
  any y in {0,1}^g(n) on tape 2, halts within c max(n, 1) steps, and x is in A iff V(x, y) = 1 for some y.
- DTIME(f): languages decided by a deterministic multitape machine (any fixed number of tapes) in time O(f).
- sigma = 1/4 if characteristic 2 has no ports, sigma = s/2 if it has ports, where s > 0 comes from constants that H8 asserts to
  exist. We do not know which case holds, so sigma is not effective.
- The separating language is the complement of matrix transposition TRANS (if characteristic 2 has no ports), or the complement of a
  padded language A'' built from a language A that witnesses the parity time hierarchy at time n^2 (if it has ports).

**Stronger form (Section 8 of the paper), from the same inputs and no others.** coNTIME[n; floor(2 log n)] is not contained in
NTIME(n (log n)^sigma) intersected with parity-TIME(n (log n)^sigma); in particular it is not contained in UTIME(n (log n)^sigma)
(unambiguous time). The complement-side form, NTIME[n; floor(2 log n)] not contained in UTIME(n (log n)^sigma), follows if
characteristic 2 has ports and is open otherwise.

All definitions are written out in full in `STATEMENT.md`.

## The inputs H1 to H12

Sources: OpenAI preprints in `github.com/openai/math` (folder `preprints/`): **EG** *Euclidean geometry in the asymptotic spectrum of
tensors*, **CL** *Circuit lower bounds for Hamiltonian cycle and the permanent*, **T** *The logarithmic exponent of integer
multiplication on tapes*. Lean names are in OpenAI's Lean library in the same repository (folder `lean/`, commit 3344da5), compared
at the level of statements, not built by us. Details and line numbers: `HYPOTHESES.md`. The two inputs in a characteristic-2 form
derived by us from T's proofs are H4 and H5.

| H | What it is | Source | OpenAI's Lean |
|---|---|---|---|
| H1 | definition of "ports" for a field; (b) depends only on the characteristic; (c) finite points or CAT(0) spaces; (d) dyadic loop-free family | EG `port-graphs.tex` l.20-55 | (a)+(d) in dyadic form: definition `HasWireExpanders`; (c) used as `exists_catZero_completion`; (b) paper only; (d) in characteristic 2: paper only (`wireExpanders_of_port` is characteristic 0) |
| H2 | the class X_2 of Hadamard spaces with spectral prices in characteristic 2; price comparison for networks | CL `prices.tex` l.107-113, l.129-149; T `graphs.tex` l.14-50 | price comparison: in OpenAI's Lean (`wire_cost_le`, every field); the class: paper only (characteristic-0 analogue `SpectralTarget`) |
| H3 | logarithmic Poincare obstruction for classes without ports | CL `entropy.tex` l.54-66 | paper only (a characteristic-0 instance inside `common_placement`) |
| H4 | short edges and distant terminals (T's geometric lemma) in characteristic 2 | T `lower.tex` l.42-116 (transfer: T assumes Weak ETH) | paper only (`padded_graph_geometry` is characteristic 0) |
| H5 | entropy at paired terminals over F_2 | T `lower.tex` l.130-202 (transfer from the rationals) | in OpenAI's Lean (`paired_entropy_at_placement`, `paired_entropy`, every field) |
| H6 | conversion of a fixed motif | EG `compressor.tex` l.16-63 | in OpenAI's Lean (`MotifConversion.exists_conversion`, every field) |
| H7 | wire networks and local identities | EG `compressor.tex` l.267-312 | paper only (Lean definitions exist, not compared) |
| H8 | iterated compression (the compressor theorem) | EG `compressor.tex` l.314-340, l.524-527, l.548-551 | OpenAI's Lean proves these bounds for its own construction (`Compression.exists_iterated_compression`, every field with `HasWireExpanders`), which is not literally H8 with the scope used here; over F_2 its hypothesis needs H1(d) in characteristic 2: paper only |
| H9 | packing of a shrinking substep | EG `compressor-appendix.tex` l.9-105 | paper only (Lean construction files exist, not compared; our colour and offset rules follow OpenAI's Lean scans `orderedColor`, `orderedTagOffsets`) |
| H10 | the shrinking substep | EG `compressor.tex` l.344-445 | paper only (Lean construction files exist, not compared) |
| H11 | the refresh substep | EG `compressor.tex` l.447-509 | paper only (Lean construction files exist, not compared) |
| H12 | descriptors (records of the construction) | EG `compressor.tex` l.561-666 | paper only (Lean construction files exist, not compared) |

## What is new

- **The proof is a dichotomy on whether characteristic 2 "has ports".** No ports: a characteristic-2 form of OpenAI's transposition
  lower bound gives Omega(n sqrt(log n)) for deciding transposition, whose complement needs only floor(log n) + 1 guess bits. Ports:
  OpenAI's iterated compressor, applied to a network whose base graph is the coarse head-movement skeleton of a parity machine and
  whose lanes are sub-blocks, compresses parity time n^2 by a factor (log n)^s with a short universal quantifier; with the parity time
  hierarchy this refutes the inclusion.
- **Under Weak ETH, the statement already follows in a few lines from OpenAI's transposition lower bound**, whose proof runs over the
  rationals (Weak ETH gives "no ports" in characteristic 0). The new content is the second case (the skeleton in the base graph,
  Benes-routed lanes, locally checkable compressor records with an explicit locality lemma), which removes Weak ETH, and the stronger
  form for nondeterministic, parity and unambiguous machines.
- The best unconditional separations of linear nondeterministic from deterministic time known to us have factors of
  iterated-logarithm type (Paul-Pippenger-Szemeredi-Trotter 1983; Santhanam 2001; NTIME(n) not in DTIME(o(n (log* n)^{1/4})) as
  stated by Chen and Wang). Conditional separations of the same classes from fine-grained hypotheses are due to Lingas
  (arXiv:2011.02428). See `NOVELTY.md`.

## What is not claimed

- Nothing unconditional: every statement assumes H1 to H12.
- No explicit sigma.
- No separation of NTIME from coNTIME, and nothing about adjacent levels of the alternation hierarchy or about space.
- Nothing for random-access machines, multidimensional tapes or classes of nearly linear time defined by random-access machines
  (there TRANS is decidable in linear time).
- Nothing for circuits, branching programs or streaming models (TRANS has linear-size formulas).
- Nothing for randomized or quantum time (TRANS has a linear-time test with one-sided error).
- No lower bound for SAT or other standard problems: we know no reduction with small enough overhead.
- Lower bounds for verifying sorting (multiset equality of keyed lists) are not claimed; we have not checked them.
- The argument does not relativize, and is not meant to.
- No priority claim: three searches found no earlier statement; that is all.

## Files

- `ntime-dtime-polylog.tex`: the paper (LaTeX source, packages amsmath, amssymb, amsthm, geometry, microtype and xurl); compiled with tectonic to `ntime-dtime-polylog.pdf` (32 pages) with no error and no undefined reference.
- `STATEMENT.md`: the full, self-contained statement with every definition, the twelve inputs, the proof structure and the limits.
- `HYPOTHESES.md`: H1 to H12 with source lines, marks and Lean status.
- `CHECKS.md`: every review and blind check made so far.
- `NOVELTY.md`: the searches for earlier work and the closest work.

## Credit

Research driven, orchestrated and reviewed by Jack Ryan. Claude (by Anthropic), GPT-6.2 Astra (by OpenAI) and Gemini 4 Neon (by Google) collaborated in finding and writing the proofs.

No professional mathematician has refereed this repository. The proof is not machine-checked.

Who did what: Claude found the first version of the argument, wrote the paper and made the independent readings; GPT-6.2 Astra
wrote the repaired proof of the port case (Lemma P) and re-derived, blind, the no-ports case and the nondeterministic Lemma A;
Gemini 4 Neon looked for general reasons why the argument must fail (oracles, known upper bounds) and proposed the
unambiguous-time version. GPT-6.2 Sol (by OpenAI) ran literature searches and reference checks, drafted the statement
description and made a final check of the release text.
