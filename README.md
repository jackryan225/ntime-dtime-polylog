# Linear nondeterministic time with 2 log n guesses is not in deterministic time n (log n)^sigma (proved in Lean 4)

**Status: machine-checked in Lean 4, with no assumption.** The twelve inputs H1 to H12 of the paper are no longer assumed:
OpenAI's Lean library is part of the build, and its proofs are checked by the same kernels as ours. Not peer reviewed: no
human has refereed the paper, the Lean statement or the Lean proof.

Archived at Zenodo: https://doi.org/10.5281/zenodo.24527297
Repository: https://github.com/jackryan225/ntime-dtime-polylog

## The theorem, as checked in Lean

There are a real number sigma > 0 and a language L of bit strings such that

1. L is in NTIME[n; floor(2 log n)]: a multitape Turing machine verifier decides it in linear time with floor(2 log2 n) guess
   bits; and L is in NTIME(n);
2. L is not in DTIME(n (log n)^sigma): no deterministic multitape Turing machine decides L within C (n (log2 n)^sigma + 1)
   steps, for any constant C.

So NTIME[n; floor(2 log n)] and NTIME(n) are not contained in DTIME(n (log n)^sigma), with one sigma and one language.
**Stronger form.** There are sigma > 0 and L in coNTIME[n; floor(2 log n)] such that L is not in NTIME(n (log n)^sigma)
intersected with parity-TIME(n (log n)^sigma); in particular L is not in UTIME(n (log n)^sigma) (unambiguous time).

Lean: `P1Final.c1_closed` (sentence 1 with the guessing class), `P1Final.c1_ntime_closed` (both sentences),
`P1Final.c1u_closed` (stronger form), `P1Final.c1u_utime_closed` (stronger form with UTIME). Each has exactly the type of a
target in the Mathlib-only statement files `lean/C1Challenge/` (checked as Lean terms), and each depends only on the axioms
`propext`, `Classical.choice`, `Quot.sound`. Statements and their blind reads: `LEAN-STATEMENT.md`.

## What the statement does not say

- sigma is not known. The proof splits on a question nobody can answer now (whether characteristic 2 "has ports"); each case
  gives its own sigma and its own language L. The theorem is not effective, and L is built inside the proof.
- Multitape Turing machines only. Nothing about random-access machines, circuits, polynomial time, or P versus NP.
- "Not in DTIME" means: every deterministic machine for L exceeds the bound on some input. It is not "almost everywhere".
- The Lean machines have two-way tapes and take the guess as a prefix of the input; that they give the paper's classes is
  argued in words, not in Lean (`LEAN-STATEMENT.md`, section 4).

## How to check it

    cd lean
    sh scripts/get-upstream.sh   # openai/math@3344da5 and ZIB-IOL/lemmata@a2dd430; patches; sha256 of all 3,067 files
    lake exe cache get           # prebuilt Mathlib d13f23b (Lean 4.34.1, pinned in lean-toolchain)
    lake build                   # 3,068 modules; prints the four type checks and the axioms

Needs elan, git 2.27 or newer, `patch`, network access, about 20 GB of disk (Mathlib about 7 GB, the build folder 11 GB) and
32 GB of memory or more (we have not tried less). Our clean build (18 cores, `LEAN_NUM_THREADS=8`, empty build folder): 1,611 s;
one Lean process peaked at 22.5 GB resident memory. A GitHub Actions build on a standard runner (4 cores, 16 GB of memory,
14 GB of disk) is not realistic, so this repository has no CI workflow.

## The audit

- Three kernels: Lean's own kernel during the build; `leanchecker`, which replays every compiled module (all 746 of ours and
  all 2,321 of OpenAI's library and its dependency Lemmata; 0 failures); and `lean4lean`, an independent kernel, on the export
  of each theorem with its whole closure (83,903 to 84,109 declarations, exit 0).
- Clean rebuilds from an empty build folder: the audit of 25 November, and this project again on 26 November.
- A scan of all source files for `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, and the sha256 of every
  source file (`lean/CLOSURE-SHA256SUMS`, 3,067 files). Details and logs: `LEAN-AUDIT.md`, `logs/`.

## The public record

To our knowledge, the unconditional separations of linear nondeterministic from deterministic multitape time published before
this work have factors of iterated-logarithm type: DTIME(n) != NTIME(n) (Paul, Pippenger, Szemeredi and Trotter, FOCS 1983),
DTIME(n sqrt(log* n)) != NTIME(n sqrt(log* n)) (Santhanam, CCC 2001), and NTIME(n) not in DTIME(o(n (log* n)^{1/4})) as stated
by Chen and Wang (ECCC TR26-006, 2026). The theorem here has the factor (log n)^sigma, for some sigma > 0 that is not known.
The proof stands on tools from three OpenAI preprints of 24 November 2026 (EG, CL and T below, in `github.com/openai/math`) and
on OpenAI's Lean library, whose proofs are compiled and checked with ours. No human has refereed the proof. Searches for
earlier work (made by models; not a claim of priority): `NOVELTY.md`. Conditional separations of the same classes from
fine-grained hypotheses are due to Lingas (arXiv:2011.02428).

## Errata to the paper

The Lean work found two errors in the paper; neither affects the theorem (`ERRATA.md`). E1: check C12 must check every bit
from position L on (the paper says "after position L", which leaves one bit unchecked). E2: the paper does not justify the
length bound for the energy prefixes; one sentence repairs it. The paper files are unchanged.

## Files

- `lean/`: the Lake project (Lean 4.34.1, Mathlib `d13f23b`): our 746 Lean files, the statement files `lean/C1Challenge/`,
  `lean/Release.lean`, `lean/scripts/get-upstream.sh`, our two patches to OpenAI's library (`lean/patches/`), the lists of the
  fetched files (`lean/upstream/`), `lean/CLOSURE-SHA256SUMS`, and the licenses and notices (`lean/LICENSE`, `lean/NOTICE`).
- `LEAN-STATEMENT.md`: the Lean statements, the definitions in words, and the blind fidelity reads.
- `LEAN-AUDIT.md`: kernels, clean rebuilds, source scan, checksums. `logs/`: the build and audit logs.
- `ERRATA.md`: the two errata to the paper.
- `ntime-dtime-polylog.tex`, `ntime-dtime-polylog.pdf`: the paper.
- `STATEMENT.md`, `HYPOTHESES.md`, `CHECKS.md`, `NOVELTY.md`: as of 25 November 2026, each with a dated addendum at the end.
- `SHA256SUMS`: sha256 of every file.

## How the proof goes

The paper `ntime-dtime-polylog.pdf` gives the proof in words. The first version of this repository (25 November 2026)
proved the theorem from twelve stated inputs H1 to H12. The Lean proof assumes none of them, so the theorem at the top
of this page is unconditional.

### The constant and the separating language

- sigma = 1/4 if characteristic 2 has no ports, sigma = s/2 if it has ports, where s > 0 comes from constants that H8 asserts to
  exist. We do not know which case holds, so sigma is not effective.
- The separating language is the complement of matrix transposition TRANS (if characteristic 2 has no ports), or the complement of a
  padded language A'' built from a language A that witnesses the parity time hierarchy at time n^2 (if it has ports).

**Stronger form (Section 8 of the paper).** coNTIME[n; floor(2 log n)] is not contained in NTIME(n (log n)^sigma) intersected
with parity-TIME(n (log n)^sigma); in particular it is not contained in UTIME(n (log n)^sigma) (unambiguous time). The
complement-side form, NTIME[n; floor(2 log n)] not contained in UTIME(n (log n)^sigma), follows if characteristic 2 has ports
and is open otherwise.

All definitions are written out in full in `STATEMENT.md`.

### The twelve inputs of the first version (no longer assumed)

The Lean proof does not assume any of H1 to H12. Where the paper uses an input, the Lean proof uses a theorem of OpenAI's
Lean library or a lemma of our own (`HYPOTHESES.md`, addendum of 26 November). The table records what each input was. Its last
column is the state of OpenAI's Lean library as compared on 25 November, before our Lean proof existed.

Sources: OpenAI preprints in `github.com/openai/math` (folder `preprints/`): **EG** *Euclidean geometry in the asymptotic spectrum of
tensors*, **CL** *Circuit lower bounds for Hamiltonian cycle and the permanent*, **T** *The logarithmic exponent of integer
multiplication on tapes*. Lean names are in OpenAI's Lean library in the same repository (folder `lean/`, commit 3344da5), compared
at the level of statements on 25 November (the Lean proof now builds the parts of that library that it uses). Details and line numbers: `HYPOTHESES.md`. The two inputs in a characteristic-2 form
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

### What is new

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

### What is not claimed

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

## Credit

Research driven, orchestrated and reviewed by Jack Ryan. Claude by Anthropic, GPT 6.2 Astra by OpenAI, and Gemini 4 Neon by
Google collaborated in finding and writing the proofs.

Not peer reviewed. No professional mathematician has refereed this repository.

Who did what. The paper: Claude found the first version of the argument, wrote the paper and made the independent readings;
GPT-6.2 Astra wrote the repaired proof of the port case (Lemma P) and re-derived, blind, the no-ports case and the
nondeterministic Lemma A; Gemini 4 Neon looked for general reasons why the argument must fail (oracles, known upper bounds) and
proposed the unambiguous-time version. GPT-6.2 Sol (by OpenAI) ran literature searches and reference checks, drafted the
statement description and made a final check of the text of 25 November. The Lean proof: Claude agents wrote the statement files, the
plan and most of the proof files; GPT-6.2 Astra and GPT-6.2 Sol wrote further proof files, each compiled and type-checked against
a target written by a Claude agent; GPT-6.2 Astra and Gemini 4 Neon made the blind reads of the statements. OpenAI's Lean
library supplies the tools of its three preprints.
