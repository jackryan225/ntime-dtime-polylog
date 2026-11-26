# Checks of the time separation and of its stronger form

All on 25 November 2026 (UTC). "Blind" means that the checker received the bare statement (and the OpenAI sources), not our proof.
Models: Claude (Anthropic: Claude Opus 5.5 agents), GPT-6.2 Astra and GPT-6.2 Sol (OpenAI), Gemini 4 Neon (Google).
**Nothing below is a machine check of the theorem: the proof is a paper proof, not machine-checked.** No professional
mathematician has refereed it.

## A. The main theorem

| # | Check | Model | Kind | Result |
|---|---|---|---|---|
| 1 | first complete version of the argument (dichotomy on ports in characteristic 2) | Claude | author | proved on paper; its port case had repairable errors (see 9) |
| 2 | adversarial review of that version | Claude | review | no gap found; one fix: the Benes settings and lane decompositions must be canonical (computed, not guessed) |
| 3 | no-ports case, blind | Claude | blind | proved; no step fails in characteristic 2 (the scalar in the entropy lemma is 1, nothing cancels modulo 2, the count of a deterministic machine is 0 or 1) |
| 4 | the pinning step of the no-ports case written out | Claude | review | holds; final contents must be summed, never pinned |
| 5 | no-ports case, blind, from the OpenAI sources only | GPT-6.2 Astra | blind | true; an independent proof (it re-proves the paired-terminal entropy step) |
| 6 | port case (Lemma P) | GPT-6.2 Astra | author (had a sketch) | proved, with the exponent s < 1/(1 + 2 log C_2); repaired the sketch (three-block interval tables, canonical Benes routing, degree padding, panel locality) |
| 7 | line-by-line check of Lemma P | Claude | check | correct on all five items checked; four minor gaps, all closed in the paper |
| 8 | port case, blind | Claude | blind attempt, then a check of the construction | blind: neither proved nor refuted, but isolated the missing step (how to arrange the computation so that the compressor's lanes are identically wired and equally loaded); then, shown Astra's construction: that step holds by it |
| 9 | adversarial reading of the whole argument, with attempts to find general reasons why it must fail | Claude, with GPT-6.2 Astra and Gemini 4 Neon | adversarial | no fatal flaw; seven repairs to an earlier write-up (tag rule, degree regularization, zero padding, head offsets, record bookkeeping), all built into the paper; the general objections (oracles, tightness, known upper bounds) do not apply |
| 10 | ports in characteristic 2 imply ports over F_2 with the parameters in F_2 | Claude | check | holds (EG `lem:comparison` read line by line) |
| 11 | the compressor theorem in OpenAI's Lean library (read, not built) | Claude | audit | `Compression.exists_iterated_compression` proves the bounds of H8 for OpenAI's own construction, for every field with `HasWireExpanders` (not literally H8 with the scope used in the paper) |
| 12 | an explicit unconditional constant by this method? | GPT-6.2 Astra | obstruction | no: a black-box barrier for the method |
| 13 | independent reading of the whole paper (before the final text), without the earlier checks | Claude | independent read | **ready as a conditional paper proof**; no gap in the paper's own steps; H1-H12 match the cited source lines; consistency checks against known results passed; text corrections listed, all applied in the final text |
| 14 | full-text comparison with Anthropic's *VP != VNP over every field* (hexagonmath.org 2611.00954) | Claude | priority check | the results are not in it, and no short derivation from it was found |
| 15 | OpenAI's Lean rules for the greedy colours and tag offsets | Claude (with small Lean proofs) | Lean reading | the Lean scans read later neighbours as 0; the paper's checks were rewritten to follow them exactly |
| 16 | final consistency of the release text (corrections, the uniqueness induction for the new colour and offset rules, the new section) | Claude | check | done; LaTeX references, citations and environments consistent; the LaTeX source was later compiled with tectonic: no error, no undefined reference or citation |
| 17 | release check of the final text (mathematics of the changed parts, consistency of all files, hygiene, LaTeX by reading) | GPT-6.2 Sol | check | 15 points: reserved slots at the two ends of the state chain and the far ends of owner links in check C4; the scope of H8 for the fixed choices (now stated in H8; the colour, offset, payload-split and tie rules match OpenAI's Lean rules); a sorting cost in the batched-lookup lemma; computable guess budgets; integer guess budgets; the choice of the hierarchy language in Lemma B; wording of limits, prior work and provenance. Addressed. A second and a third check of the fixes (also GPT-6.2 Sol) raised further points of precision and three small gaps in unchanged parts (the parity-hierarchy simulator on invalid transcripts, the cost bound of check C13 on dishonest witnesses, a too general form of Lemma P in the abstract); these were corrected; a fourth check found six remaining points of precision; a fifth check confirmed their correction except three wording points, which were then corrected without a further check |

## B. The stronger form (coNTIME[n; 2 log n] not in NTIME cap parity-TIME(n (log n)^sigma), hence not in UTIME)

| # | Check | Model | Kind | Result |
|---|---|---|---|---|
| 18 | the idea of an unambiguous-time version | Gemini 4 Neon | idea | lead |
| 19 | proof (Lemma A over the algebraic closure of F_2, Lemma B for parity machines) | Claude | author | proved on paper |
| 20 | Lemma A, blind | GPT-6.2 Astra | blind | holds for every nondeterministic machine; F_2 suffices by a random specialization of the weights; the parity version is false as stated |
| 21 | independent reading | Claude | independent read | correct relative to H1-H12; the route over the algebraic closure would need H2 and H5 over that field, which the specialization of 20 avoids |
| 22 | line-by-line check of the specialization and of the paper's Section 8 | Claude | check | correct; Section 8 uses H1-H12 exactly (see also 17) |

## C. Searches for earlier work

Three independent searches and a reference check (`NOVELTY.md`): no earlier statement found.

## C2. Second checks of the three weakest inputs (25 November 2026, after the release read)

Each check was run blind: the model got the bare statement (and, where noted, the source files), not our proof.

| # | input | model | kind | result |
|---|---|---|---|---|
| 23 | H4 in characteristic 2 (T's geometric lemma, transferred) | Gemini 4 Neon | blind, bare statement | true. A complete proof with an explicit expander. Parts (1) and (2) use only the metric axioms, rescaling and H3; part (3) uses CAT(0) and completeness. So the transfer needs exactly that X_2 is a class of complete CAT(0) spaces, closed under rescaling, without ports |
| 24 | H4 (within the whole Case 1 statement) | GPT-6.2 Astra | blind, bare statement + T, CL, EG sources | true. Independent proof; the entropy inequality was re-proved over F_2 |
| 25 | H1(d) in characteristic 2 | Gemini 4 Neon | blind, bare statement | true, gamma' <= 48 D gamma. The argument uses only the metric (no characteristic) |
| 26 | H1(d) in characteristic 2 | GPT-6.2 Astra | blind, bare statement | true, gamma' = 4 q max{3, 12 gamma}; an independent short proof |
| 27 | H9-H11 as used by Lemma locality (EG text) | GPT-6.2 Astra | blind, bare statement + EG sources | holds; read radii 2-3 (records, widths, kernels), 3-5 (far slot numbers), refresh 0-1, all within the paper's 3/6/7/1; only the layout bit and the greedy scans are global |
| 28 | H9-H11 against OpenAI's Lean construction (commit 3344da5) | Claude | independent read, datum by datum, plus a numpy re-implementation of one Lean shrink substep | holds: every datum is local; the only global data are the layout bit and the two greedy scans (the paper's C5/C6 follow the Lean scans exactly); radii 3/6/7/1 and the uniqueness induction survive. Fidelity item: Lean uses a mixed-radix lane-0 key instead of EG's xor-relative identifiers; no radius changes |

## D. Machine checking

None for the theorem. Formalization in Lean 4 has started but is not part of this release. H4 and H1(d) now have two blind second checks each (C2 above). The compressor construction H9-H11 now has a blind check (27) and an
independent read against OpenAI's Lean (28).


## E. Machine checking (added 26 November 2026)

Section D above says "None for the theorem". That was true for the paper proof of 25 November. Since then (all UTC, 25 November 2026 unless
stated):

| # | Check | By | Result |
|---|---|---|---|
| 29 | Lean 4 proof of `c1`, `c1_ntime`, `c1u`, `c1u_utime` (the statements of `LEAN-STATEMENT.md`) with no hypothesis | Claude agents, with parts written by GPT-6.2 Astra and GPT-6.2 Sol; every delivered file compiled and type-checked against our target | proved; axioms `propext`, `Classical.choice`, `Quot.sound` only |
| 30 | fidelity of the statement of `c1` to the paper's main theorem | a Claude agent; blind: GPT-6.2 Astra, Gemini 4 Neon | the same conclusion; Lean is stronger (no H1 to H12); no difference makes it weaker |
| 31 | fidelity of `c1_ntime` and of `c1u` | blind: GPT-6.2 Astra, Gemini 4 Neon (one call each per statement) | faithful up to harmless differences (listed in `LEAN-STATEMENT.md`) |
| 32 | second kernel: leanchecker replay of every module of the build (746 of ours, 2,321 of OpenAI's library and its Lemmata dependency) | build machine | 0 failures |
| 33 | third kernel: lean4lean on the export of each theorem | build machine | 83,903 / 84,109 / 84,016 / 84,028 declarations checked, exit 0 |
| 34 | clean rebuild from an empty build folder, source scan, sha256 of every source file | build machine | passed (25 November); the release project passed again on 26 November (`LEAN-AUDIT.md`) |
| 35 | errata found by the Lean work | Claude, GPT-6.2 Astra, Gemini 4 Neon | two (`ERRATA.md`); the theorem is not affected |

Still not done: no human has read the Lean statement files, the proof or the paper. The equivalence of the Lean machine model
with the paper's is argued in words, not in Lean.
