# Searches for earlier work

Statements searched. **(A)** There is sigma > 0 with NTIME[n; O(log n) guess bits] not contained in DTIME(n (log n)^sigma) on
multitape Turing machines (so NTIME(n) not in DTIME(n (log n)^sigma)); also the weaker form "NTIME(n) not in DTIME(n g(n)) for some
g growing faster than log* n". **(B)** coNTIME[n; O(log n)] not contained in NTIME(n (log n)^sigma) intersected with
parity-TIME(n (log n)^sigma), in particular not in UTIME(n (log n)^sigma). **(C)** A dichotomy on "ports" (OpenAI, 24 November 2026)
applied to uniform time classes.

**Result: no earlier statement of (A), (B) or (C) was found.** This records searches; it is not a claim of priority. Under Weak
ETH, (A) is a short corollary of OpenAI's transposition lower bound, whose proof runs over the rationals (see "What is new" in
`README.md`).

## The searches (all on 25 November 2026, UTC)

| # | When | By | Covered |
|---|---|---|---|
| 1 | 06:56-07:15 | Claude (part of an adversarial reading) | web search; ECCC: all 49 November reports (TR26-291 to 343) by title; arXiv API (submitted since 25 Oct 2026: NTIME, DTIME, nondeterministic/deterministic time in cs.CC, linear time, ports, tensor network, time hierarchy, multitape); GitHub issues and pull requests (including cslib-community/cslib-frontier); Zenodo API; blogs |
| 2 | 07:15-07:34 | Claude (independent of search 1) | arXiv: all 528 cs.CC entries of 1 Oct to 24 Nov 2026 (title and abstract) plus all-category queries since 1 Sep 2026, and the cs.CC listing of 25 Nov; ECCC: all reports TR26-001 to 343 (full abstracts); GitHub (issues, pull requests, code in cslib-frontier, openai/math, formal-conjectures, OpenProblemsInNLA); Zenodo (16 queries); vibemathed.com dataset (1355 entries); hexagonmath.org (all works); Palomar registry (recent results); MathOverflow, cstheory and cs StackExchange (API, since 1 Sep 2026); four blogs; the OpenAI TeX and Lean sources (commit 3344da5); Anthropic sources; papers citing Paul-Pippenger-Szemeredi-Trotter 1983 and Santhanam 2001 (OpenAlex) |
| 3 | 07:53-07:58 | GPT-6.2 Sol | arXiv (25 Nov listing, targeted full-text checks); forward citations of the two classical papers and of the three OpenAI preprints; hexagonmath.org (indexed PDF full text, candidates opened); nilradical.ai; the Kourovka notebook (21st edition, full text); the Palomar registry (recent-results data); proofatlas.ai (advances, formalizations, open problems); vibemathed.com; Zenodo; GitHub (cslib-frontier issues and pull requests); MathOverflow, Math StackExchange, CSTheory; ECCC reports of 18-25 Nov 2026 (PDFs opened). Also statement (B) |
| 4 | 08:19-08:24 | GPT-6.2 Sol | reference check of every work cited in the paper's prior-work section (primary sources opened; see the paper's bibliography) |

A full-text reading of Anthropic's *VP != VNP over every field* (hexagonmath.org 2611.00954v1, 23 November 2026) was made
separately: it uses a different dichotomy (contracting versus flat prices over Mat_mu(F_2)), contains no statement about multitape
Turing time classes, no transposition bound and no parity-time speed-up; (A) and (B) are not in it, and no short derivation of
them from it was found.

## Closest work found

| Work | What it gives | Relation |
|---|---|---|
| A. Lingas, *Consequences of APSP, triangle detection, and 3SUM hardness for separation between determinism and non-determinism*, arXiv:2011.02428 v5 (2021); Procedia Computer Science 195 (2021) 163-171 | the same classes NDTIME(c log n, n) on multitape machines; separations **conditional** on fine-grained hypotheses (triangle detection: not in DTIME(n^{delta'/2}) for delta' < omega; low-dimensional orthogonal vectors: not in DTIME(n^{2-eps}); APSP, 3SUM, clique and ETH forms) | closest. Some premises were reported false in 2026 preprints (ETH; polynomial-range 3SUM and APSP); the triangle, OV and large-weight forms are, as far as we know, open. Where they hold, his bounds are much stronger. Ours assume no fine-grained hypothesis |
| W. Paul, N. Pippenger, E. Szemeredi, W. Trotter, FOCS 1983, 429-438 | DTIME(n) != NTIME(n) on multitape machines | the classical separation |
| R. Santhanam, CCC 2001, 286-294 | DTIME(n sqrt(log* n)) != NTIME(n sqrt(log* n)) (same bound on both sides) | iterated-logarithm type |
| L. Chen, Y. Wang, ECCC TR26-006 (2026), footnote 3 | states NTIME(n) not in DTIME(o(n (log* n)^{1/4})) as the best known, citing Paul-Pippenger-Szemeredi-Trotter and an answer of R. Williams on MathOverflow (question 4953, 16 Dec 2009) | the report itself separates RAMs from multitape machines with short random oracles |
| Strassle and Subercaseaux, arXiv:2611.11832 (9 Nov 2026) | NTIME[t] in DTIME[2^{O(t/sqrt(log t))}] | an upper bound on deterministic simulation; consistent |
| Balasubramanian and Majumdar, arXiv:2611.27814 (v2, 24 Nov 2026) | pushdown reachability needs N^{2-eps} time on multitape machines (via the time hierarchy) | cites Paul-Pippenger-Szemeredi-Trotter as the state of the art for NTIME versus DTIME; no linear-time logarithmic-guess verifier for its hard instances was found, so no NTIME consequence |
| R. Williams, Computational Complexity 15 (2006), Thm 1.6 | NTIBI[n, n^eps] not in DTISP[n^{c_eps}, n^{o(1)}] (also multitape) | time-space bound: restricts the space of the deterministic machine |
| a draft in cslib-frontier (pull request 7507, 22 Nov 2026) | NTIME[t] in DSPACE[t/sqrt(log t)], NTIME(n) != DSPACE(n), also for parity time | separation from space, not from deterministic time |
| Y. Tal, ECCC TR26-331 (22 Nov 2026) | sorting in o(N log N) on multitape machines; a transposition upper bound from the September 2026 OpenAI multiplication preprint | consistency only |
| D. Harvey, J. van der Hoeven, arXiv:2503.22848 (FOCS 2025), Cor. 6.2, with T's multiplier n (log n)^{1/2+o(1)} | TRANS in DTIME(n (log n)^{1/2+o(1)}) | shows that Case 1 (Omega(n sqrt(log n)) for TRANS) is tight up to (log n)^{o(1)} |
| OpenAI, T (24 Nov 2026) and its Lean library | under variable-count Weak ETH: Omega(n sqrt(log n)) for multitape multiplication and transposition, also for sound nondeterministic multiplication machines (Lean) | under Weak ETH, (A) follows from T in a few lines; our Case 1 is that argument with Weak ETH replaced by "characteristic 2 has no ports" |
| OpenAI, CL (24 Nov 2026), introduction | the ports dichotomy, for circuits ("either outcome gives a circuit lower bound") | the template; we found it applied to uniform time classes nowhere |

## Consistency checks against known results

- (A) does not give NTIME(n) not in DTIME(n^{1+eps}): Case 1 is capped by the upper bound for TRANS, and Case 2 gains only a
  polylogarithmic factor.
- The proof does not relativize: for oracle machines with a query tape erased after each query, there is an oracle with deterministic
  and nondeterministic linear time equal (Hemmerling, Information and Computation 209 (2011), Proposition 15); the proof uses tape
  locality.
- No unconditional NTIME versus coNTIME separation follows (paper, Section 8).
- On random-access machines TRANS is in linear time, so Case 1 has no RAM analogue, as it should.
