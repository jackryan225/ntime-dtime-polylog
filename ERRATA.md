# Errata to the first version of the paper (found by the Lean work, 25 November 2026)

These are errors of the first version of the paper (25 November 2026). **Both are corrected in the paper of 26 November 2026**
(Section 9 of the paper lists them). This file keeps the record. Line numbers below refer to the first version. **Neither erratum
affects the theorem.** The Lean proof uses the corrected forms.

## E1. Check C12: one bit is not checked

Place: Section 7, subsection "The witness and its checks", item C12 (`ntime-dtime-polylog.tex` line 1050).

The paper says: every bit of S3 "after position" Omega(y_max) + (sum of the widths at y_max) is 0. With positions counted from 0,
"after position L" leaves the bit at position L unchecked. Correct form: **every bit at a position i with L <= i < |S3| is 0**,
where L = Omega(y_max) + (sum of the widths at y_max). Found by three independent readings of Section 7 made for the Lean work
(Claude, and blind, GPT-6.2 Astra and Gemini 4 Neon).

## E2. Energy prefixes: the length bound is not justified

Place: Section 7, the paragraph that starts "Every field has a fixed length: addresses and prefixes lambda + O(log lambda)
bits" (line 842), and its uses in Lemma Space ("both energy prefixes ... O(d_l lambda) bits") and in the existence part of the
uniqueness lemma ("the true ... energy prefixes").

The paper gives a reason for the lengths of widths and of the integers of a term index only. For the energy prefixes E_k(y)
(the sums, over all bases y' <= y, of the energies of the motifs anchored there; each energy is an integer combination, with
fixed coefficients, of squares of supply widths) no bound is stated. Repair, one sentence: a level has at most P_0 = O_M(t)
positions, a position anchors at most 2 d_l motifs, and every supply width is at most C_2^T (W_0 + 1) = lambda^{O(1)}; so
0 <= E_k(y) <= 2^{lambda + O(log lambda)}, and a field of lambda + O(log lambda) bits holds every energy prefix for n >= n_M
(the threshold of Lemma Space). If a coefficient can be negative, the stored number is the cleared-denominator form with
non-negative coefficients (the Lean proof stores a natural number). Found when a Lean step failed: the stored energy sums were
known only modulo a power of two. In Lean the fit is a separate lemma for long inputs.

## Not an erratum

The Lean proof checks C7 at both kinds of level (shrinking and refresh). This is what the paper already says; an earlier plan of
the Lean work had it wrong.
