# The time separation: full statement, every definition, and what it rests on

This document describes the result of the paper `ntime-dtime-polylog.tex` (version of 25 November 2026) completely and without
reference to conventions. Section numbers "paper, Section k" refer to that file (1 Introduction, 2 Prior work, 3 Models and classes,
4 The inputs H1-H12, 5 Case 1, 6 Case 2, 7 Proof of the main theorem, 8 Nondeterministic and unambiguous machines, 9 Remarks). This text was checked line by line against
the paper.

## 1. The theorem

$$
(\mathrm{H1}\wedge\mathrm{H2}\wedge\cdots\wedge\mathrm{H12})\ \Longrightarrow\ \exists\,\sigma>0:\quad
\mathrm{NTIME}[n;\lfloor 2\log_2 n\rfloor]\ \not\subseteq\ \mathrm{DTIME}\big(n(\log_2 n)^{\sigma}\big).
$$

So there is ONE language $L$, decided in linear time by a verifier that reads $\lfloor 2\log_2 n\rfloor$ guess bits, such that NO
deterministic multitape Turing machine (with any fixed number of tapes) decides $L$ in time $O(n(\log n)^{\sigma})$. Consequently
$\mathrm{NTIME}(n)\not\subseteq\mathrm{DTIME}(n(\log n)^{\sigma})$. The theorem does not assume Weak ETH or any other complexity
hypothesis; in the paper version of 25 November 2026, its premises are the twelve inputs H1 to H12 (Section 3 below), which restate results of three OpenAI preprints of
24 November 2026. Since 26 November 2026, the main theorem and its stronger form have also been machine-checked unconditionally in Lean 4 (compiling OpenAI's Lean library inside the same kernel closure to discharge H1 to H12; see `README.md`, `LEAN-STATEMENT.md`, and `LEAN-AUDIT.md`). A stronger form is in Section 5 below (paper, Section 8).

## 2. Every definition

**Machine model** (paper, Section 3.1). A $k$-tape machine ($k\ge1$ fixed for the machine) has $k$ tapes with cells
$0,1,2,\dots$, one head per tape, a finite control and a finite tape alphabet containing a blank and a left endmarker $\vdash$. At
the start every tape holds $\vdash$ in cell 0 and blanks elsewhere, except tape 1, which holds the input $x\in\{0,1\}^n$ in cells
$1,\dots,n$; all heads are on cell 0. One step (transition) reads the state and the $k$ scanned symbols, writes one symbol on each
tape, moves each head by $-1$, $0$ or $+1$, and changes the state. By a syntactic convention no transition writes $\vdash$ outside
cell 0, overwrites $\vdash$, or moves left from $\vdash$ (every machine can be put in this form with a constant factor in time and
the same number of accepting computations), so no head ever reaches a negative cell. There is no read-only restriction on any tape.
A machine is deterministic if it has at most one transition for each state and scanned tuple; nondeterministic (NTM) if it has
finitely many. A computation is a finite sequence of configurations, each obtained from the previous one by one transition, ending in
a halting state; it accepts if that state is accepting. $\#\mathrm{acc}(M,x)$ is the number of accepting computations. A machine
runs in time $f$ if on every input of length $n$ EVERY computation (accepting or not) halts within $\max(f(n),1)$ steps.

**Limited nondeterminism** (paper, Definition 3.1). In guess budgets $\log n$ means $\log\max(n,2)$. $\mathrm{NTIME}[f;g]$ is the class of languages $A$ for which there are a
deterministic multitape machine $V$ (the verifier) and a constant $c>0$ such that, for every $x\in\{0,1\}^n$ on tape 1 and EVERY
$y\in\{0,1\}^{g(n)}$ written on tape 2, $V$ halts within $c\max(f(n),1)$ steps, and
$x\in A \iff \exists y\in\{0,1\}^{g(n)}:\ V(x,y)=1$. The guess is supplied whole on tape 2 (not guessed step by step); the time
bound holds for every guess. In the theorem $f(n)=n$ and $g(n)=\lfloor 2\log_2 n\rfloor$. $\mathrm{coNTIME}[f;g]$ is the same with
"for all $y$" in place of "for some $y$", equivalently the complements of the languages in $\mathrm{NTIME}[f;g]$.

**Unlimited nondeterminism and counting classes** (paper, Definition 3.1). $\mathrm{NTIME}(f)$: languages $A$ for which some NTM
$M$ runs in time $O(f)$ and $x\in A\iff\#\mathrm{acc}(M,x)\ge1$. $\oplus\mathrm{TIME}(f)$ (parity time): the same with
"$\#\mathrm{acc}(M,x)$ is odd". $\mathrm{UTIME}(f)$ (unambiguous time): some NTM $M$ runs in time $O(f)$, has
$\#\mathrm{acc}(M,x)\le1$ on EVERY input, and $x\in A\iff\#\mathrm{acc}(M,x)=1$. If $g=O(f)$ and a machine that
reads its input $x$ can compute $g(|x|)$ within $O(f(|x|))$ steps (true for $f(n)=n$ and every budget used here),
$\mathrm{NTIME}[f;g]\subseteq\mathrm{NTIME}(f)$ (write the guess, one binary branching per bit, then run $V$); and
$\mathrm{DTIME}(f)\subseteq\mathrm{UTIME}(f)\subseteq\mathrm{NTIME}(f)\cap\oplus\mathrm{TIME}(f)$.

**Deterministic time.** $\mathrm{DTIME}(h)$: languages decided by a deterministic multitape machine (any fixed number of tapes)
that halts on every input of length $n$ within $C\max(h(n),1)$ steps for some constant $C$. Here $h(n)=n(\log_2 n)^{\sigma}$. The separation says that every such machine fails on
infinitely many lengths. $\mathrm{DTIME}$ is closed under complement, so $\mathrm{NTIME}[f;g]\subseteq\mathrm{DTIME}(h)$ implies
$\mathrm{coNTIME}[f;g]\subseteq\mathrm{DTIME}(h)$.

**Small lengths.** In guess budgets the paper reads $\log n$ as $\log\max(n,2)$, so the budget at $n<2$ is
$\lfloor2\log 2\rfloor=2$; time bounds at the finitely many small lengths are constants. This does not affect the separation.

**The exponent.** $\sigma=1/4$ if characteristic 2 has no ports (then every $\sigma<1/2$ works). If it has ports,
$\sigma=s/2$ with
$$s=2^{-\lceil\log_2(64(1+b_0+\lceil\log_2 C_2\rceil))\rceil},$$
where $b_0$ and $C_2$ are constants that H8 (over $\mathbb F_2$) asserts to exist (then every $\sigma<s$ works). Since nobody knows
which case holds, and $b_0$, $C_2$ are not given explicitly, $\sigma$ is not effective. "Ports" is defined in H1 below.

**Case 1 witness.** $\mathrm{TRANS}$ is the set of strings $XY$ of length $2N^2$ ($N\ge1$) where $X,Y$ are binary $N\times N$
matrices written row by row without separators and $Y=X^{T}$. All other lengths are outside $\mathrm{TRANS}$. The separating
language is the complement $\overline{\mathrm{TRANS}}$ (all binary words not in $\mathrm{TRANS}$, malformed lengths included). Its
verifier accepts malformed lengths for every guess; at length $2N^2$ it reads the guess as a pair $(i,k)$ of
$\lceil\log_2N\rceil$-bit numbers, rejects if $i\ge N$ or $k\ge N$, fetches the bits at positions $iN+k$ and $N^2+kN+i$ and accepts
iff they differ. This uses $2\lceil\log_2N\rceil\le\lfloor\log_2n\rfloor+1$ guess bits and $O(n)$ steps.

**Case 2 witness.** Let $A$ be a language that witnesses the parity time hierarchy at time $n^2$ (paper, Theorem "Parity time
hierarchy": $A\in\oplus\mathrm{TIME}(n^2)$ and $A\notin\oplus\mathrm{TIME}(t')$ for every $t'=o(n^2)$), and let $V,m,k$ be given for
$A$ by Lemma P (paper, Section 6). With
$t=n^2$, $\lambda=\lceil\log_2t\rceil$, $p=\lfloor\log_2\lambda\rfloor$, $T=\lfloor sp\rfloor$, $m=(p+1)^6\lceil t/2^{T}\rceil$,
$k=\lceil\log_2t\rceil$, $R(n)=(p+1)m(n)$:
$$A''=\{\,1^n0\,x\,u\,0^{R(n)}:\ n\ge n_M,\ |x|=n,\ |u|=m(n),\ V(x,u,\gamma)=1\text{ for all }\gamma\in\{0,1\}^{k(n)}\,\}.$$
The separating language is $\overline{A''}$. Its bit-level definition is fixed once the finite data of the proof are fixed (the
parity machine for $A$, the constant $n_M$, the compressor data of H8).

## 3. The twelve inputs H1 to H12

Sources: three OpenAI preprints of 24 November 2026 in the public repository `github.com/openai/math`, folder `preprints/`:
**EG** *Euclidean geometry in the asymptotic spectrum of tensors*, **CL** *Circuit lower bounds for Hamiltonian cycle and the
permanent*, **T** *The logarithmic exponent of integer multiplication on tapes*. Line numbers refer to the files in their `build/`
folders. Lean names refer to OpenAI's Lean library (same repository, folder `lean/`, commit 3344da5), compared at the level of
statements by reading; nobody here built them. Table form: `HYPOTHESES.md`.

Background words (EG `prices.tex` l.8-85). A *party* is a site holding one factor space of a tensor; a *restriction* applies one
linear map at each party. A *spectral point* over a field assigns to each tensor (over that field, on a fixed finite set of parties) a
nonnegative real number; it is normalized, additive under direct sum, multiplicative under tensor product (factors grouped by party)
and monotone under restriction. The equality wire of width $b$ between two parties is $\sum_{i<2^b}e_i\otimes e_i$. A *spectral
space* carries compatible prices on all finite placements, a one-bit wire costing the distance of its endpoints. A Hadamard space is
a complete geodesic metric space with the CAT(0) comparison property.

- **H1 (ports; EG `port-graphs.tex` l.11-55; EXACT).** For a symmetric stochastic matrix $G$ on a finite set $V$ and points $x_i$ of a
  spectral space over a field $\mathbb F$, put $\mathcal E_G(x)=|V|^{-1}\sum_{i,j}G_{ij}d(x_i,x_j)^2$ and
  $\mathcal V(x)=|V|^{-2}\sum_{i,j}d(x_i,x_j)^2$. (a) $\mathbb F$ *has ports* if there are a family of regular symmetric multigraphs
  of unbounded order and bounded degree and a constant $\gamma$ with $\mathcal V(x)\le\gamma\,\mathcal E_G(x)$ for every graph of the
  family ($G$ its normalized adjacency matrix, a diagonal arc keeping the walk in place) and every assignment $x$ into a spectral space
  over $\mathbb F$. (b) This depends only on the characteristic of $\mathbb F$. (c) One may test finite spectral points or complete
  CAT(0) spectral spaces. (d) With ports, the family may be taken connected, loop-free, of one power-of-two degree and of arbitrarily
  large power-of-two orders. "Characteristic 2 has ports" means $\mathbb F_2$ has ports. Lean: the dyadic form (a)+(d) is the
  definition `HasWireExpanders`; (c) is used as `exists_catZero_completion`; (b) and (d) in characteristic 2 are paper only.
- **H2 (the class $\mathcal X_2$; CL `prices.tex` l.107-113, l.129-149, T `graphs.tex` l.14-50; EXACT against CL).**
  $\mathcal X_2$ is the class of Hadamard spaces carrying compatible spectral prices for tensors over a field of characteristic 2 on all
  finite subsets, with distance equal to the price of a one-bit wire; it depends only on the characteristic. A class *admits ports* if
  regular multigraphs of one positive degree and unbounded orders satisfy one inequality
  $\mathbb E\,d(x_U,x_V)^2\le C\,\mathbb E\,d(x_I,x_J)^2$ ($U,V$ independent uniform vertices, $(I,J)$ a uniform directed arc) for all
  placements in all members; for $\mathcal X_\chi$ this is exactly ports in the sense of H1. Price comparison: if the vertices of a
  tensor network over $\mathbb F_2$ with edge widths $q_e$ are placed at points $x_u$ of a member of $\mathcal X_2$, every product of
  equality wires obtained from the network by local linear maps has price at most $\sum_{e=uv}q_e\,d(x_u,x_v)$, and $r$ copies cost
  $r$ times this. Lean: the comparison is `wire_cost_le` (every field); the class is paper only.
- **H3 (CL `thm:loggraph`, `entropy.tex` l.54-66; EXACT, field-free).** Let $P$ be the walk on a $d$-regular multigraph ($d\ge1$) with
  $n\ge2$ vertices and uniform stationary law $\pi$. If $\mathcal V_\pi(x)\le\beta\,\mathcal E_P(x)$ for every placement in every member of a
  class of Hadamard spaces without ports, then $\beta\ge c\log n/\log(d+1)$ for an absolute $c>0$. Lean: paper only.
- **H4 (T `lem:geometry` in characteristic 2, `lower.tex` l.42-116; TRANSFER).** Assume characteristic 2 has no ports. Let a
  multigraph have $P_0$ vertices, maximum degree $D$ and edge widths at most $Db$; let $P$ be the least power of two $\ge P_0$. For
  all large $P_0$ there are a placement $u\mapsto x_u$ in some $X\in\mathcal X_2$ and a point $o\in X$ with, for $S=\sum_{e=uv}q_e\,
  d(x_u,x_v)$ and constants depending only on $D$: $S\le C_D\,bP/\sqrt{\log P}$;
  $\mathbb E_{a\in A,t\in B}(d(x_a,x_t)-1)^2\le C_DP/(N\log P)$ for any two lists $A,B$ of $N$ vertices, distinct within each list;
  and $\sum_vh_v\,d(x_v,o)\le\frac1{\sqrt2}\sum_vh_v+C_D(\frac{P}{\log P}\sum_vh_v^2)^{1/2}$ for all weights $h_v\ge0$. The
  placement comes before the lists and weights. Change from the source: T assumes Weak ETH, which it uses only to obtain a class of
  Hadamard spaces without ports (l.70-73); we obtain $\mathcal X_2$ without ports from "characteristic 2 has no ports" and H1(c). The
  rest of T's proof (expander padding, scalar Poincare inequality, CAT(0) barycenter, Cauchy-Schwarz) is field-free. Lean: paper only
  (`padded_graph_geometry` is characteristic 0).
- **H5 (T `lem:entropy` over $\mathbb F_2$, `lower.tex` l.130-202; TRANSFER).** Let a tensor network over $\mathbb F_2$ have pairs of
  vertices $(a_j,t_j)$, $1\le j\le L$, and let $W$ be a random binary vector of length $L$. Suppose that for each $w$ in the support of
  $W$, pins $C_v(w)$ at the vertices make the contracted tensor equal to $\bigotimes_j((e_{w_j})_{a_j}\otimes(e_{w_j})_{t_j})$. Then
  for every placement in $X\in\mathcal X_2$, every $o\in X$ and every order of the coordinates,
  $\sum_jH(W_j\mid W_1,\dots,W_{j-1})\,d(x_{a_j},x_{t_j})\le S+\sum_vH(C_v(W))\,d(o,x_v)$. Change from the source: "over the
  rationals" and "nonzero scalar multiple" become "over $\mathbb F_2$" and "equal to". Lean: `paired_entropy_at_placement` and
  `paired_entropy` are stated for every field; $K=\mathbb F_2$ gives H5.
- **H6 (EG `thm:conversion`, `compressor.tex` l.16-63; EXACT; summary, full text in the paper, Section 4).** For a fixed set of parties, demand edges $D$ and a connected spanning
  multigraph $S$ of supply edges with positive rational masses, if every spectral point satisfies
  $\sum_{D}p_ed_e^2\le H\sum_Sq_ed_e^2$, then for every $H'>H$ and all demand widths $b$ there is an exact sum identity
  $W_D(b)=\sum_\alpha(\bigotimes_vL_{v,\alpha})W_S(c_\alpha)$ with $\|c_\alpha\|_q^2\le H'\|b\|_p^2+O(1)$, with finitely many parameters
  solving fixed integer equations in the field, indices of $O(1)$ integers of size $O(M+1)$, and entries computable in polynomial
  time. Lean: `MotifConversion.exists_conversion` (every field).
- **H7 (EG `compressor.tex` l.267-312; EXACT; summary).** Networks of the stated form: a base digraph with $d$ in- and $d$ out-arcs per vertex
  ($d$ a power of two), lanes in a binary vector space, a displacement per base arc, positions (base vertex, lane), actual arcs of
  integer widths, energy $\mathcal L=\sum b_e^2/p$; and the exact identity of one substep, in which each whole old vertex factor goes
  to one new position. Lean: definitions only; paper only.
- **H8 (EG `thm:compressor`, `compressor.tex` l.314-340 with l.524-527 and l.548-551; EXACT; summary).** If $\mathbb F$ has ports there are
  a power-of-two degree $d_0$, an integer $b_0\ge1$, a constant $C_2\ge2$ and finitely many templates such that every network of the
  stated form with $P_0$ positions of degree $d_0$, maximum width $W_0$ and at least $Tb_0$ lane coordinates has an exact expansion by
  $T$ blocks of local identities with final width $\sum b_e\le\sqrt{\mathcal L_T}\le2^{-T}(\sqrt{\mathcal L_0}+O(P_0))$, all fields of
  length $\le C_2^T(W_0+1)$, at most $C_2^T$ occurrences per final position, one parameter solution in $\mathbb F$; each block is
  $s_0$ shrinking substeps and one refresh, with $P_0/\kappa_0^i$ positions at block $i$ ($\kappa_0>2$); and each final vertex sums only
  its own hidden indices. Scope: all of this holds for every proper colouring, every tag offsets satisfying the exclusion conditions
  of H9, every as-even-as-possible payload split and either tie rule of the layout (EG's proof uses only these properties). Lean:
  `Compression.exists_iterated_compression` under `HasWireExpanders` (every field); over $\mathbb F_2$ its hypothesis needs H1(d) in
  characteristic 2 (paper only). That Lean theorem proves the bounds for OpenAI's own construction; it is not literally H8 with this
  scope.
- **H9-H12 (EG `compressor-appendix.tex` l.9-105 and `compressor.tex` l.344-445, 447-509, 561-666; EXACT; summary).** The constructions inside
  H8: the packing of a shrinking substep (greedy colouring with $2d+1$ colours, lane split, bundles of thick-thick wires, tag offsets
  $\phi_x$ with $\phi_x\notin\tau_e^{\rm tag}+L_x$ and $\phi_x+\phi_y\notin\tau_e^{\rm tag}+L_x+L_y$ at every incidence,
  $J>2d((d+1)+(d+1)^2)$, role counts, slot identifiers), the shrinking substep (six-party motifs, two supply groups, one global layout
  chosen by energy, $m_e=\lfloor pq_e/p'\rfloor$ parallel surviving arcs, EG `compressor.tex` l.410), the refresh substep (port blocks, external wires, port-graph
  ties), and the descriptors (fixed-length term encodings, layout rule, identifiers). The paper uses only the constructions, not the
  RAM of H12. Lean: construction files exist but their match with the text is not checked: paper only. The paper's colour and offset
  rules follow OpenAI's Lean scans `orderedColor` and `orderedTagOffsets` exactly (a neighbour of larger address is read as 0).

Case 1 uses H1(a)-(c), H2, H3, H4, H5; Case 2 uses H1(a), (b), (d), H6-H12.

## 4. The proof in twenty lines

1. Split on whether $\mathbb F_2$ has ports (by H1(b), whether characteristic 2 has ports). Exactly one holds.
2. **Case 1 (no ports).** H1-H3 make $\mathcal X_2$ a class without ports; H4 gives a placement with short edges and terminals at
   distance about 1; H5 charges entropy to paired terminals. Together: a tensor network over $\mathbb F_2$ that, with the rows of $X$
   pinned, outputs exactly the basis vector of $X^T$ on a $2^{-\rho N^2}$ fraction of all $X$ ($\rho<1-1/\sqrt2$) needs
   $\Omega(N\sqrt{\log N})$ vertices (paper, Section 5, the proposition "T Theorem thm:table over $\mathbb F_2$").
3. A deterministic machine deciding TRANS in time $T$ gives such a network: blocks of $N$ cells, epochs of $N$ steps, a popular
   record of head blocks at epoch boundaries ($2^{O(1+T/N)}$ records), one vertex per epoch, block and state wires; the contraction is
   $[M$ accepts $(X,Y)$ with that record$]\in\{0,1\}$, so nothing cancels modulo 2. So $T=\Omega(N^2\sqrt{\log N})=\Omega(n\sqrt{\log n})$.
4. The complement of TRANS has a linear-time verifier with $\lfloor\log n\rfloor+1$ guess bits, so it is not in $\mathrm{DTIME}(n(\log n)^\sigma)$ for
   any $\sigma<1/2$.
5. **Case 2 (ports).** Fix the data of H8 over $\mathbb F_2$. For a parity machine running in time $t=n^2$, split time into small
   intervals and tapes into small blocks of length $B\approx\lambda^{1/2}$ ($\lambda=\log t$); the coarse head movement (skeleton) is
   a vector of trits. For each skeleton build a network of the form H7: the skeleton is the BASE graph (big intervals, owners of big
   blocks), the lanes are the $N=\lambda^{\Theta(1)}$ small intervals / small blocks of a big interval, and accesses inside a big
   interval are routed by a Benes network of depth $O(\log\log t)$ with canonical (computed, not guessed) settings.
6. Interval tables count valid code strings modulo 2; the contraction of the network for skeleton $\sigma$ is the number modulo 2 of
   accepting runs with skeleton $\sigma$ (paper, Section 6, Lemma "Path count").
7. Compress each network by H8 with $T=\lfloor s\log\lambda\rfloor$ blocks: final width $O(t\lambda^{-s}\log\lambda)$.
8. A one-substep locality lemma (radius 3 for incidences, widths, kernels; 6 for far slot numbers; 7 for addresses; 1 for a refresh)
   makes every compressor record checkable from a constant-size neighbourhood of panels.
9. A witness $u$ of $m\approx t\lambda^{-s}\mathrm{polylog}\lambda$ bits lists the skeleton, an owner directory, all panels and the
   final arc bits; a deterministic verifier with a $k=\lceil\log t\rceil$-bit check index $\gamma$ performs one local check. Every free
   choice is fixed by a checked rule, so each true expansion term has exactly one passing witness (uniqueness by induction over levels).
10. Lemma P: $x\in A$ iff the number of $u$ that pass all checks is odd: $A\in\oplus[m]\cdot\forall[k]\cdot\mathrm{DTIME}(m\log\lambda)$.
11. Take $A$ from the parity time hierarchy and pad to $A''$; its complement is in $\mathrm{NTIME}[\nu;2\log\nu]$. If that were in $\mathrm{DTIME}(\nu(\log\nu)^{s/2})$, guessing
    $u$ and running the deterministic decider would put $A$ in parity time $O(t\lambda^{-s/2}(\log\lambda)^7)=o(n^2)$.
12. The parity time hierarchy (proved in the paper: parsimonious transcript simulation; the diagonal machine adds one accepting path)
    forbids this. So Case 2 gives the theorem with $\sigma=s/2$.

**What is new.** Under Weak ETH, Case 1 alone already gives the statement: OpenAI's transposition theorem holds under Weak ETH (its
proof runs over the rationals, where Weak ETH gives "no ports" in characteristic 0; that implication says nothing about
characteristic 2) and its network theorem
applies to deciders. The new content is Case 2 (steps 5-10), which removes Weak ETH, and the stronger form below.

## 5. The stronger form (paper, Section 8)

**Theorem.** Assume H1-H12. There are $\sigma>0$ and a language $L\in\mathrm{coNTIME}[n;\lfloor2\log n\rfloor]$ with
$L\notin\mathrm{NTIME}(n(\log n)^\sigma)\cap\oplus\mathrm{TIME}(n(\log n)^\sigma)$. In particular
$\mathrm{coNTIME}[n;\lfloor2\log n\rfloor]\not\subseteq\mathrm{UTIME}(n(\log n)^\sigma)$.

The witness depends on the case: $L=\mathrm{TRANS}$ without ports (it is not in NTIME), $L=A''$ for a hierarchy language $A$ with
ports (it is not in parity time). The proof uses exactly H1-H12, no further input.
- *Lemma A (no ports, every NTM).* An NTM that has an accepting computation on every $(X,X^T)$ and none on any other $(X,Y)$ needs
  $c_MN^2\sqrt{\log N}$ steps on some $(X,X^T)$. Proof: the network of step 3 with formal weights $z_{j,w}$, one per epoch $j$ and per
  code word $w$ of $N$ transitions; the contraction is a sum of distinct multilinear monomials (one per accepting run with the popular
  record), identically 0 for $Y\ne X^T$. A random assignment of the weights in $\mathbb F_2$ makes it 1 with probability at least
  $2^{-E}$ ($E$ = number of epochs; fix the variables outside one monomial, then the cube sum equals the top coefficient 1). One
  assignment works for a $2^{-o(N^2)}$ fraction of all $X$, which is enough for step 2.
- *Lemma B (ports, parity machines).* For $A$ from the parity time hierarchy at time $n^2$, $A''\in\mathrm{coNTIME}[\nu;2\log\nu]$
  and $A''\notin\oplus\mathrm{TIME}(\nu(\log\nu)^{s/2})$: replace the deterministic decider in step 11 by a parity machine; the sum
  over $u$ of its accepting counts has the right parity, so $A$ would be in parity time $o(n^2)$.
- *Limits.* No NTIME versus coNTIME separation follows (the proof of Lemma B needs a parity count). Lemma A has no proof for parity
  machines (a wrong input may have an even, nonzero number of accepting paths). Machines with at most $(\log n)^\varepsilon$ accepting
  paths and time $O(n(\log n)^\sigma)$ are covered when $\sigma+\varepsilon<s$; polynomial ambiguity is open. The form $\mathrm{NTIME}[n;2\log n]\not\subseteq\mathrm{UTIME}(n(\log n)^\sigma)$ holds if
  characteristic 2 has ports (parity time is closed under complement) and is open if it has none.

## 6. What is not claimed

- Nothing unconditional: everything assumes H1-H12. No explicit $\sigma$.
- No separation of NTIME from coNTIME, and nothing about adjacent levels of the alternation hierarchy or about space. Nothing for
  random-access machines, multidimensional tapes, circuits, branching programs, streaming, or randomized and quantum time (TRANS is
  in linear time on random-access machines and has a linear-time test with one-sided error). No lower bound for SAT or other standard
  problems. Lower bounds for verifying sorting are not claimed.
- The proof does not relativize: for oracle machines with a query tape that is erased after each query, relative to an oracle complete
  for linear space under linear-time reductions, deterministic and nondeterministic linear time coincide (Hemmerling 2011,
  Proposition 15). It uses that a multitape step reads only cells under its
  heads.
- Characteristic 2 is a convenience, not a necessity: for a prime $p$, $\mathrm{Mod}_p$ time is closed under complement with a
  constant factor ($1+(p-1)\#\mathrm{acc}^{p-1}$ accepting paths, Fermat), so it has a time hierarchy, and Case 2 over
  $\mathbb F_p$ needs only $O(\log p)$ more witness bits per final position; this needs characteristic-$p$ forms of H1(d), H2, H4, H5
  and H8, and gives the main theorem again (the stronger form would need further changes, not claimed).
- Guess bits: the proof actually uses $\lfloor\log n\rfloor+1$ guess bits (no ports) and at most $\lceil\log\nu\rceil+\lceil\log\log\nu\rceil+2$
  at input length $\nu$ (ports); for large $n$ this is below $\lfloor2\log n\rfloor$, which is a safe, weaker statement.

## 7. Other definitions in the literature, and how they relate

- *Read-only input tape.* Paul, Pippenger, Szemeredi and Trotter (FOCS 1983) use a separate read-only input tape plus work tapes. Our
  model writes the input on tape 1 with no read-only restriction; the two models simulate each other with a constant factor in time
  (copy the input to a work tape), so linear-time classes and the theorem are the same.
- *Number of tapes.* The deterministic side allows any fixed number of tapes per machine, with no common bound; the verifier has a
  fixed number of tapes. On one-tape machines much stronger separations are known, and they are a different question.
- *Guess bits.* "NTIME$[n;g]$" (verifier with a $g$-bit certificate on a tape) equals Lingas's $\mathrm{NDTIME}(g(n),n)$ (a $g(n)$-bit
  nondeterministic oracle) and the class of NTMs with $O(n)$ time that make at most $O(g)$ binary guesses, up to constant factors in
  $g$ and in time, for budgets $g$ that are computable in linear time. Our theorem fixes the factor: $\lfloor 2\log n\rfloor$ bits.
- *NTIME(n).* We use the standard machine class (every computation halts within $O(n)$ steps); it contains NTIME$[n;g]$ for every
  $g=O(n)$ that is computable in linear time.
- *Infinitely often versus almost everywhere.* "Not in $\mathrm{DTIME}(h)$" means: no machine is correct and $O(h)$-time on all inputs.
  The proof shows that every such machine fails at infinitely many input lengths; it does not show failure at almost every length.
- *A Lean 4 statement* of a slightly weaker form (guess bits $c(\lfloor\log_2 n\rfloor+1)$ for some $c$, two-way infinite tapes, the
  guess written as a self-delimiting prefix of the input) has been written; it is not proved and is not part of this release.

## 8. Status of the checks

Before the final text: an independent reader (Claude) re-derived every step of the paper that is not an input, matched H1-H12
against the cited lines, ran consistency checks against known results, and judged the paper ready as a conditional paper proof; its
corrections are applied. The no-ports case was proved blind by Claude and, independently and blind, by GPT-6.2 Astra from
the OpenAI sources only. The port case (Lemma P) was written by GPT-6.2 Astra and checked line by line by Claude; a blind
Claude attempt isolated the same missing idea (how to make the compressor's lanes identically wired). An adversarial reading
(Claude, with GPT-6.2 Astra and Gemini 4 Neon) found repairable errors in an earlier write-up; all repairs are in the paper. Lemma A
of the stronger form was re-derived blind by GPT-6.2 Astra, who found the specialization over $\mathbb F_2$; Claude checked
it. On the final text: a release check by GPT-6.2 Sol listed 15 points (among them reserved slots at the two ends of the state
chain, the scope of H8 for the fixed choices, a sorting cost in the batched-lookup lemma, integer guess budgets, the choice of the
hierarchy language in Lemma B, and wording); they were addressed. A second and a third check of the fixes (also GPT-6.2 Sol) raised further
points of precision (tag order, small lengths, the scope of the Lean comparison) and three small gaps in unchanged parts (the
simulator in the parity hierarchy on invalid transcripts, the cost bound of check C13 on dishonest witnesses, and a too general form
of Lemma P in the abstract); these were corrected; a fourth check found six remaining points of precision, and a fifth check confirmed their
correction except three wording points (the small-length form of DTIME here, the list of inputs without Lean coverage in a remark
of the paper, and this status text), which were then corrected without a further check. Three searches for earlier work found none (`NOVELTY.md`). Nothing is
machine-checked. Details: `CHECKS.md`.


## 9. Addendum of 26 November 2026: the theorem in Lean 4, with no assumption

Sections 1 to 8 above are the text of 25 November 2026 and are not changed. Since then the conclusion of the theorem of
Section 1 (both sentences) and the stronger form of Section 5 (both sentences) have been proved in Lean 4 **with no
hypothesis**: H1 to H12 are not assumed. Where the paper uses an input, the Lean proof uses a theorem of OpenAI's Lean library
(commit 3344da5, with two small patches of ours that make its port statement uniform in the field) or a lemma of our own;
OpenAI's proofs are compiled and checked by the kernel as part of the build.

- Lean theorems: `P1Final.c1_closed`, `P1Final.c1_ntime_closed`, `P1Final.c1u_closed`, `P1Final.c1u_utime_closed`. Their types
  are, as Lean terms, those of the targets in the Mathlib-only statement files `lean/C1Challenge/` (`LEAN-STATEMENT.md`).
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The case split. The paper splits on "F_2 has ports" and joins this to characteristic 2 by H1(b). The Lean proof splits, by
  excluded middle, on "the algebraic closure of F_2 has ports" (`PortTwo`) and uses each case only through that proposition.
  So the Lean theorem does not need H1(b); sigma is not effective in Lean either.
- The Lean statement uses floor(2 log2 n) guess bits exactly, the paper's class. The draft Lean statement named in Section 7
  (last item, with c (floor(log2 n) + 1) guess bits) was replaced on 25 November: its time bound did not count the guess
  prefix, which made it false (a Lean proof of that is in the development).
- Not in Lean: the equivalence of the Lean machine model (two-way tapes, guess as an input prefix) with the model of Section 2
  (argued in words, `LEAN-STATEMENT.md` section 4).
- Two errata to the paper found by the Lean work; neither affects the theorem: `ERRATA.md`.
- Audit (three kernels, clean rebuilds, checksums): `LEAN-AUDIT.md`. No human has read the Lean statement or the proof.
