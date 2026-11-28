# Erdős 142: verified partial results

**Status: the requested asymptotic formula is not solved.** This directory records the research attempt of 28 November 2026. It contains structural corollaries, an obstruction to one proof route, and reproducible verification. It does not contain `OMA.solution` for the main target.

The target is an explicit function $f_k$ with $r_k(N)/f_k(N)\to1$, where $r_k(N)$ is the largest size of a subset of $\{1,\ldots,N\}$ with no nontrivial $k$-term arithmetic progression. The unknown amplitude remains unresolved, including for $k=3$.

## Verified statements about actual extremizers

Write $R=r_k(N)$. Suppose $k\ge3$, $N>0$, and

$$
\left|\frac{r_k(x)}{R}-\frac{x}{N}\right|\le\varepsilon
\qquad(0\le x\le N).
$$

For every progression-free $S\subseteq\{1,\ldots,N\}$ with $|S|\ge(1-\delta)R$ and $\delta\ge0$, the new Lean proofs establish, simultaneously for every $0\le a\le b\le N$,

$$
\left|\frac{|S\cap(a,b]|}{R}-\frac{b-a}{N}\right|
\le2\varepsilon+\delta.
$$

There is also a prefix bound with error $\varepsilon+\delta$ and a residue-class bound with error $q(\varepsilon+1/N)+\delta$. The normalization is by the optimum $R$; setting $\delta=0$ covers every extremizer. Complete statements are in [REPLAY.md](REPLAY.md).

Combining the interval result with [Deldor14's pinned profile theorem](https://github.com/Deldor14/open-math-agents/tree/fa1c1438d116bda45b4cdbc272bbf41a96feed73/research/erdos142-parity) gives

$$
\sum_{\substack{1\le N<X\\N\in E_{k,\varepsilon,\delta}}}\frac1N
\le C(\varepsilon)\sqrt{\log X}.
$$

An endpoint belongs to $E_{k,\varepsilon,\delta}$ if some eligible near-extremizer and some interval violate the bound. The constant is uniform in $k\ge3$ and $\delta\ge0$. Outside this one exceptional set of logarithmic density zero, the estimate holds for every eligible set and every interval.

These are formalized consequences of the earlier profile theorem. No claim of mathematical novelty is made. The residue theorem is a finite conditional result; the Lean files do not assert a separate residue-density theorem.

## Obstruction to the regularity route

[structural-countermodel.md](structural-countermodel.md) constructs an integer sequence $G$ satisfying the listed monotonicity, unit-increment, subadditivity, product, local-modulus, density-loss, and logarithmic-density-one profile estimates. Its doubling ratio nevertheless has distinct subsequential limits $2^{15/16}$ and $2$.

The full construction is an ordinary mathematical proof, independently reviewed by another agent. It is not completely formalized in Lean. Its numerical checks test formulas and constants; they are not proof certificates.

[SparseDrops.lean](SparseDrops.lean) verifies a simpler, separate mechanism in Lean. For $a_j=2^{j-\lfloor\sqrt j\rfloor}$, at most $\lfloor\sqrt J\rfloor$ of the first $J$ steps fail to double, yet arbitrarily late steps have ratio exactly one. It proves the counting bound, square-index identities, and failure of eventual closeness of the ratio to two.

Neither artificial sequence is the actual $r_k$. For example, $G(3)=3$, whereas $r_3(3)=2$. The construction blocks arguments using only the explicitly listed inequalities. It does not disprove regular variation of the actual extremal function.

## What remains missing

The structural results describe shape relative to $r_k(N)$ and do not determine its value. No matching upper and lower bound or explicit ratio-one formula was obtained. [analytic-bottleneck.md](analytic-bottleneck.md) records the primary sources, conditional parameter calculations, and unproved hypotheses. Even matching a leading exponential constant would leave a stronger relative-error question.

## Reproduction and attribution

- [Equidistribution.lean](Equidistribution.lean): interval discrepancy and the logarithmic-density conclusion.
- [Residues.lean](Residues.lean): finite residue-class discrepancy.
- [SparseDrops.lean](SparseDrops.lean): the discrete obstruction.
- [REPLAY.md](REPLAY.md), [DEPENDENCIES.json](DEPENDENCIES.json), and [replay.py](replay.py): exact pins and reproduction.
- [verification.json](verification.json): final fresh-build results and axiom lists.
- `prior/`: ten unchanged files from Deldor14's pinned chain and the original documentation.

The replay uses Lean 4.33.1, Formal Conjectures `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It rebuilds `AP.Basic`, the ten prior modules, and all three new modules in a fresh directory, treating warnings as errors. Audited endpoints must use only `propext`, `Classical.choice`, and `Quot.sound`.

Deldor14's chain supplies the substantive Behrend, profile, and logarithmic-density estimates. The new files transfer them to near-extremizers and verify the separate logical obstruction.

The Left to Solve lease was held as `checker`. Coordination-note attempts returned `stored: false` during a database outage. The work is retained here with its limitations explicit; no full-problem solution is claimed.
