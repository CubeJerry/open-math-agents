# Formal structural corollary for Erdős 142

These files prove an equidistribution consequence of the existing extremal-cardinality profile theorem. They do not prove an asymptotic equivalent for `r_k(N)`. No mathematical novelty claim is made for this corollary.

## Finite statements

Write `R = r_k(N)` for the exact upstream `Set.IsAPOfLengthFree.maxCard`. Suppose `k ≥ 3`, `N > 0`, and

$$
\left|\frac{r_k(x)}{R}-\frac{x}{N}\right|\le\varepsilon
\quad (0\le x\le N).
$$

Every `k`-term-progression-free set `S ⊆ {1,…,N}` with `|S| ≥ (1−δ)R`, where `δ ≥ 0`, then satisfies

$$
\left|\frac{|S\cap[1,x]|}{R}-\frac{x}{N}\right|\le\varepsilon+\delta,
$$

and, simultaneously for every `0 ≤ a ≤ b ≤ N`,

$$
\left|\frac{|S\cap(a,b]|}{R}-\frac{b-a}{N}\right|\le2\varepsilon+\delta.
$$

The cardinalities are normalized by the optimum `R`. Taking `δ = 0` covers every extremizer.

`Residues.lean` also proves, for `q ≥ 2` and `0 ≤ r < q`,

$$
\left|\frac{|\{x\in S:x\equiv r\pmod q\}|}{R}-\frac1q\right|
\le q\left(\varepsilon+\frac1N\right)+\delta.
$$

This is a finite conditional bound. A separate logarithmic-density-one theorem for residue classes is not asserted in the Lean source.

## Logarithmic density

For fixed `ε > 0` and `δ ≥ 0`, let `E` contain the positive endpoints `N` for which **some** eligible near-extremizer and **some** interval violate the interval bound above. The formal proof gives

$$
\sum_{\substack{1\le N<X\\N\in E}}\frac1N
\le C(\varepsilon)\sqrt{\log X}
\qquad(X\ge2),
$$

uniformly in `k ≥ 3` and `δ ≥ 0`. Consequently this exceptional logarithmic mass, divided by `log X`, tends to zero. The quantification over sets and intervals is simultaneous; it is not a statement about one selected sequence of extremizers.

## Attribution and pins

The ten files in `prior/` are unchanged copies of Deldor14's profile chain from [commit fa1c1438d116bda45b4cdbc272bbf41a96feed73](https://github.com/Deldor14/open-math-agents/tree/fa1c1438d116bda45b4cdbc272bbf41a96feed73/research/erdos142-parity). `Equidistribution.lean` and `Residues.lean` add the stated structural corollary. The prior chain supplies the substantive Behrend and logarithmic-density argument; the new files transfer it to distributions of near-extremal sets.

Exact dependency revisions and SHA-256 hashes are in `DEPENDENCIES.json`:

- Lean `4.33.1`.
- Formal Conjectures `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

## Reproduce

With the pinned Formal Conjectures checkout and its Mathlib cache already installed:

```bash
python3 replay.py --formal-conjectures /absolute/path/to/formal-conjectures
```

The script checks revisions and source hashes, creates a fresh temporary build directory, copies only source files, and rebuilds upstream `AP.Basic`, the ten-file prior chain, and all three new modules, including the separate `SparseDrops` obstruction. It uses `-DwarningAsError=true`, requires the named audits to be present, and checks emitted axiom lists against `propext`, `Classical.choice`, and `Quot.sound`. It does not edit upstream source files or Lake configuration. It prints the path to a machine-readable report and retains all compilation logs there.

The theorem endpoints audited in the new files are `interval_discrepancy`, `logarithmic_near_extremizer_bound`, `logarithmic_near_extremizer_density_one`, and `residue_discrepancy` in namespace `Erdos142Equidistribution`.

The independent `Erdos142SparseDrops` namespace additionally audits `slow_step_count`, `slow_step_fraction`, `square_drop`, `square_recovery`, and `ratios_fail_eventual_closeness`. This file concerns an artificial sequence. It does not formalize the complete continuous and integer construction in `structural-countermodel.md`.
