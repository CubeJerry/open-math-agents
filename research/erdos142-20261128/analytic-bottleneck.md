# Primary sources and the analytic bottleneck

Research note, 28 November 2026. This session did not obtain an asymptotic formula for the progression-free extremal function, a matching upper and lower bound, or a proof of the proposed sifting dichotomy.

## Bounds checked against primary sources

**Upper bound for three-term progressions.** Rushil Raghavan, [*Improved Bounds for 3-Progressions*, arXiv:2603.27045v3](https://arxiv.org/html/2603.27045v3), Theorem 1.4, gives

\[
r_3(N)\le N\exp\left[-\Omega\left(\left(\frac{\log N}{\log\log N}\right)^{1/6}\right)\right].
\]

The theorem in version 3, dated 15 May 2026, is sharper than the bound retained in its abstract: the theorem has a factor \((\log\log N)^{-1/6}\) in the exponent, whereas the abstract has \((\log\log N)^{-1}\). Proposition 4.2 gives a density increment with added Bohr rank \(O(L^4)\), where \(L=\log(2/\alpha)\). Its iteration produces rank \(O(L^5)\), logarithmic reciprocal radius \(O(L\log L)\), and consequently \(\log N=O(L^6\log L)\).

**Published lower-bound construction.** Elsholtz, Hunter, Proske, and Sauermann, [*Improving Behrend's construction*, arXiv:2406.12290](https://arxiv.org/html/2406.12290v1), Theorem 1.1, gives

\[
r_3(N)\ge N\,2^{-(C+o(1))\sqrt{\log_2 N}},
\qquad C=2\sqrt{\log_2(24/7)}.
\]

In natural logarithms, the leading constant is \(2\sqrt{\log(24/7)}=2.220039352\ldots\). This is a lower bound, not an asymptotic equality.

**Recent lower-bound claim with public verification evidence.** [Cairn claim C-58](https://cairn-commons.com/claims/C-58), posted by 555tery on 27 November 2026, claims the bound

\[
r_3(N)\ge N\exp[-C\sqrt{\log N}]
\]

eventually for every \(C>2\sqrt{\log(250/73)}=2.219010119\ldots\). The [pinned Lean source](https://github.com/555tery/quandle-orbit-series/blob/21274b81d4fec2b0e344940ae053c925410dbacf/lean/QuandleResearch/Proofs/Erdos142/Geometry.lean) contains an endpoint stated using explicit AP-free finite subsets of the conventional interval. Its [GitHub workflow](https://github.com/555tery/quandle-orbit-series/actions/runs/46024786132) reports success; the workflow specifies compilation, axiom auditing, and six-kernel replay. This session inspected the source and workflow but **did not independently replay the proof**. No novelty or full-problem claim is made here.

**General fixed lengths.** OpenAI's [*Quasipolynomial Bounds for Arithmetic Progressions*, September 2026](https://github.com/openai/math/tree/main/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026), claims \(r_k(N)\le C_kN\exp[-c_k(\log N)^{\varepsilon_k}]\) for every fixed \(k\ge3\), with positive constants depending on \(k\). This session did not audit that proof or independently establish the quantitative theorem's Lean coverage. The claimed estimate itself supplies no ratio-one formula.

## What the sifting obstruction does and does not show

The existing team notes describe progression-free examples in which general sifting requires output logarithmic density losses of quadratic order in \(L\). Those examples obstruct an unconditional replacement of the sifting output density by \(\alpha^{O(1)}\).

Their quadratic-graph construction also confines a label coordinate to a short interval. A single label character therefore supplies a cheap density increment. Consequently, those examples do not rule out the different assertion: **either a cheap structured density increment exists, or efficient sifting is possible**.

No proof of that assertion was obtained. A useful version would have to bound the new rank, radius, density gain, and localization losses, with hypotheses that remain applicable throughout iteration. Identifying an increment in one example does not establish the general dichotomy.

## Conditional bookkeeping calculation

Even if a valid theorem reduced both sifting logarithmic density losses from \(O(L^2)\) to \(O(L)\), retaining the other current steps would leave the product of these two losses in the almost-periodicity estimate. The resulting rank increment would have order \(L^2\). With the same iteration and radius accounting, this would give

\[
d=O(L^3),\qquad -\log\rho=O(L\log L),
\qquad \log N=O(L^4\log L).
\]

This is a conditional parameter calculation, not a new upper-bound theorem. It suggests an exponent near \(1/4\), which still does not match the known lower-bound scale. More generally, rank increment \(O(L^a)\) in this architecture leads to logarithmic size cost \(O(L^{a+2}\log L)\).

The requested ratio-one formula is stronger still: even identifying a leading \(\sqrt{\log N}\) coefficient in both bounds leaves a possible multiplicative error \(\exp[o(\sqrt{\log N})]\), which need not converge to one.

## Exploratory calculation not promoted to a result

Centered sphere slices were considered as stress tests for the proposed dichotomy. Heuristic local central-limit estimates suggested a tradeoff between sifting loss and the radius cost of a tangent-plane increment. The required estimates and their uniform applicability were not proved. These calculations were not used in any verified theorem or posted as completed work.
