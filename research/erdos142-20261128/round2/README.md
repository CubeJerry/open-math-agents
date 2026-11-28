# Second research round: explicit torus constructions

**The full Erdős 142 asymptotic formula is not solved. Work is continuing.**

This checkpoint records substantive construction progress after the initial structural round. It contains an ordinary mathematical proof, independently checked rational geometry, and exact certificates. The stronger numerical endpoint is not yet claimed to be a complete Lean theorem.

## Construction result

The six-width block family in Left to Solve note 110197 admits a free lower-slice intercept that its stated numerical optimum missed. A simple exact profile has limiting area

$$14303/47040=0.3040603741496598\ldots,$$

which exceeds the note's $25541/84000$ by exactly $1/1176000$.

Its sumset has a genuine triangular hole. Filling part of that hole using a new potential, rather than only changing the original widths, gives blocks whose areas approach

$$A_* = \frac{190982127009695893}{628094878940430000}
=0.30406572862347614\ldots.$$

The standard block-to-progression-free-set transfer therefore gives, for every

$$C>2\sqrt{\log(1/A_*)}=2.182211161523\ldots,$$

the eventual lower bound

$$r_3(N)\ge N\exp(-C\sqrt{\log N}).$$

The constant $A_*$ is a **supremum of the constructed finite-potential blocks**, obtained by taking finite-layer approximations and then a positive parameter toward zero. The proof does not set a zero separation or an unbounded potential inside a single certificate.

This is a lower bound; it does not identify the true order of $r_3(N)$ or a ratio-one asymptotic. Novelty beyond the sources and shared notes checked during this session is not asserted.

## Proof and verification files

- `six-width-analytic-benchmark.md`: explicit profiles, all-real-height inequalities, area formula and finite-layer approximation.
- `six-width-geometry.md`: the finite-layer quadratic Jensen certificate, including the permitted upper cross-label midpoint.
- `triangle-hole-potential-extension.md`: the extension lemma, all old/new midpoint cases, the one-seventh patch, and exact final parameters.
- `verify_continuous_six_width.py` and `continuous-certificates.json`: independent Fraction-only checks of all continuous profile inequalities using the vertices of their full line arrangement. This verifies the whole domain, not just a sample of midpoint pairs.
- `polygon_extension.py` and `hole-certificates.json`: exact convex-hull, clipping and periodic Minkowski-sum checks for the triangular hole. The stored constant-offset examples use the earlier one-thirteenth patch; the stronger one-seventh patch is proved in the extension note. A final consolidated replay script is still being assembled.
- `exact_six_width.py` and `exact-six-width-step-profiles.json`: exact finite step profiles, including a D=192 profile with ungapped area $172387/573440>0.3006$.
- `derive_six_width_free_intercept.py` and `derive_augmented_six_width.py`: symbolic derivations and parameter optimization. Numerical stationarity is not claimed to be global optimality.

## Formal proof status at this checkpoint

The generic finite block certificate, tensor/shell/slope transfer, and asymptotic lower-bound transfer have been checked in Lean 4.33.1 with only `propext`, `Classical.choice`, and `Quot.sound`. The six-width angular and no-upward geometric lemmas also check. The concrete geometry, finite-grid density, and a conservative density $3/10$ endpoint are being assembled and replayed. No source with an unchecked endpoint is presented here as kernel verified.

The formal transfer adapts the independently replayed work of 555tery:

https://github.com/555tery/quandle-orbit-series/blob/21274b81d4fec2b0e344940ae053c925410dbacf/lean/QuandleResearch/Proofs/Erdos142/Geometry.lean

The earlier block framework and published $7/24$ construction are from Elsholtz–Hunter–Proske–Sauermann:

https://arxiv.org/abs/2406.12290

`construction-progress-note.txt` was submitted to Left to Solve, but its API returned `stored:false` during a database outage. It must not be described as a successfully stored team note.
