# Reproducing the formal and exact arithmetic checks

## Formal endpoint

The principal theorem is Erdos142LowerBound.r_three_eventual_of_constant in [formal/CombinedLowerBound.lean](formal/CombinedLowerBound.lean). It proves

$$
\forall C>2\sqrt{\log(10/3)},\quad
\exists N_0,\ \forall N\ge N_0,\quad
N e^{-C\sqrt{\log N}}\le
\operatorname{Set.IsAPOfLengthFree.maxCard}(3,N).
$$

The last function is definitionally Erdos142.r 3 N. The proof avoids importing the upstream file containing the unsolved target.

## Required environment

- Lean 4.33.1.
- Formal Conjectures commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53.
- Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.
- The matching Mathlib and support-package compiled dependency caches.

[DEPENDENCIES.json](DEPENDENCIES.json) records the checked source hashes, order, and required axiom audits. [REPLAY_MANIFEST.json](REPLAY_MANIFEST.json) also records the nine supporting package commits and import provenance. The runner verifies the compiler version, Formal Conjectures commit, Mathlib commit, upstream AP.Basic hash, and all 18 local module hashes before it builds anything.

Run, replacing the example paths with the locations of the pinned checkout and binary:

~~~bash
python replay_formal.py \
  --formal-conjectures /path/to/formal-conjectures \
  --lean /path/to/lean-4.33.1/bin/lean \
  --output-parent /path/to/fresh-builds
~~~

The runner creates a new directory. It copies the checked sources there, compiles every module with one worker and warnings as errors, saves the compiler logs, and records all requested axiom audits. It neither edits the checkout nor relies on earlier local proof outputs. Cached standard-library and Mathlib dependencies are intentionally reused.

## Recorded successful replay

The saved [verification.json](verification.json) reports:

- Status: passed.
- 19 modules: upstream AP.Basic plus 18 local modules.
- 48 axiom-audit entries covering 47 distinct declarations.
- Allowed audit dependencies: propext, Classical.choice, Quot.sound.
- Total compiler time: 470.988 seconds.
- Final endpoint source SHA256: 061fa632f0eda45ea54f95ecf5d669c812460f33f70aa0dfd66830c02cc1185b.

The report contains each source hash, elapsed time, exit code, and exact axiom list. The build began at 2026-11-28 12:27:08 UTC and finished at 12:34:59 UTC.

## Exact ordinary-proof audits

The geometric verifiers use Python's standard-library Fraction arithmetic:

~~~bash
python verify_signed_six_width.py
python verify_continuous_six_width.py
python verify_augmentations.py
python exact_six_width.py
~~~

The first command independently checks the full continuous pair-domain inequalities for the rational signed profile, reducing piecewise-affine inequalities to the vertices of their exact line arrangement. The third checks periodic Minkowski exclusions and areas for the hole extensions.

Symbolic integration requires SymPy:

~~~bash
python derive_signed_six_width.py
~~~

This directly integrates the actual profile pieces, then checks the displayed area formula and exact square identity. The optional numerical LP search uses NumPy/SciPy and is not part of the proof.

The larger signed constant is supported by the ordinary proof plus these independent audits. These commands do not turn it into a Lean theorem. SignedUpperExclusion.lean checks useful signed geometric lemmas, but the completed density instantiation in the formal chain remains 3/10.
