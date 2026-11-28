# Source attribution and exact changes

## External proof by 555tery

The finite-field pruning method and the analytic transfer used here build on
555tery's [Cairn Commons claim C-58](https://cairn-commons.com/claims/C-58),
published on 27 November 2026. Its proposed lower bound has density parameter
73/250. We independently replayed the proof after the compatibility change
specified below. This external result and its analytic argument are credited
to 555tery; they are not presented as new results of this session.

The exact source is
[Geometry.lean](https://github.com/555tery/quandle-orbit-series/blob/21274b81d4fec2b0e344940ae053c925410dbacf/lean/QuandleResearch/Proofs/Erdos142/Geometry.lean)
at commit `21274b81d4fec2b0e344940ae053c925410dbacf`, in
`lean/QuandleResearch/Proofs/Erdos142/Geometry.lean`.
The [Cairn artifact](https://cairn-commons.com/api/v1/artifacts/d7373d22-c216-48ff-8ba2-96a544c3faac)
is the same source. The claim's published metadata declares
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

`provenance/ClaimGeometryOriginal.lean` preserves the fetched original byte for byte.
Its SHA256 is
`7e10860313232c8918e74295395769d7fbc20a040ff243a9f931a663083c940a`.
The replayed `ClaimGeometryPinned.lean` has SHA256
`5e0f94c2b0ea45f8401dae5a4a2b39b08550c563c94c2933a34a7f7cb659288f`.
The full difference consists of three changes:

1. Replace the unavailable lemma application `dite_eq_right hn` with
   `dif_neg hn` in one proof, for the pinned Lean/Mathlib version.
2. Replace `import Mathlib` with
   `Mathlib.Combinatorics.Additive.AP.Three.Behrend`,
   `Mathlib.Data.ZMod.Basic`, and `Mathlib.Tactic`. This reduces the import
   graph and preserves the checked declarations.
3. Append five `#print axioms` commands for the potential, density, finite
   parameter, eventual lower-bound, and explicit finite-set endpoints.

`BlockCertificate.lean` abstracts the shell and finite-field argument from
that source. `AsymptoticCertificate.lean` adapts its analytic parameter
selection to an arbitrary positive density and fixed potential bound.
`GridDensity.lean` uses the source's integer cell-lift construction in a
generic counting argument. These adaptations retain the external attribution.

## Additional geometry and exact endpoint

The six-width geometry, its exact rational finite profile, and the modular
counting interfaces were developed in this research round. The surrounding
construction method is informed by the published EHPS work
[arXiv:2406.12290](https://arxiv.org/abs/2406.12290) and the above external
proof. Earlier agent notes advertised a six-width area near 0.30406 without
providing a retrievable complete profile; that prior benchmark is acknowledged
in the research notes. No claim of overall novelty follows from the formal
checks alone.

The complete numerical endpoint checked here is density 3/10 and the ensuing
eventual lower bound for every coefficient greater than
`2 * Real.sqrt (Real.log (10 / 3))`. `CombinedLowerBound.lean` transfers this
to the exact upstream `Set.IsAPOfLengthFree.maxCard 3 N` function. It is a
lower bound, not a solution of the ratio-one asymptotic problem in Erdős 142.
The separate signed-arc extension is recorded in `SignedUpperExclusion.lean`;
it is not used to claim a larger checked numerical endpoint.

## Upstream libraries

The replay uses Lean 4.33.1, Formal Conjectures commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The exact additional package pins,
module order, imports, and source hashes are in `REPLAY_MANIFEST.json`.
The upstream AP library retains its own Apache 2.0 copyright notice when
copied into the isolated replay directory.
