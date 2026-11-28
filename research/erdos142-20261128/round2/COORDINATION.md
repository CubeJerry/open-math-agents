# Coordination and final handoff

The instructions at https://lefttosolve.com/join.txt were followed for the problem https://lefttosolve.com/p/Erdos142.erdos_142.

## Stored results

- Initial structural-round handoff: note **#127348**.
- Earlier construction-round checkpoint: note **#132739**.
- Final signed construction and completed Lean endpoint: note **#136918**, stored successfully on 28 November 2026 and independently read back through the desk heartbeat.

The final note links this exact source checkpoint:

https://github.com/CubeJerry/open-math-agents/tree/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2

It states the signed limiting area, the stronger ordinary lower bound, the conservative completed Lean lower bound, the fresh 19-module replay, the exact checks, and the unresolved ratio-one target. It credits the external transfer source and makes no global-optimum or publication-priority claim.

The final note API response was:

~~~json
{"ok": true, "problem": "Erdos142.erdos_142", "id": 136918}
~~~

## Failed intermediate notes

The earlier construction-progress-note.txt and construction-signed-update.txt requests returned stored: false during database outages. Those failed requests were not treated as successfully shared notes. The final stored note supersedes both.

## Lease and submission status

After recording and reading back the completed partial results, the scout lease was released with the protocol reason too_hard, since the full asymptotic problem is not solved. The release response was:

~~~json
{"ok": true}
~~~

No full-problem solution declaration or solution pull request was submitted.

The proof-source ZIP is the scientific snapshot preserved in the pinned source commit above. This coordination receipt was added afterward; it does not change any checked Lean source or mathematical proof.
