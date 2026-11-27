# Proofs of OEIS conjectures

These proofs use Lean 4.33.1 and the project's pinned Mathlib. The matching statement files give each proof its declared target. The project checks the axioms of `OMA.solution` to ensure the proof is independent of the statement placeholder.

## A365383 — Least eventual period of a partition row

Fix a positive integer $n$. Let $T(n,k)$ count the partitions of $n$ whose part sizes represent $k$ with unrestricted nonnegative multiplicities. If a partition represents $k$, appending every part of the partition once gives a representation of $k+n$. Thus $T(n,k)$ is nondecreasing along each residue class modulo $n$. Each such sequence consists of integers bounded by the number $p(n)$ of partitions. It eventually stabilizes. Taking the largest threshold among the $n$ residue classes gives $T(n,k+n)=T(n,k)$ for all sufficiently large $k$.

In fact $T(n,k)=p(n)$ exactly when $n$ divides $k$. Every partition represents every multiple of $n$ by repeated use of all its parts. Conversely, the one-part partition $(n)$ represents only multiples of $n$. If $t$ is any eventual period, take a sufficiently large multiple $k$ of $n$. Both $k$ and $k+t$ give the maximum row value, so $n$ divides $t$. The least positive eventual period is therefore exactly $n$.

[Conjecture](https://oeis.org/A365383) · [Lean proof](../../proofs/oeis-a365383.lean) · [Lean statement](../../statements/oeis-a365383.lean)

## A389425 — Natural density of unit gaps

List the positive integers $k$ such that $6k-5$ and $6k-1$ are both composite as $t_0<t_1<\cdots$. The progression $35j+16$ consists of eligible integers, since the two expressions are $7(30j+13)$ and $5(42j+19)$. Hence $t_i\le 35i+16$.

If $t_{i+1}-t_i>1$, then $t_i+1$ is ineligible. At least one of $6t_i+1$ and $6t_i+5$ is prime. Assign one such prime to the gap. The intervals $[6t_i+1,6t_i+5]$ are disjoint, so distinct exceptional gaps receive distinct primes. For $i<N$ every assigned prime is at most $400N$. Consequently the number of exceptional gaps among the first $N$ is at most $\pi(400N)$. Chebyshev's bound gives $\pi(400N)=O(N/\log N)=o(N)$, proving the asserted natural density of one.

[Conjecture](https://oeis.org/A389425) · [Lean proof](../../proofs/oeis-a389425.lean) · [Lean statement](../../statements/oeis-a389425.lean)

## A395088 — Zero runs in the morphic fixed point

Let $h(0)=011$ and $h(1)=0$. Iteration from $0$ gives strictly increasing nested prefixes and therefore an infinite fixed point $w$. The second iterate has the two blocks $h^2(0)=01100$ and $h^2(1)=011$. Each starts with one zero and two ones. An additional pair of zeros follows the ones precisely when the input bit is zero.

Since $w=h^2(w)$, its initial zero run has length one. After the two ones in the block for input $w_i$, the next zero run consists of the trailing zeros of that block and the initial zero of the following block. Its length is three for $w_i=0$ and one for $w_i=1$. Every one run has length two. With the input indexed from zero and runs from one, this gives $c(i+2)=3-2w_i$ for every $i\ge0$.

[Conjecture](https://oeis.org/A395088) · [Lean proof](../../proofs/oeis-a395088.lean) · [Lean statement](../../statements/oeis-a395088.lean)
