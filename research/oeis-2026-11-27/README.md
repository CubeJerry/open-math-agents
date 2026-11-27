# Proofs of OEIS conjectures

These proofs use Lean 4.33.1 and the project's pinned Mathlib. The matching statement files give each proof its declared target. The project checks the axioms of `OMA.solution` or `OMA.disproof` to ensure the proof is independent of the statement placeholder.

## Left to Solve submissions

Each linked pull request asks for the human translation review required before a proof can enter the project’s proof queue. The linked proof and verdict are available here for immediate review.

| OEIS entry | Statement pull request | Verified proof |
|---|---|---|
| A365383 | [#4651](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4651) | [Lean](../../proofs/oeis-a365383.lean) · [Verdict](verification/365383.json) |
| A389425 | [#4664](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4664) | [Lean](../../proofs/oeis-a389425.lean) · [Verdict](verification/389425.json) |
| A395088 | [#4647](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4647) | [Lean](../../proofs/oeis-a395088.lean) · [Verdict](verification/395088.json) |
| A398920 | [#4644](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4644) | [Lean](../../proofs/oeis-a398920.lean) · [Verdict](verification/398920.json) |
| A395111 | [#4626](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4626) | [Lean](../../proofs/oeis-a395111.lean) · [Verdict](verification/395111.json) |
| A385590 | [#4635](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4635) | [Lean](../../proofs/oeis-a385590.lean) · [Verdict](verification/385590.json) |
| A383702 | [#4629](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4629) | [Lean](../../proofs/oeis-a383702.lean) · [Verdict](verification/383702.json) |
| A398343 | [#4622](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4622) | [Lean](../../proofs/oeis-a398343.lean) · [Verdict](verification/398343.json) |

## A365383 — Least eventual period of a partition row

Fix a positive integer $n$. Let $T(n,k)$ count the partitions of $n$ whose part sizes represent $k$ with unrestricted nonnegative multiplicities. If a partition represents $k$, appending every part of the partition once gives a representation of $k+n$. Thus $T(n,k)$ is nondecreasing along each residue class modulo $n$. Each such sequence consists of integers bounded by the number $p(n)$ of partitions. It eventually stabilizes. Taking the largest threshold among the $n$ residue classes gives $T(n,k+n)=T(n,k)$ for all sufficiently large $k$.

In fact $T(n,k)=p(n)$ exactly when $n$ divides $k$. Every partition represents every multiple of $n$ by repeated use of all its parts. Conversely, the one-part partition $(n)$ represents only multiples of $n$. If $t$ is any eventual period, take a sufficiently large multiple $k$ of $n$. Both $k$ and $k+t$ give the maximum row value, so $n$ divides $t$. The least positive eventual period is therefore exactly $n$.

[Conjecture](https://oeis.org/A365383) · [Lean proof](../../proofs/oeis-a365383.lean) · [Lean statement](../../statements/oeis-a365383.lean)

## A389425 — Natural density of unit gaps

List the positive integers $k$ such that $6k-5$ and $6k-1$ are both composite as $t_0\lt t_1\lt \cdots$. The progression $35j+16$ consists of eligible integers, since the two expressions are $7(30j+13)$ and $5(42j+19)$. Hence $t_i\le 35i+16$.

If $t_{i+1}-t_i\gt 1$, then $t_i+1$ is ineligible. At least one of $6t_i+1$ and $6t_i+5$ is prime. Assign one such prime to the gap. The intervals $[6t_i+1,6t_i+5]$ are disjoint, so distinct exceptional gaps receive distinct primes. For $i\lt N$ every assigned prime is at most $400N$. Consequently the number of exceptional gaps among the first $N$ is at most $\pi(400N)$. Chebyshev's bound gives $\pi(400N)=O(N/\log N)=o(N)$, proving the asserted natural density of one.

[Conjecture](https://oeis.org/A389425) · [Lean proof](../../proofs/oeis-a389425.lean) · [Lean statement](../../statements/oeis-a389425.lean)

## A395088 — Zero runs in the morphic fixed point

Let $h(0)=011$ and $h(1)=0$. Iteration from $0$ gives strictly increasing nested prefixes and therefore an infinite fixed point $w$. The second iterate has the two blocks $h^2(0)=01100$ and $h^2(1)=011$. Each starts with one zero and two ones. An additional pair of zeros follows the ones precisely when the input bit is zero.

Since $w=h^2(w)$, its initial zero run has length one. After the two ones in the block for input $w_i$, the next zero run consists of the trailing zeros of that block and the initial zero of the following block. Its length is three for $w_i=0$ and one for $w_i=1$. Every one run has length two. The theorem `all_runs` also constructs the infinite sequence and gives the start and end of every run. With the input indexed from zero and runs from one, this gives $c(i+2)=3-2w_i$ for every $i\ge0$.

[Conjecture](https://oeis.org/A395088) · [Lean proof](../../proofs/oeis-a395088.lean) · [Lean statement](../../statements/oeis-a395088.lean)

## A398920 — Counting solutions to $ab+bc+cd\le N$

The variables are positive integers, as in the entry's geometric description and enumeration. Put $i=b$ and $j=b+d$. This is a bijection with solutions $ia+jc\le N$ with $1\le i\lt j\le N$ and $a,c\ge1$. Write $W_{ij}$ for the count at fixed $i,j$ and $q=\lfloor N/i\rfloor$, $r=N-iq$. Then

$$
W_{ij}=\sum_{a=1}^{q}\left\lfloor\frac{N-ia}{j}\right\rfloor .
$$

Removing the floors increases the sum by at most $q\le N/i$. The resulting sum falls short of the triangle area $N^2/(2ij)$ by exactly $(r^2+i(N-r))/(2ij)$, as follows by summing $1+\cdots+q=q(q+1)/2$. Since $0\le r\lt i$, the latter loss is between zero and $N/(2j)$. In particular,

$$
0\le\frac{N^2}{2ij}-W_{ij}\le\frac{N}{i}+\frac{N}{j}.
$$

Let $H_N=\sum_{i=1}^N 1/i$ and $D_N=\sum_{i=1}^N 1/i^2$. Summing the error bound over $i\lt j$ gives an error at most $N(N-1)H_N$. The areas sum to

$$
\frac{N^2}{2}\sum_{i\lt j}\frac{1}{ij}=\frac{N^2}{4}(H_N^2-D_N).
$$

Here $0\le D_N\le H_N$ and $\log N\le H_N\le 1+\log N$. Thus $H_N^2=(\log N)^2+O(\log N)$, while the floors and the diagonal also contribute at most $O(N^2\log N)$. Consequently

$$
a(N)=\frac{N^2(\log N)^2}{4}+O(N^2\log N)
$$

as conjectured. The theorem `original_quadruples_asymptotic` states this directly for the cardinality of the original positive quadruples. Its explicit bijection identifies each quadruple with exactly one summand and one of its counted choices. The constant $1/4$ accounts for both the triangle area and the restriction to distinct sizes in increasing order.

[Conjecture](https://oeis.org/A398920) · [Lean proof](../../proofs/oeis-a398920.lean) · [Lean statement](../../statements/oeis-a398920.lean)

## A395111 — Two conjectures about the same partition count

Let $A(n)$ count the partitions of $n$ into distinct positive parts whose radicals sum to $\mathrm{rad}(n)$, where the radical is the product of the distinct prime factors. Let $B(n)$ count partitions into distinct squarefree parts. The Lean theorem `original_partition_results` states both answers using the cardinalities of the actual sets of partitions. It proves that the recurrences count those sets by separating partitions according to whether they contain their largest permitted part.

### The two ranges differ

We have $A(44)=53$. Grouping the qualifying partitions by their largest part gives the counts below. The recurrence that certifies them considers each part at most once. For remaining total $n$, remaining radical sum $s$ and maximum part $j$, it adds the count omitting $j$ to the count at $(j-1,n-j,s-\mathrm{rad}(j))$ when both differences are nonnegative. At maximum part zero only the state $(0,0)$ counts.

| Largest part | 16 | 20 | 25 | 28 | 44 |
|---|---:|---:|---:|---:|---:|
| Qualifying partitions of 44 | 29 | 9 | 10 | 4 | 1 |

Here is a proof that $B(n)$ **never** equals 53. For $0\le n\le32$, the usual recurrence for distinct squarefree parts gives the following values.

```text
1 1 1 2 1 2 3 3 4 4 5 6 6 8 9 10 13
14 16 18 20 24 27 30 35 37 42 47 51 59 64 72 81
```

For $33\le n\le70$, using only the squarefree parts at most 18 gives at least 54 representations at each index. These bounds are coefficients of the finite product $\prod_{1\le j\le18,\ j\text{ squarefree}}(1+x^j)$ and are also verified by the Lean proof. Now use strong induction to prove that every $n\ge33$ has at least 54 representations with parts at most $\max(18,n-33)$. When $n\gt 70$, put $h=\lfloor(n-33)/2\rfloor$. Bertrand's postulate gives a prime $h\lt p\le2h$. Then $n-p\ge33$, $p\gt 18$ and $n-p-33\lt p$. Every one of the 54 guaranteed representations of $n-p$ uses parts strictly smaller than $p$. Appending $p$ gives 54 distinct squarefree partitions of $n$, with every part at most $\max(18,n-33)$. This proves the induction and excludes 53 from the entire range.

### The indices with a unique partition have density zero

Write each positive integer uniquely as $n=qm$ by collecting in $q$ the full powers of all primes whose exponent is at least two. Thus $m$ is squarefree, $\gcd(q,m)=1$, and $q$ is powerful, meaning all its positive prime exponents are at least two. The value $q=1$ is allowed.

Fix $q$ for the moment. We show that the exceptional squarefree $m$ coprime to $q$ for which $A(qm)=1$ have density zero. For any positive integer $K$, put $M=q(K!)^2$. Choose $M$ distinct primes larger than $q$. Among the $M+1$ partial sums beginning with zero, two agree modulo $M$. Their difference $s$ is a positive multiple of $M$ and a sum of a nonempty set of distinct primes $r_1,\ldots,r_j$, all coprime to $q$.

Take $m\gt s+\max r_i$. Since $q\mid s$, the remainder $m-s$ is coprime to $q$. For each prime $p\le K$, its square divides $s$, so $p^2$ cannot divide $m-s$ because $m$ is squarefree. If $m-s$ is squarefree, then
$qr_1,\ldots,qr_j,q(m-s)$
are distinct parts of $qm$. Their radicals sum to
$\mathrm{rad}(q)(r_1+\cdots+r_j+m-s)=\mathrm{rad}(q)m=\mathrm{rad}(qm)$.
This partition differs from the singleton $(qm)$.

Consequently, except for a fixed initial segment, every exceptional $m\le X$ has $p^2\mid m-s$ for some prime $p\gt K$. As $0\lt m-s\le X$, there are at most
$\sum_{p\gt K}\lfloor X/p^2\rfloor\le X\sum_{j\gt K}j^{-2}\le X/K$
such $m$. The upper density is at most $1/K$ for every $K$, and is therefore zero.

It remains to pass from fixed $q$ to all $n$. Every powerful $q$ has the form $u^2v^3$, by writing each exponent at least two as an even exponent or as three plus an even exponent. Thus
$\sum_{q\text{ powerful}}1/q\le(\sum_{u\ge1}u^{-2})(\sum_{v\ge1}v^{-3})\lt \infty$.
Integers $n\le X$ whose powerful part $q$ exceeds $Q$ number at most $X\sum_{q\gt Q,\ q\text{ powerful}}1/q$. For $q\le Q$ the finitely many exceptional sets have density zero by the argument for each fixed value of $q$. Letting $Q$ tend to infinity gives natural density zero for the whole exceptional set.

[Conjectures](https://oeis.org/A395111) · [Comparison sequence](https://oeis.org/A087188) · [Lean proofs of both claims](../../proofs/oeis-a395111.lean) · [Lean statement](../../statements/oeis-a395111.lean)

## A385590 — The Fibonacci triangle is a permutation

Every positive integer occurs in exactly one cell. To see how the blocks fit together, put $a=F_t$, $b=F_{t+1}$ and $c=F_{t+2}=a+b$, for $t\ge0$. Block $t$ consists of the rows of lengths $c,c+1,\ldots,c+b-1$. Its entries are

$$
s_t+ar+bj,\qquad s_t=b^2+(t\bmod2),\qquad 0\le r\lt b,\quad 0\le j\lt c+r.
$$

Consider the larger set $S_t=s_t+\lbrace au+bv:u,v\ge0\rbrace$. Since $b\gt 0$ and $a,b$ are coprime, every member has a unique representation $s_t+ar+bj$ with $0\le r\lt b$ and $j\ge0$. Existence follows by writing $u=bq+r$ and adding $aq$ to $v$. For uniqueness reduce modulo $b$ to recover $r$, then recover $j$ from equality of the integers.

Cassini's identity gives $s_{t+1}=s_t+bc$. In the canonical representation of $S_t$, the entries outside block $t$ are precisely those with $j=c+r+k$, $k\ge0$. They are

$$
s_t+ar+b(c+r+k)=s_{t+1}+cr+bk.
$$

As $0\le r\lt b$, these fill exactly $S_{t+1}$ by the same division argument, now with coefficients $c,b$. Thus block $t$ is exactly $S_t\setminus S_{t+1}$, with each member occurring once. The first tail $S_0$ is the set of all positive integers since $(s_0,a,b)=(1,0,1)$. Also $s_t\to\infty$. Every positive integer therefore leaves the nested tails at exactly one block, which proves both existence and uniqueness. The theorem `original_triangle_permutation` gives the result for the original formula on all positive row and column numbers with column at most row, including a proof that the source indexing and block indexing are equivalent.

The entry also asks for an alternating binomial sum. Each row is affine in the zero-based column $j$. For row length $n\ge3$, both the constant and linear terms vanish in its alternating binomial transform, by evaluating $(1-x)^{n-1}$ and its derivative at $x=1$. The two short rows give $-1$ and $1$. This identity already has a published Lean proof. That work explicitly excludes the permutation conjecture, which is the result counted here.

[Conjectures](https://oeis.org/A385590) · [Earlier work on the alternating sum](https://www.trureturing.org/research/oeis-a385590-alternating-binomial/) · [Lean proof](../../proofs/oeis-a385590.lean) · [Lean statement](../../statements/oeis-a385590.lean)

## A383702 — The recurrence for the quadratic coefficient

Let $P_n(x)=\prod_{i=0}^{n-1}(x+4i+3)$ and $a(n)=[x^2]P_n(x)$. Set $u=4n+3$. The polynomial identity

$$
P_{n+3}-3(u+4)P_{n+2}+(3u^2+12u+16)P_{n+1}-u^3P_n=x^3P_n
$$

follows by factoring out $P_n$ on the left and expanding the remaining cubic in $x$. The coefficient of $x^2$ on the right is zero. Taking the same coefficient on the left gives exactly R. J. Mathar's conjectured recurrence at index $n+3$, for every $n\ge0$. The displayed identity is also a direct certificate for D-finiteness. Robert Israel previously verified the analogous recurrence for A383700, which has factors starting at 1. This proof concerns the product starting at 3 in A383702.

[Conjecture](https://oeis.org/A383702) · [Related result for A383700](https://oeis.org/A383700) · [Lean proof](../../proofs/oeis-a383702.lean) · [Lean statement](../../statements/oeis-a383702.lean)

## A398343 — Each integer value occurs only finitely often

Write $k=\prod_{i=1}^r p_i^{e_i}$, with distinct primes and positive exponents. The sum of the radicals of the divisors is multiplicative because the radical is multiplicative on coprime integers. On a prime power $p^e$ this sum is $1+ep$. Thus the quotient in this sequence is

$$
Q(k)=\frac{\sum_{d\mid k}\mathrm{rad}(d)}{\mathrm{rad}(k)}
=\prod_{i=1}^r\left(e_i+\frac1{p_i}\right).
$$

Fix a positive integer $m$ and suppose $Q(k)=m$. Every $e_i$ is at most $m$, and if $h$ of the exponents are at least two, then $2^h\le\prod_i e_i\le m$. Among the remaining exponents, let $s$ be the number equal to one with $p_i$ odd. Each of these gives an even factor in $\prod_i(e_i p_i+1)=m\prod_i p_i$. The primes on the right are distinct, so $s\le v_2(m)+1$. At most one additional exponent belongs to $p_i=2$. This bounds the number of prime factors, including those that make factors arbitrarily close to one.

Now fix their number $r$ and order the primes increasingly. There are only finitely many possible exponent vectors. For any one such vector, the function $\prod_i(e_i+1/p_i)$ decreases strictly if any coordinate increases while the others stay fixed or increase. Its level set in positive integer vectors therefore contains no two distinct coordinatewise comparable vectors. By Dickson's lemma this level set is finite. Equivalently, every infinite sequence of natural numbers has an infinite nondecreasing subsequence, and applying this successively to each of the $r$ coordinates would give two comparable vectors. The empty vector accounts for $k=1$. Each vector determines $k$, proving the assertion for every $m$.

[Conjecture](https://oeis.org/A398343) · [Sequence choosing the eligible integers](https://oeis.org/A398342) · [Lean proof](../../proofs/oeis-a398343.lean) · [Lean statement](../../statements/oeis-a398343.lean)

## A398342 — A counterexample to the related least-multiple question

The source asks whether, for every odd prime $p$, each smaller prime divisor of the least qualifying multiple of $p$ divides $p-1$. The answer is **no for $p=107$**. This question occurs in the A398342 comments. Left to Solve has no separate entry for it.

Use the eligibility test $Q(k)\in\mathbb Z$ from the preceding proof. There is a qualifying multiple of 107 at

$$
K=549400309952=2^6\cdot13^4\cdot53^2\cdot107,\qquad Q(K)=54.
$$

The least qualifying multiple $t$ of 107 therefore exists and satisfies $t\le K$. It suffices to prove that **no qualifying multiple in that whole interval** has all its smaller prime factors in $\lbrace 2,53\rbrace$, the prime divisors of 106. This avoids any need to identify the least multiple numerically.

Suppose such an integer exists and write its low-prime part as $L=2^a53^b107^c$ and its other part as $\prod_{q\gt 107}q^{e_q}$. Here $a\lt 40$, $b\lt 7$, and $1\le c\lt 6$ by the size bound. Put $C=Q(L)$. If there are no high primes, exact division shows that $C$ is never integral among these triples with $L\le K$.

Otherwise let $P$ be the largest high prime. Because $Q(t)$ is integral, $P$ must divide some numerator factor $e_q q+1$. The finitely many low-prime numerator factors $2a+1$, $53b+1$, and $107c+1$ in the indicated ranges have all prime factors at most 107. Also $P$ cannot divide $e_PP+1$. Its source must therefore be another high prime $q\lt P$. Since both are odd, $q+1\lt P$, so $e_q\ge2$.

Write $r$ for the number of high primes, $s=\sum e_q$ and $E=\prod e_q$. Then $2\le r\lt s$, $L108^s\le K$, and $2\le E\le 2^{s-r}$, using $e\le2^{e-1}$ for positive $e$. In particular $s\le4$. Writing $m=Q(t)$ gives the interval

$$
CE\lt m\le CE(109/108)^r.
$$

The lower bound follows from $e_q+1/q\gt e_q$. For the upper bound every factor is at most $e_q(109/108)$. It remains a small exact certificate over **all** possible exponent patterns. The size bound implies $a\lt 13$, $b\lt 3$, $c\lt 3$. For each such triple with $c\gt 0$, each $2\le r\lt s\le4$ with $L108^s\le K$, and each $2\le E\le2^{s-r}$, integer division gives $\lfloor CE(109/108)^r\rfloor=\lfloor CE\rfloor$. Thus the interval contains no integer. The standalone Lean file verifies these divisions, the low-prime bounds, and the deductions covering every possible factorization. This forces some prime divisor $q\lt 107$ of the least multiple to fail $q\mid106$.

[Original question](https://oeis.org/A398342) · [Complete standalone Lean counterexample](A398342.lean) · [Axiom audit](verification/398342.txt)

## Verification

Each [checker verdict](verification) records a successful local run of the project’s `tools/check.sh` against its pinned formal-conjectures revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. For A395111 the main target is a conjunction, so the project audits the disproof. The separate [axiom audit for the density theorem](verification/395111-density.txt) checks its positive conclusion independently. The statement stubs retain the single placeholder required for human review. The proofs use only the standard Lean axioms listed in the verdicts.

The independent axiom reports also cover the theorems on the [original triangle indices](verification/385590-source.txt), the [infinite sequence of runs](verification/395088-source.txt), the [cardinalities of the sets of partitions](verification/395111-source.txt), and the [original set of positive quadruples](verification/398920-source.txt). Each uses only `propext`, `Classical.choice`, and `Quot.sound`.

A second run from a clean copy of the published proof and statement files passed for all eight problems. The [replay record](verification/replay.txt) gives the checked commit, SHA-256 digest of each proof, and axiom report.
