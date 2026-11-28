# A structural obstruction to upgrading logarithmic-density-one regularity

This is a countermodel for a proposed proof route, not a formula for the actual arithmetic-progression extremal function. Monotonicity, subadditivity, a no-carry product lower bound, a local increment inequality, Behrend-scale density loss, and a logarithmic-density-one linear profile do not together imply regular variation at every scale.

All arguments below are ordinary mathematical proofs. This complete construction has not been formalized in Lean. Numerical checks, supplied separately, are checks on the formulas and are not substitutes for the proofs.

## Construction

For a real number `t >= 0`, put `n = floor(sqrt(t))` and define

\[
h(t)=n+\min(t-n^2,1).
\]

Thus `h` rises with slope one on each interval `[n^2,n^2+1]` and is constant until the next such interval. The first two rising intervals meet, so `h(t)=t` for `0 <= t <= 2`.

For `x >= 1` define

\[
f(x)=x\,2^{-h(\log_2 x)/16},
\qquad G(N)=\lceil f(N)\rceil\quad(N\ge1),
\qquad G(0)=0.
\]

The logarithm in the definition has base two. Unsubscripted logarithms below are natural logarithms.

## Smoothing identity and subadditivity of h

There is an exact identity

\[
h(t)=\min_{0\le u\le t}\bigl(\lceil\sqrt u\rceil+t-u\bigr).
\tag{1}
\]

Write `t=n^2+s`, with `0 <= s < 2n+1`. The choices `u=n^2` and `u=t` give the values `n+s` and `n+1` when `s>0`, respectively, and give `n` when `s=0`. For `u<n^2`, put `m=ceil(sqrt(u)) <= n`; then `u <= m^2`, and

\[
m+t-u\ge m+t-m^2\ge n+t-n^2,
\]

because the difference in the final inequality is `(n-m)(n+m-1) >= 0`. For `u>n^2`, the expression is at least `n+1`. This proves (1), including `0 <= t < 1`.

The function `g(u)=ceil(sqrt(u))` is subadditive: `sqrt(u+v) <= sqrt(u)+sqrt(v) <= g(u)+g(v)`, and the final expression is an integer. Choose minimizers `u` and `v` in (1) for inputs `a` and `b`. Their sum is an admissible choice for `a+b`, so

\[
\begin{aligned}
h(a+b)
&\le g(u+v)+a+b-u-v\\
&\le g(u)+a-u+g(v)+b-v\\
&=h(a)+h(b).
\end{aligned}
\]

The same representation proves that `h` is increasing and 1-Lipschitz. If `s <= t`, a minimizer for `s` gives `h(t) <= h(s)+(t-s)`. Conversely, every candidate `u <= t` has cost at least `h(s)`: for `u <= s` compare the two costs directly; for `u>s` use `g(u) >= g(s) >= h(s)`.

Also `h(0)=0`, `h(t) <= t`, and for `t >= 1`,

\[
\sqrt t\le h(t)\le\sqrt t+1.
\tag{2}
\]

For the lower bound in (2), if `s <= 1` then `(n+s)^2 >= n^2+s` since `n>=1`; if `s>=1`, then `h(t)=n+1 >= sqrt(t)`. The upper bound follows directly from `h(t)<=n+1`.

## Properties of the real function

For `1 <= x <= y`, monotonicity and the Lipschitz bound give

\[
\left(\frac yx\right)^{15/16}
\le\frac{f(y)}{f(x)}\le\frac yx.
\tag{3}
\]

Consequently `f` is increasing, `f(x)/x` is decreasing, and `f(x)>=x^(15/16)`. Decreasing density gives subadditivity:

\[
f(x+y)\le f(x)+f(y)\qquad(x,y\ge1).
\]

Subadditivity of `h` gives supermultiplicativity:

\[
f(xy)\ge f(x)f(y)\qquad(x,y\ge1).
\]

Equation (2) gives, for `x >= 2`,

\[
2^{-1/16}x\,2^{-\sqrt{\log_2 x}/16}
\le f(x)\le x\,2^{-\sqrt{\log_2 x}/16}.
\tag{4}
\]

Equivalently the varying density factor is `exp(-sqrt(log(2))*sqrt(log(x))/16)`, up to the displayed fixed factor. Thus `f(x)=o(x)` and `f(x)=x^(1-o(1))`. It is compatible asymptotically with every upper bound `x exp(-C(log x)^gamma)` having fixed `gamma<1/2` and fixed `C>0`.

The local modulus is even stronger than the one needed here:

\[
0\le f(N+H)-f(N)\le\frac HN f(N).
\tag{5}
\]

## Exact integer properties

The sequence `G` is increasing, integer-valued, and satisfies

\[
G(0)=0,\quad G(1)=1,\quad 1\le G(N)\le N,
\quad G(N+1)-G(N)\in\{0,1\}.
\]

The final assertion follows from (5), since `f(N+1)-f(N)<=f(N)/N<=1`; the case `N=0` is explicit.

Subadditivity survives ceiling exactly:

\[
G(M+N)\le G(M)+G(N).
\tag{6}
\]

We do **not** claim that ceiling preserves direct supermultiplicativity. The following slightly weaker product inequality does hold:

\[
G(2MN)\ge G(M)G(N).
\tag{7}
\]

For a proof, first note the uniform estimate

\[
G(N)\le\frac54 f(N)\qquad(N\ge1).
\tag{8}
\]

If `N<=4`, use `G(N)<=N`, `f(N)>=N^(15/16)`, and `4^(1/16)<5/4`. If `N>=5`, then `f(N)>=5^(15/16)>4`, so `G(N)<f(N)+1<(5/4)f(N)`. Now (3), real supermultiplicativity, and `2^(15/16)>25/16` imply

\[
f(2MN)\ge2^{15/16}f(M)f(N)\ge G(M)G(N),
\]

which proves (7). Zero cases in (7) are immediate.

A stronger bound relevant to the existing local-modulus note is

\[
G((2m-1)H)\ge G(m)G(H)\qquad(m,H\ge1).
\tag{9}
\]

For `m>=3`, use

\[
\begin{aligned}
f((2m-1)H)
&\ge\left(\frac{2m-1}{m}\right)^{15/16}f(mH)\\
&\ge(5/3)^{15/16}f(m)f(H)\\
&\ge(25/16)f(m)f(H)\\
&\ge G(m)G(H).
\end{aligned}
\]

Here `(5/3)^(15/16)>25/16`. For `m=2`, use `G(2)=2`, `f(3H)>=f(3)f(H)`, and `f(3)=3^(15/16)>5/2`; the last equality uses `log_2(3)<2` and `h(t)=t` on `[0,2]`. For `m=1`, (9) is equality.

Combining (6) and (9) proves the exact self-referential local modulus

\[
(2m-1)H\le N
\quad\Longrightarrow\quad
G(m)\bigl(G(N+H)-G(N)\bigr)\le G(N)
\tag{10}
\]

for all positive integers `m,H,N`; zero cases are immediate where defined. This has the same shape as the existing inequality for `r_3`. It uses `G(m)`, **not the actual unknown extremal function** `r_3(m)`.

## Failure of regular variation on exact integer scales

Put `N_j=2^(j^2)` and `M_j=2^(j^2+1)`. These are integers. For every integer `j>=1`,

\[
\frac{f(2N_j)}{f(N_j)}=2^{15/16},
\qquad
\frac{f(2M_j)}{f(M_j)}=2.
\tag{11}
\]

Thus even the fixed doubling ratio has no limit. Since `f(N)->infinity`, ceiling gives `G(N)/f(N)->1`. Therefore

\[
\frac{G(2N_j)}{G(N_j)}\longrightarrow2^{15/16},
\qquad
\frac{G(2M_j)}{G(M_j)}\longrightarrow2.
\]

At the end of each ramp there is also a fixed full-profile defect:

\[
\frac{f(N_j)}{f(M_j)}-\frac{N_j}{M_j}
=\frac{2^{1/16}-1}{2}>0.0221.
\tag{12}
\]

Ceiling preserves this discrepancy asymptotically.

## Full normalized profile at logarithmic density one

Define

\[
D_f(N)=\sup_{1\le x\le N}
\left|\frac{f(x)}{f(N)}-\frac{x}{N}\right|.
\]

Write `t=log_2(N)` and `y=log_2(N/x)`. Since the density is decreasing, the discrepancy is nonnegative and equals

\[
2^{-y}\left(2^{(h(t)-h(t-y))/16}-1\right)
\le2^{-15y/16}.
\tag{13}
\]

Fix `epsilon>0` and choose `L>0` with `2^(-15L/16)<=epsilon/2`. If `t>=L` and the interval `[t-L,t]` meets no ramp `[j^2,j^2+1]`, then `h` is constant on that interval. Formula (13) gives `D_f(N)<=epsilon/2`: short windows have zero defect, and longer windows have exponentially suppressed defect.

Therefore every exceptional logarithmic endpoint `t` is contained in an initial bounded interval or in

\[
\bigcup_{j\ge0}[j^2,j^2+1+L].
\]

The measure of this union below `T` is at most `(L+1)(sqrt(T)+1)`, up to the initial interval. Passing to integer endpoints uses the elementary bound

\[
\sum_{2^a\le N\le2^b}\frac1N
\le(b-a)\log2+2^{-a}\qquad(0\le a\le b),
\]

and summing the `2^(-j^2)` terms is finite. Consequently

\[
\sum_{\substack{1\le N<X\\D_f(N)>\epsilon}}\frac1N
=O_\epsilon(\sqrt{\log X}).
\tag{14}
\]

For the integer sequence define

\[
D_G(N)=\max_{x\in\{0,\ldots,N\}}
\left|\frac{G(x)}{G(N)}-\frac xN\right|.
\]

The ceiling errors satisfy, uniformly in `1<=x<=N`,

\[
\left|\frac{G(x)}{G(N)}-\frac{f(x)}{f(N)}\right|\le\frac1{f(N)}.
\]

Indeed, write `G(x)=f(x)+a` and `G(N)=f(N)+b`, with `0<=a,b<1`; the numerator of the difference is `a f(N)-b f(x)`, whose absolute value is at most `f(N)` because `0<=f(x)<=f(N)`. Since `f(N)->infinity`, (14) also holds with `D_G` in place of `D_f`, after adjusting the constant.

### The square-root exceptional-mass rate is attained

There is also a matching lower bound for one fixed positive tolerance. For integer `j>=2` and `t=j^2+s` with `1/2<=s<=1`, take `N=2^t` and `x=N/2`. Then `h(t)=j+s` and `h(t-1)=j`, so

\[
\frac{f(N/2)}{f(N)}-\frac12
=\frac{2^{s/16}-1}{2}
\ge d_0:=\frac{2^{1/32}-1}{2}>0.
\]

For integer `N` in the same dyadic interval, use `x=floor(N/2)`. Monotonicity and (5) give `|f(x)-f(N/2)|<=1`; including the ceiling error and the change in `x/N` changes the discrepancy by at most `3/f(N)`. Thus, for all sufficiently large such integers, `D_G(N)>d_0/2`.

Every interval

\[
\left[2^{j^2+1/2},2^{j^2+1}\right]
\]

therefore consists of exceptional integer endpoints once `j` is large. Its harmonic mass tends to `(log 2)/2`; in particular it is bounded below by a positive constant. There are order `sqrt(log X)` disjoint such intervals below `X`. With the fixed tolerance `epsilon_0=d_0/2`, this proves

\[
\sum_{\substack{1\le N<X\\D_G(N)>\epsilon_0}}\frac1N
=\Theta(\sqrt{\log X}).
\tag{15}
\]

Thus the abstract structural assumptions listed here do not even force an improvement on the square-root order of the exceptional logarithmic mass.

## Scope

An argument using only the properties proved above cannot upgrade logarithmic-density-one profile regularity to regular variation for every endpoint. The countermodel has all these properties and fails that conclusion. This does not rule out a theorem exploiting additional arithmetic-progression structure.

The sequence `G` is not the actual extremal function: already `G(3)=3`, whereas `r_3(3)=2`. It has not been shown to obey every known inequality for progression-free sets; only the inequalities explicitly proved above are claimed. Its local modulus involves its own `G(m)`, not `r_3(m)`.

Even a proof of regular variation for the actual `r_k` would still leave the slowly varying density factor undetermined. It would not by itself supply the ratio-one formula requested in Erdős 142.
