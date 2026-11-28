# An arithmetic input that would establish scale regularity

This note isolates an unproved sufficient hypothesis. It is not a proof of that hypothesis, and even proving it would not determine the explicit asymptotic density required by Erdős 142.

Let `r(N)=r_3(N)` be the maximum size of a subset of `{1,...,N}` with no nontrivial three-term arithmetic progression. For odd positive `N`, let `R(N)` be the maximum size of a subset `S` of `Z/NZ` such that `x+z=2y` with `x,y,z` in `S` implies `x=y=z`.

## Missing arithmetic hypothesis

The following comparison would suffice for regular variation:

\[
\boxed{\displaystyle
\frac{R(N)}{r(N)}\longrightarrow1
\quad\text{as odd }N\longrightarrow\infty.}
\tag{H}
\]

**Status: unproved in this investigation.** The scalar structural inequalities and near-extremizer interval equidistribution do not establish (H). No claim is made that (H) is necessary or an easier open problem than regular variation itself.

There is always `R(N)<=r(N)`: representatives of a cyclic progression-free set form an interval progression-free set. The elementary reverse embedding only gives `R(2N+1)>=r(N)`. Indeed, for `a,b,c` in `{1,...,N}`, the integer `a+c-2b` has absolute value less than `2N+1`, so a congruence to zero modulo `2N+1` is an actual equality. This reverse embedding changes the scale and does not prove (H).

## Elementary gluing implication

For every odd positive `N`,

\[
r(2N)\ge2R(N).
\tag{1}
\]

Take a cyclic extremizer `S` and let `B` consist of every integer in `{1,...,2N}` whose residue belongs to `S`. Each residue occurs twice, so `|B|=2|S|`.

If `a,a+d,a+2d` were a three-term progression in `B`, then `d>=1` and `2d<=2N-1`, hence `d<N`. Its common difference is nonzero modulo `N`. Since `N` is odd, the three residues are distinct and form a forbidden progression in `S`. Thus `B` is interval progression-free, proving (1).

Interval splitting gives `r(2N)<=2r(N)`. Consequently (H) would give

\[
\frac{r(2N)}{r(N)}\longrightarrow2
\tag{2}
\]

first along odd `N`. It would also hold along even `N`, because `r(N)-r(N-1)<=1`, `r(N)->infinity`, and

\[
r(2N)\ge r(2N-2)=(2-o(1))r(N-1)=(2-o(1))r(N).
\]

## From doubling regularity to the entire interval profile

This implication uses only subadditivity, monotonicity, increments at most one, and unboundedness of `r`.

Assume (2). Fix a power of two `B=2^w`. Iterating the doubling estimate for this fixed number of steps gives

\[
A_H:=\frac{r(BH)}{B r(H)}\longrightarrow1
\qquad(H\longrightarrow\infty),
\]

and subadditivity gives `A_H<=1`. For any integer `0<=x<=BH`, put `q=floor(x/H)`. Splitting into intervals of length at most `H` gives

\[
r(x)\le(q+1)r(H),
\qquad r(x)\ge r(BH)-(B-q)r(H).
\]

Since `q/B<=x/(BH)<=(q+1)/B`, these imply

\[
\sup_{0\le x\le BH}
\left|\frac{r(x)}{r(BH)}-\frac{x}{BH}\right|
\le\left(\frac1{A_H}-1\right)+\frac1{B A_H}.
\tag{3}
\]

For arbitrary `N`, choose `H=floor(N/B)` and `N_0=BH`, so `0<=N-N_0<B`. The bounds `0<=r(N)-r(N_0)<=B` and `r(N)->infinity` show that replacing `N_0` by `N` changes the normalized profile by at most `B/r(N)+B/N`. Thus the limsup of the full profile error is at most `1/B`. Letting the fixed dyadic `B` grow proves

\[
\sup_{0\le x\le N}
\left|\frac{r(x)}{r(N)}-\frac{x}{N}\right|
\longrightarrow0.
\tag{4}
\]

Taking `x=floor(lambda N)` gives `r(floor(lambda N))/r(N)->lambda` for `0<lambda<=1`. For `lambda>1`, apply (4) at `M=floor(lambda N)` with `x=N` and invert the resulting positive ratio. Hence `r` would be regularly varying with index one at every endpoint.

## Finite obstruction to exact cyclic equality

An exact finite comparison is false: `r(5)=4`, witnessed by `{1,2,4,5}`, while `R(5)=2`.

To see the cyclic upper bound, any three residues can be sent by an affine automorphism of `Z/5Z` to `{0,1,c}` with `c` equal to `2`, `3`, or `4`. These contain, respectively, the progressions `(0,1,2)`, `(0,3,1)`, and `(4,0,1)`. Every two-element set is free because a nontrivial three-term progression modulo five has three distinct points. This establishes `R(5)=2`.

This example does not refute the asymptotic hypothesis (H); it prevents replacing it by an exact equality without proof.

## The missing additive information

Uniform prefix counts control one-point spatial marginals. Doubling an interval set introduces wraparound equations

\[
a+c-2b=\pm N
\]

that are absent from the original interval prohibition. The number and arrangement of such triples are not determined by prefix counts. A successful gluing argument must control these higher-order additive correlations, or construct cyclic sets by another method.

Finally, (4) would say that the unknown factor `r(N)/N` varies slowly under fixed dilations. It would not identify that factor. The ratio-one asymptotic sought in Erdős 142 would remain an additional problem.
