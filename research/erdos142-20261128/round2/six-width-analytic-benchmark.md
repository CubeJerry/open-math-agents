# Exact free-intercept six-width benchmark

**Status.** The profiles and area below have an elementary exact feasibility proof. They are continuous profiles, so the bounded-potential block is obtained by the finite-layer approximation in the last section. The argument does not solve the ratio-one asymptotic problem for `r_3(N)`. No novelty claim is made against the unavailable original profiles from team note 41051.

## Profiles

Set

$$
p=\frac65,\qquad q=\frac9{10},\qquad w=\frac{17}{140},\qquad b=\frac5{12}.
$$

For `0<s<1/2`, put

$$
L(s)=ps,\qquad W(s)=\min(w+qs,1-ps).
$$

The lower angular slice is `(-L(s)/2,W(s)/2)`. For `0<t<b`, put

$$
\begin{aligned}
U(t)&=1-2pt,\\
P_0(t)&=2w+q-1+2qt, &P(t)&=\min(U(t),P_0(t)),\\
V_1(t)&=1-2w-2qt, &V_0(t)&=(2-U(t)-P_0(t))/2,\\
V(t)&=\min(V_1(t),V_0(t)),\\
M_0(t)&=p-1+2pt, &M(t)&=\min(V(t),M_0(t)).
\end{aligned}
$$

At height `s=1/2+t`, use the upper angular slice

$$
\left(\frac14-\frac{V(t)}4,\frac14+\frac{P(t)}4\right)
\mathbin{\cup}
\left(-\frac14-\frac{M(t)}4,-\frac14+\frac{U(t)}4\right).
$$

The exact switching points are

$$
m=\frac{16}{147}<v=\frac{23}{147}<c=\frac{10}{49}
<b=\frac5{12}<h=\frac{41}{98}<\frac12.
$$

Here `W=w+qs` until `h`, then `W=1-ps`; `P=P_0` until `c`, then `P=U`; `V=V_0` until `v`, then `V=V_1`; and `M=M_0` until `m`, then `M=V_0` until `v`, then `M=V_1`. Every width lies in `[0,1]`. For example, `P_0(0)=1/7`, `V_0(0)=3/7`, `M_0(0)=1/5`, and `V_1(b)=1/140>0`.

The intercept `w` is independent of `p,q`. Forcing the lower crossover `h` to equal the upper cutoff `b` removes the small improvement obtained here.

## Exact feasibility for every continuous height pair

The sufficient conditions are those independently derived in `six-width-geometry.md`.

Within a lower slice, `L+W<=1`. Within an upper slice, `P<=P_0`, `V<=V_0` and `M<=V`, so

$$
P+U+2V\le P_0+U+2V_0=2,
\qquad P+U+2M\le2.
$$

For two lower heights `a,z` whose upward midpoint has upper offset `t=(a+z)/2<b`, use `P<=U` and the linearity of `L`:

$$
L(a)+L(z)+\max(P(t),U(t))
=2pt+U(t)=1.
$$

The minimum of two affine functions is concave, so `W(a)+W(z)<=2W(t)`. Since `t<b<h`, `W(t)=w+qt`; and `M<=V<=V_1` gives

$$
W(a)+W(z)+\max(V(t),M(t))
\le2(w+qt)+V_1(t)=1.
$$

For a lower height `a` and upper endpoint offset `c_0`, the upward midpoint offset is

$$
t=\frac14+\frac{a+c_0}{2}<b.
$$

Consequently `a+c_0<2b-1/2=1/3<b<h`; in particular `W(a)=w+qa`. Both mixed constraints follow from exact affine identities:

$$
\begin{aligned}
P(c_0)+2W(a)+2\max(V(t),M(t))
&\le P_0(c_0)+2(w+qa)+2V_1(t)=1,\\
M(c_0)+2L(a)+2\max(U(t),P(t))
&\le M_0(c_0)+2pa+2U(t)=1.
\end{aligned}
$$

Thus all local, lower/lower, and lower/upper inequalities hold for all real heights. This is stronger than a check at sampled midpoint nodes.

## Exact area and optimization of the intercept

The area is

$$
A=\frac12\int_0^{1/2}(L+W)\,ds
+\frac14\int_0^b(U+P+V+M)\,dt.
$$

For general `p,q,w` in the same switching regime, with `b=1/(2p)`,

$$
A_L=\frac14-\frac{(1-w)^2}{4(p+q)}.
$$

Integrating the upper pieces at

$$
m=\frac{2-p-q/2-w}{p+q},\quad
v=\frac{q/2-w}{p+q},\quad
c=\frac{1-q/2-w}{p+q}
$$

gives

$$
A=-\frac{4p^4+4p^3q+8p^3w-24p^3+5p^2q^2+4p^2qw-24p^2q
+28p^2w^2-32p^2w+20p^2+16pqw-8pq+4q^2}{32p^2(p+q)}.
$$

This is a strictly concave quadratic in `w`; its maximizer is

$$
w_* =\frac{p(8-2p-q)-4q}{14p}.
$$

At `p=6/5,q=9/10`, this is `17/140` and

$$
\boxed{A=\frac{14303}{47040}=0.30406037414965986\ldots.}
$$

The difference from team note 110197's numerical claim is exactly

$$
\frac{14303}{47040}-\frac{25541}{84000}=\frac1{1176000}>0.
$$

The cited earlier value is treated only as a comparison number, not as a verified construction. A nearby rational choice

$$
p=\frac{211}{175},\quad q=\frac{158}{175},\quad w=\frac{6242}{51695}
$$

has the same feasibility argument and area

$$
\frac{16317762989}{53665613400}=0.30406366302709587\ldots.
$$

Its switching points are `57410/545013`, `9497/60557`, `110582/545013`, followed by `b=175/422` and `h=75755/181671`, in strictly increasing order. The approximate stationary maximum of this three-parameter family is `0.3040636641862076` at `p=1.2055953978708467`, `q=0.9028486822158846`, `w=0.1207451826419701`. The numerical stationarity calculation is not a global optimality certificate.

The exact formulas and symbolic integrations are reproducible with `derive_six_width_free_intercept.py`.

## Finite layers with an explicit approximation bound

The continuous profiles do not by themselves certify a uniformly bounded Jensen potential. Form a genuine finite-layer block as follows. Let `D` be divisible by 12, so both `1/2` and `b=5/12` are grid boundaries. On each grid cell, replace each width by its infimum over that cell. Each resulting angular slice is contained in every original slice of the same type at a height in the cell. The continuous inequalities therefore imply all finite-cell local and midpoint constraints: for any reachable triple of cells, choose heights realizing the indicated midpoint and compare the infima with the original widths at those heights.

The Lipschitz constants of `L,W,U,P,V,M` can respectively be taken as

$$
6/5,\quad6/5,\quad12/5,\quad12/5,\quad9/5,\quad12/5.
$$

For a `K`-Lipschitz function on a cell of length `1/D`, the integral minus cell length times its infimum is at most `K/(2D^2)`: choose a point of minimum and integrate the Lipschitz bound on the two sides. Summing with the area weights above gives the exact estimate

$$
0\le A-A_0\le\frac{123}{160D}.
$$

Now remove a gap of total width `g=1/(100D^2)` from each cell, half at each end. The block area is

$$
A_g=(1-Dg)A_0
\ge A-\frac{123}{160D}-\frac{A}{100D}
> A-\frac{623}{800D},
$$

where the last step only uses `A<1`. The potential proved in `six-width-geometry.md` is bounded by `C+1`, with `C=2+6/g^2`. Every parameter is rational and the number of layers is finite.

For the concrete choice `D=1200000`,

$$
A_g>\frac{4767656491}{15680000000}
=0.3040597251913265\ldots
>\frac{25541}{84000},
$$

with the latter difference exactly `9473/47040000000`.

More generally, `D` can tend to infinity, so bounded-potential finite-layer blocks approach `14303/47040` from below. An analogous approximation works for the nearby stronger rational benchmark. The tensor/shell/slope transfer must still be applied, together with an exact finite-grid point-count certificate, before stating a formal lower-bound theorem for integers. Assuming that separately established transfer, the limiting natural-log leading constant corresponding to the simple benchmark area is `2 sqrt(log(47040/14303)) = 2.182227300826024...`; this is a lower-bound construction constant, not a ratio-one asymptotic formula.

## A sufficient nonlinear extension

If `L,W` are concave lower profiles and `L+W<=1`, retain `P<=U<=1-2L(t)` and `M<=V<=1-2W(t)`. Let `A_b=2b-1/2`. For a concave function `f`, with `t=1/4+(a+c_0)/2`, the function

$$
a\longmapsto4f(t)-2f(a)
$$

is nonincreasing whenever `0<=a<=A_b-c_0`, because `t>=a` and concave slopes decrease. Its minimum is attained when `t=b`. Thus it suffices to impose

$$
P(c_0)\le4W(b)-2W(A_b-c_0)-1,\qquad
M(c_0)\le4L(b)-2L(A_b-c_0)-1
$$

for `0<=c_0<=A_b`. These become the affine formulas above when the relevant lower profiles are affine. They offer an exact way to test concave piecewise-linear extensions without missing intermediate real height pairs.

## Numerical search of kink extensions

The scripts `search_concave_six_width.py` and `search_two_kink_six_width.py` optimize one concave kink in `L`, or independent concave kinks in both `L` and the initially affine branch of `W`. They integrate the resulting piecewise-affine envelopes exactly in real arithmetic, implemented with floating arithmetic. Five local starts and a differential-evolution run in each family returned the same area `0.3040636641862076`, with the active kink amplitudes tending to zero or the kinks moving beyond the portion where they affect the block.

The further script `search_nonconcave_six_width.py` allows either sign of each kink. It replaces the concavity shortcut by the exact piecewise-affine envelope

$$
S_f(t)=\max_{a+z=2t}\bigl(f(a)+f(z)\bigr).
$$

The maximum occurs when one endpoint is a breakpoint of `f`, so it is a finite upper envelope of affine pieces. The mixed constraints are similarly obtained as finite lower envelopes, with extrema when a lower endpoint or an upper midpoint is at a profile breakpoint. Four local starts again returned the affine optimum, and all tested one-sided kink derivatives in the active range were negative. These computations are evidence against this restricted kink search, not a global upper bound for the six-width family. The successful subsequent extension uses a new patch in a triangular sumset hole and a potential depending on one of its barycentric coordinates; see `triangle-hole-potential-extension.md`.
