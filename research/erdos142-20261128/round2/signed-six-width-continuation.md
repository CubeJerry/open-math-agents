# Signed six-width profiles and an exact optimized area

**Verified mathematical conclusion.** The six-width construction remains valid when its angular widths are signed, provided the actual intervals have nonnegative length and the same linear exclusion inequalities hold. This removes an artificial truncation of the previous analytic profile. The resulting finite-layer bounded-potential blocks have areas approaching

$$
\boxed{E_* = \frac{17-6\sqrt2}{28}
=0.304097093777193918\ldots.}
$$

The optimization below is exact in the stated switching regime. It is not an upper bound for all torus blocks, nor a ratio-one asymptotic formula for `r_3(N)`.

## 1. The signed geometric conditions

In each lower height cell, use the angular interval

$$
A=(-L/2,W/2).
$$

In each upper height cell, use

$$
B^+=(1/4-V/4,1/4+P/4),\qquad
B^-=(-1/4-M/4,-1/4+U/4).
$$

All six parameters may lie in `[-1,1]`. Require `0≤L+W≤1`, `P+V≥0`, and `M+U≥0`; a zero-length interval is empty. These conditions allow a slice to move away from the nominal centers `0` or `±1/4`.

Retain the local conditions

$$
P+U+2V\le2,\qquad P+U+2M\le2.
\tag{Local}
$$

For two lower endpoint cells with an upward upper midpoint, retain

$$
L_i+L_j+\max(P_t,U_t)\le1,
\qquad W_i+W_j+\max(V_t,M_t)\le1.
\tag{LL}
$$

For a lower endpoint cell `i`, upper endpoint cell `j`, and upward upper midpoint cell `t`, retain

$$
P_j+2W_i+2\max(V_t,M_t)\le1,
\qquad M_j+2L_i+2\max(P_t,U_t)\le1.
\tag{LH}
$$

Each maximum can be expanded into two linear inequalities, exactly as in the earlier nonnegative-width LP. The list of possible target height cells is unchanged.

### Upward-midpoint exclusion, with all signs checked

Write `R=max(P_t,U_t)` and `S=max(V_t,M_t)` for the target upper slice. Its doubled angular coordinates, and their integer translates, lie in the bands centered at half-integers with left radius `S/2` and right radius `R/2`. Thus the central open interval

$$
(-1/2+R/2,\ 1/2-S/2)
\tag{Gap}
$$

avoids them. Signed widths do not change this observation: the actual positive angular arc is contained in `(0,1/2)` and the negative arc in `(-1/2,0)`, by the upper caps on the four widths and their positive actual lengths.

For (LL), the endpoint angular sum lies in `(-(L_i+L_j)/2,(W_i+W_j)/2)`, which the two inequalities place inside (Gap).

For (LH), the two possible endpoint-sum intervals have endpoints

$$
\left(\frac14-\frac{2L_i+V_j}{4},\frac14+\frac{2W_i+P_j}{4}\right),
\quad
\left(-\frac14-\frac{2L_i+M_j}{4},-\frac14+\frac{2W_i+U_j}{4}\right).
$$

The upper endpoint of the first interval is at most `1/2−S/2`, and its lower endpoint is at least

$$
\frac R2+\frac{M_j-V_j}{4}\ge-\frac12+\frac R2.
$$

The lower endpoint of the second interval is at least `−1/2+R/2`, and its upper endpoint is at most

$$
-\frac S2+\frac{U_j-P_j}{4}\le\frac12-\frac S2.
$$

Only `V_j−M_j≤2` and `U_j−P_j≤2` are used in these auxiliary bounds. The signed caps supply both. Consequently both intervals lie inside (Gap), proving exclusion. Open endpoints handle equality in the linear constraints.

Two upper endpoints cannot have an upward vertical midpoint in the height range `(0,1)`, so these are all upward cases.

### Within-cell Jensen inequality

For a lower point put `u=a`. Its angular interval has length at most `1/2`, so a modular midpoint within the same interval is ordinary and

$$
u_x^2+u_z^2-2u_y^2=(a_x-a_z)^2/2.
$$

For upper points put `u=a−1/2` on `B^+`, and `u=a` on `B^-`. Both folded arcs lie in `(-1/2,0)`. With equal endpoint labels, the folded midpoint is ordinary. With different endpoint labels, the modular discrepancy is `±1/2`; (Local) excludes `+1/2`, regardless of the signs of `P,U,V,M`. The surviving discrepancy `−1/2` obeys

$$
4\bigl(u_x^2+u_z^2-2u_y^2\bigr)\ge(a_x-a_z)^2,
$$

by the same direct square computation as in `six-width-geometry.md`.

After inserting a vertical gap of size `g>0` between distinct retained height cells, the complete potential is

$$
F(s,a)=Cs^2+4u^2,\qquad C\ge2+6/g^2.
$$

For endpoints in different cells, the vertical quadratic has enough curvature to pay the worst negative angular contribution. Downward vertical wraps have positive curvature at least `1/2`. Same-cell ordinary vertical midpoints use the angular inequality just proved. The potential is nonnegative and bounded by `C+1`, exactly as in the nonnegative-width construction.

## 2. Continue the analytic profile to its true endpoint

Let

$$
b=\frac1{2p},\qquad h=\frac{1-w}{p+q}.
$$

On lower heights `0<s<1/2`, use

$$
L(s)=ps,\qquad W(s)=\min(w+qs,1-ps).
$$

On the entire upper offset range **`0<t<h`**, use

$$
\begin{aligned}
U(t)&=1-2pt,\\
P_0(t)&=2w+q-1+2qt,& P(t)&=\min(U(t),P_0(t)),\\
V_1(t)&=1-2w-2qt,& V_0(t)&=(2-U(t)-P_0(t))/2,\\
V(t)&=\min(V_1(t),V_0(t)),\\
M_0(t)&=p-1+2pt,& M(t)&=\min(V(t),M_0(t)).
\end{aligned}
$$

Assume the switching regime

$$
0<m<v<c<b<h<1/2,
$$

where

$$
m=\frac{2-p-q/2-w}{p+q},\quad
v=\frac{q/2-w}{p+q},\quad
c=\frac{1-q/2-w}{p+q},
$$

and, as holds at the explicit parameters below, `1<p<2`, `0<q<p`, `w>0`, and `2w+q−1≥0`.

For `b<t<h`, the formulas simplify to

$$
P(t)=U(t)=1-2pt<0,
\qquad V(t)=M(t)=1-2w-2qt>0.
$$

Nevertheless, both actual upper arcs remain nonempty because

$$
P(t)+V(t)=M(t)+U(t)
=2(p+q)(h-t)>0.
$$

The earlier cutoff at `b` discarded these valid moving arcs.

All local inequalities hold because `P≤P_0`, `V≤V_0`, and `M≤V`. For a lower/lower upward midpoint with upper offset `t<h`, linearity of `L` and concavity of `W` give

$$
L(a)+L(z)+U(t)=1,
\qquad W(a)+W(z)+V(t)\le2(w+qt)+V_1(t)=1.
$$

For a mixed upward midpoint `t=1/4+(a+c_0)/2<h`, one has

$$
a<2h-1/2<h,
$$

so `W(a)=w+qa`. The two exact affine identities are unchanged:

$$
P_0(c_0)+2W(a)+2V_1(t)=1,
\qquad M_0(c_0)+2L(a)+2U(t)=1.
$$

Together with `P≤U` and `M≤V`, these prove all (LL) and (LH) inequalities for every real height pair, including targets above `b`.

The signed caps also hold. The lower widths remain positive and below 1. The functions `V,M` are positive and below `V_1(0)<1`. The functions `P,U` are at most 1 and are bounded below by `U(h)=1−2ph>−1`, since `p<2` and `h<1/2`.

## 3. Exact area

Let `A(p,q,w)` denote the previously integrated area truncated at `b`, as in `six-width-analytic-benchmark.md`. The total angular width on `b<t<h` is

$$
\frac{P+V+M+U}{4}=(p+q)(h-t).
$$

Hence the continued area is

$$
E=A+\frac{p+q}{2}(h-b)^2.
$$

Direct integration over the full range, without using the earlier truncated formula, gives

$$
E=-\frac{4p^2+4pq+8pw-24p+5q^2+4qw-24q+12w^2-16w+16}
{32(p+q)}.
$$

The standalone script `derive_signed_six_width.py` integrates the actual piecewise-affine profiles to `h`, checks this expression, and checks the square identity below symbolically.

For each fixed parameter point, finite constant-cell inner approximations with positive vertical gaps approach this area. To keep every retained arc strictly nonempty, first truncate the upper range at `h−η`, then approximate the six Lipschitz functions by their cellwise infima on a sufficiently fine mesh. Every exclusion inequality is preserved because all its width coefficients are nonnegative. The discarded strip, the uniform approximation error, and the gaps all tend to zero. This supplies genuinely bounded-potential finite-layer blocks of every area below `E`; it does not assume that the full continuous profile already has a bounded potential.

## 4. Exact optimization by squares

Put `r=p+q>0`. Direct symbolic integration and simplification give the identity

$$
\begin{aligned}
E={}&\frac{17-6\sqrt2}{28}
-\frac{(\sqrt2\,r-3)^2}{28r}\\
&-\frac{(7q-2r-2)^2}{336r}
-\frac{(2p+q+6w-4)^2}{96r}.
\end{aligned}
\tag{Squares}
$$

Thus `E≤(17−6√2)/28` throughout this switching regime. Equality holds at

$$
r=\frac3{\sqrt2},\qquad
p=\frac{15\sqrt2-4}{14},\qquad
q=\frac{3\sqrt2+2}{7},\qquad
w=\frac{5-3\sqrt2}{7}.
$$

The switching points there are

$$
m=\frac{10\sqrt2-12}{21},\quad
v=\frac{9-4\sqrt2}{21},\quad
c=\frac{3+\sqrt2}{21},\quad
b=\frac{15\sqrt2+4}{62},\quad
h=\frac{6+2\sqrt2}{21}.
$$

Their approximate values are `0.10200646`, `0.15919742`, `0.21020065`, `0.40666457`, and `0.42040129`, in the required order. Simple rational bounds on `√2` verify all hypotheses; no numerical optimizer is needed for the area maximum.

The exact square identity can also be obtained in three elementary steps: optimize `w=(4−2p−q)/6`; for fixed `r`, optimize `q=2(r+1)/7`; then maximize

$$
\frac{17}{28}-\frac r{14}-\frac9{28r}
$$

at `r=3/√2`.

## 5. A simple fully rational benchmark

Choose

$$
p=\frac{69}{56},\qquad q=\frac{25}{28},\qquad
w=\frac3{28},\qquad r=\frac{17}{8}.
$$

The switching points are

$$
\frac{12}{119}<\frac{19}{119}<\frac{25}{119}
<\frac{28}{69}<\frac{50}{119}<\frac12.
$$

All signed-width feasibility statements therefore hold by the exact identities above, and the area is

$$
\boxed{E=\frac{579}{1904}=0.30409663865546218\ldots.}
$$

An independent rational vertex-arrangement verifier checked the continuously varying inequalities for this profile as well as this area. The limiting irrational optimum can alternatively be approached by rational parameter triples in the same open regime.

This signed continuation is already compatible with a height-dominated finite-layer potential. Its area improvement does not require the more general triangular facet-potential patch from the preceding note, although that extension remains independently valid.

## 6. Ordinary-proof transfer to the exact integer extremal function

The stronger signed geometry above has not been encoded in the completed Lean chain. Its integer implication follows as an ordinary mathematical proof from the same transfer theorem, as follows.

For every `ρ<E_*` sufficiently close to `E_*`, choose rational `p,q,w` in the displayed open switching regime so that the continued area exceeds `ρ`. Truncate slightly below `h`, replace widths by sufficiently fine constant-cell infima, and insert sufficiently small rational vertical gaps. The resulting finite union of rational rectangles still has area above `ρ` and a uniformly bounded potential satisfying the full torus midpoint inequality. All parameter choices are fixed before the finite prime grid is chosen.

For a rational rectangle, the number of `1/p` grid points in its interior, divided by `p²`, tends to its area as `p→∞`; a finite disjoint union has the same property. Consequently every sufficiently large prime has a finite torus block of density at least `ρ` and with the same potential bound. This is precisely the input to the generic tensor/shell/slope transfer proved in `AsymptoticCertificate.lean`, whose conclusion holds for every coefficient `C>2 sqrt(log(1/ρ))`.

The separate kernel-checked `RothBridge.lean` proves `rothNumberNat N ≤ Set.IsAPOfLengthFree.maxCard 3 N`, the latter being definitionally the original `Erdos142.r 3 N`. Finally let `ρ` approach `E_*` from below. For every

$$
C>2\sqrt{\log\!\left(\frac{28}{17-6\sqrt2}\right)}
=2.182116624879836\ldots,
$$

there is an `N_0` such that for every `N≥N_0`,

$$
r_3(N)\ge N\exp\bigl(-C\sqrt{\log N}\bigr).
$$

This final stronger constant is supported by the signed geometric proof and exact symbolic/vertex checks, not by a completed Lean formalization of that geometry. The separately completed end-to-end Lean theorem uses the explicit density `3/10` and proves the same conclusion for every `C>2 sqrt(log(10/3))=2.194513890888765...`. Both statements are lower bounds; neither provides the requested ratio-one asymptotic formula.
