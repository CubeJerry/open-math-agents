# A new torus-block augmentation from an exact triangular sumset hole

## Status and scope

This is an analytic construction, with independent exact rational polygon checks. It is not a solution of the ratio-one asymptotic problem for the actual extremal function in Erdős 142. It improves a geometric input to the Behrend-type lower-bound construction. No claim in this document is represented as fully checked in Lean.

The initial block is the six-width family being independently verified by the parent and literature agents. Its ideal area is approached by valid finite-layer inner approximations. The augmentation below works for every such approximation, and its added area is independent of the number or size of the layers. In particular, the large constants in the potential do not affect the limiting block density.

The strongest construction recorded here adds a limiting fraction **1/2 of the area of a triangular hole** in the original block's sumset, by using only the two upper doubling preimages. Earlier four-preimage constructions add limiting fraction 1/7 or exact fraction 1/13, and serve as separately certified fallbacks. The progression from 1/13 to 1/7 to 1/2 changes the potential argument, rather than merely refining a numerical search.

## 1. Coordinates and the six-width block

Work in the torus `(R/Z)^2`, using lifts in the unit rectangle

$$
D=[0,1)\times[-1/2,1/2).
$$

Write a lift as `(s,a)`. Let `p,q,w` be positive rational parameters, put

$$
b=\frac1{2p},\qquad h=\frac{1-w}{p+q},\qquad
d=\frac12-w-\frac{q}{2p}=(p+q)(h-b),
$$

and use the following profile functions:

$$
L(s)=ps,\qquad W(s)=\min(w+qs,1-ps),\quad 0\le s\le\tfrac12;
$$

$$
\begin{aligned}
U(t)&=1-2pt,\\
P_0(t)&=2w+q-1+2qt,\qquad P(t)=\min(U(t),P_0(t)),\\
V_1(t)&=1-2w-2qt,\\
V_0(t)&=1-w-q/2+(p-q)t,\qquad V(t)=\min(V_1(t),V_0(t)),\\
M(t)&=\min(V(t),p-1+2pt),\qquad 0\le t\le b.
\end{aligned}
$$

The ideal block is the union of three polygons:

$$
\begin{aligned}
T_0&=\{(s,a):0\le s\le 1/2,\ -L(s)/2\le a\le W(s)/2\},\\
T_+&=\{(1/2+t,a):0\le t\le b,\ 1/4-V(t)/4\le a\le1/4+P(t)/4\},\\
T_-&=\{(1/2+t,a):0\le t\le b,\ -1/4-M(t)/4\le a\le-1/4+U(t)/4\}.
\end{aligned}
$$

Closed boundaries are useful for exact geometry. Inner approximations use open horizontal intervals and separated height intervals.

Besides the no-upward constraints certified elsewhere, the hole argument below assumes

$$
1<p<2,\qquad b<h<1/2,\qquad w+qb>1/4,
$$

and that all six widths are between zero and one. Every numerical and rational candidate listed below satisfies these conditions.

## 2. An exact open triangle missing from `T+T`

Define

$$
H=\left\{(s,a):2b<s<2h,\quad
w+\frac q2s<a<1-\frac p2s\right\}.
$$

Its vertices are

$$
A=(2b,1/2),\qquad B=(2b,w+qb),\qquad
C=(2h,1-ph).
$$

Its area is

$$
|H|=(p+q)(h-b)^2=\frac{d^2}{p+q}>0.
$$

**Claim.** The image of `H` in the torus is disjoint from `T+T`.

First note the elementary angular bounds

$$
-1/2<a_0<1/4,\qquad 0\le a_+\le1/2,\qquad
-1/2\le a_-\le0.
$$

For the strict upper bound on `a_0`, `W` attains its maximum at `h`, where
`W(h)=1-ph<1/2` because `h>b`. The strict lower bound follows from `p<2`.

Every point of `H` has height greater than `2b` and angular coordinate strictly between `1/4` and `1/2`.

* **Two upper endpoints.** Their ordinary height sum lies in `[1,1+2b]`; its torus representative lies in `[0,2b]`, so it cannot meet `H`.
* **Two lower endpoints.** Their height sum is at most one, so a target in `H` has its ordinary height `s`. The angular sum satisfies
  `−ps/2 <= a_x+a_z <= w+qs/2`. The unshifted sum lies below `H`; its translate by one lies above `H`. The angular ranges exclude other translates.
* **A lower and a positive upper endpoint.** A target height in `H` has no height wrap: the maximum ordinary mixed height is `1+b`, whereas `s+1>1+2b>1+b`. The bound `P<=P_0` gives

  $$
  a_0+a_+\le\frac{w+qs_0}{2}+\frac14+\frac{P_0(t)}4
  =w+\frac q2(s_0+1/2+t)=w+\frac q2s.
  $$

  The unshifted angular sum is below `H`. A translate from below zero cannot meet `H`, because this mixed sum is greater than `−1/2` whereas `a_H−1<−1/2`.
* **A lower and a negative upper endpoint.** Again there is no height wrap. Since `M(t)<=p−1+2pt`,

  $$
  a_0+a_-\ge-\frac p2s_0-\frac p4-\frac p2t=-\frac p2s.
  $$

  The translate by one is above `H`. The unshifted sum is below `1/4`, so cannot meet `H`.

This proves the claim for the entire continuous polygons, including their boundaries. Consequently it holds for every inner block `S` contained in `T`.

For the particularly simple parameters

$$
p=6/5,\quad q=9/10,\quad w=17/140,
$$

the triangle has vertices

$$
(5/6,1/2),\quad(5/6,139/280),\quad(41/49,122/245),
$$

and area `1/164640`. The independent polygon program finds exactly fifteen relevant periodic Minkowski polygons; each intersects the closed triangle only along a boundary segment or not at all.

## 3. The four-preimage construction

Let `K` be an open subset of `H` with each coordinate diameter smaller than `1/2`. Let

$$
W_K=\{w\in D:2w\pmod{\mathbb Z^2}\in K\}.
$$

It has four disjoint components. In the current chart they are

$$
\frac12K+e/2,\qquad e\in\{0,1\}\times\{0,-1\}.
$$

The total area of the four components is `|K|`. Each `w` has a unique local doubled coordinate `k_w in K`, with `2w=k_w+e_w`.

Let `S` be a valid inner approximation of the original block. Assume its bounded potential has been normalized so

$$
0\le F_S\le M,
$$

and for all modular progressions `x+z=2y` with `x,y,z in S`,

$$
F_S(x)+F_S(z)-2F_S(y)\ge\|x-z\|^2.
$$

The sets `S` and `W_K` are disjoint. Otherwise a common point `w` would give `2w in S+S` and `2w in K subset H`, contradicting the hole property. Old endpoints cannot have a new midpoint for the same reason.

For a progression with all three points new, doubling the progression gives

$$
k_x+k_z-2k_y\in\mathbb Z^2.
$$

Each coordinate of its left side has absolute value smaller than one, by the coordinate diameter assumption. Hence

$$
k_x+k_z=2k_y.
$$

Returning to the original progression then shows that `e_x+e_z` is even in each coordinate. Since the two available sheet labels in each coordinate differ by one, **the endpoint sheets agree**, `e_x=e_z`. In particular,

$$
k_x-k_z=2(x-z).
$$

The midpoint sheet may be different. Thus a single convex potential in the `k` coordinates, used on all four sheets, controls the actual lifted endpoint distance. This is the point at which simply treating the four sheets as an ordinary convex region would be incorrect.

## 4. An offset-only patch of area `|H|/13`

Let `lambda_1,lambda_2,lambda_3` be the barycentric coordinates of the triangle `H`, and put

$$
K_{13}=\{k\in H:3/13<\lambda_i(k)<6/13\text{ for }i=1,2,3\}.
$$

For `u,v in K_13`, every barycentric coordinate of `2u−v` is strictly positive. Hence

$$
2K_{13}-K_{13}\subset H.
$$

The relative area is

$$
\frac{|K_{13}|}{|H|}=(4/13)^2-3(1/13)^2=1/13.
$$

If a mixed progression had an old endpoint `x`, a new endpoint `z`, and a new midpoint `y`, doubling would give

$$
2x\equiv2k_y-k_z\pmod{\mathbb Z^2}.
$$

Its right side is in `H`, while its left side belongs to `S+S`; this is impossible.

Choose any center `c` and use

$$
F_W(w)=Q+\|k_w-c\|^2,\qquad Q=2M+2.
$$

New-only progressions satisfy strong Jensen by the preceding sheet calculation. Every remaining mixed progression has an old midpoint; its endpoint contribution contains at least one copy of `Q`, which pays the worst old-potential contribution `−2M` and the maximum squared distance two in `D`. Thus the joined block is valid.

At the simple benchmark, the ideal joined area is

$$
\frac{14303}{47040}+\frac1{2140320}
=\frac{260315}{856128}
\approx0.30406084136951483.
$$

At the independently optimized rational parameters

$$
p=345/286,\quad q=250/277,\quad w=4201393/34900338,
$$

the ideal joined area is

$$
\frac{424074534852967}{1394685492338424}
\approx0.3040646347743497.
$$

### Optional optimality fact for this sufficient condition

The fraction `1/13` is optimal among all measurable patches satisfying `2K−K subset H`. Taking the convex hull preserves the condition. Minkowski averaging its six images under permutations of the triangle vertices preserves feasibility, and Brunn–Minkowski does not decrease area. A symmetric convex feasible body is contained in a strip body

$$
a\le\lambda_i\le2a\quad(i=1,2,3),\qquad 1/6\le a\le1/3.
$$

Its relative area is

$$
(1-3a)^2-3(1-4a)_+^2+3(1-5a)_+^2.
$$

On the three successive intervals cut by `1/5` and `1/4`, this is
`(6a−1)^2`, `−2+18a−39a^2`, and `(1−3a)^2`. The global maximum is `1/13` at `a=3/13`.

This optimality statement concerns the exclusion condition `2K−K subset H`, not all possible potential constructions. The next section exceeds it by paying certain mixed progressions with a varying potential.

## 5. A larger one-facet patch: limiting area `|H|/7`

Fix `0<epsilon<1`, write `r=1−epsilon`, and designate one barycentric coordinate as active. Let

$$
K_\epsilon=\left\{k\in H:\lambda_1(k)>\epsilon,\quad
\frac{2r}{7}<\lambda_2(k),\lambda_3(k)<\frac{4r}{7}\right\}.
$$

This is the homothetic image, with ratio `r` and center the active vertex, of the pentagon with `lambda_2,lambda_3 in (2/7,4/7)` and `lambda_1>0`. Its area is exactly

$$
|K_\epsilon|=\frac{(1-\epsilon)^2}{7}|H|.
$$

Indeed, in coordinates `(lambda_2,lambda_3)`, the limiting region is a square of area `4/49` with a corner triangle of area `1/98` removed. Its area `1/14` is `1/7` of the reference triangle area `1/2`.

The safe coordinates satisfy

$$
\lambda_2(2u-v)>0,\qquad\lambda_3(2u-v)>0
\quad(u,v\in K_\epsilon).
$$

Suppose an old endpoint `x`, new endpoint `z`, and new midpoint `y` form a progression. As before `2x` is congruent to `v=2k_y-k_z`. Since `2x in S+S`, the hole property implies `v` is not in `H`. The two safe coordinates of `v` are positive. Thus its active coordinate must be nonpositive:

$$
2\lambda_1(k_y)-\lambda_1(k_z)\le0.
$$

Consequently,

$$
\lambda_1(k_z)^2-2\lambda_1(k_y)^2
\ge2\lambda_1(k_y)^2>2\epsilon^2.
$$

Let `R` bound `||k−c||` on the closed triangle and choose `C` such that

$$
C\epsilon^2\ge2M+2+2R^2.
$$

Use the potential

$$
F_W(w)=C\lambda_1(k_w)^2+2\|k_w-c\|^2.
$$

All cases now have an explicit proof:

1. **Old endpoints, new midpoint:** impossible by `2W subset K subset H`.
2. **Old and new endpoints, new midpoint:** the active-coordinate inequality gives

   $$
   F_S(x)+F_W(z)-2F_W(y)
   \ge2C\epsilon^2-4R^2\ge2.
   $$

3. **At least one new endpoint, old midpoint:** each new endpoint contributes at least `C epsilon^2`; all old potentials are in `[0,M]`, so the gap is at least `C epsilon^2−2M>=2`.
4. **All new:** the doubled coordinates satisfy an ordinary midpoint equation and the endpoint sheets agree. The active-coordinate square is convex. The norm-square term has Jensen gap `||k_x−k_z||^2=4||x−z||^2`, which is more than sufficient.
5. **All old:** the original certificate applies.

The new potential is bounded, since `K_epsilon` is bounded. It grows when `epsilon` decreases, which is harmless for a fixed block. The original inner approximation may lose arbitrarily little area, and `epsilon` may be chosen arbitrarily small. Therefore valid blocks have area arbitrarily close to

$$
|T|+\frac{|H|}{7}.
$$

### Exact rational candidate

The literature agent optimized the continuous objective and supplied

$$
p=1125/932,\qquad q=710/787,\qquad
w=162359479/1353277980.
$$

The exact polygon verifier independently confirms the hole. The exact ideal quantities are

$$
|T|=\frac{39150986575333445821}{128759450182788150000},
\qquad
|H|=\frac{203852631623809}{10729954181899012500},
$$

and

$$
|T|+\frac{|H|}{7}
=\frac{190982127009695893}{628094878940430000}
\approx0.30406572862347614.
$$

For the concrete rational choice `epsilon=1/1000`, the ideal original area plus the actual new patch area is

$$
\frac{9787833834603452823681061}{32189862545697037500000000}
\approx0.3040657231980581.
$$

An actual finite-layer old block has area slightly smaller than the ideal original area. This loss must be included whenever quoting a single finite certificate; it must not be silently omitted.

## 6. Two upper preimages: limiting area `|H|/2`

This larger construction uses an asymmetry of the original block that was absent from the general hole lemma: all original points have height at most

$$
S_0=1/2+b.
$$

Put `delta=h−b>0`, and assume

$$
0<S_0-\delta,\qquad S_0+2\delta<1.
$$

These are strict inequalities with a large margin at both parameter choices below. For `0<eta<1`, truncate the hole only at its vertical base:

$$
K_\eta=\{(s,a)\in H:s>2b+2\eta\delta\}.
$$

It is a similar triangle of area `(1−eta)^2|H|`. Use its two **upper** doubling preimages,

$$
W=\left(\tfrac12K_\eta+(1/2,0)\right)
\ \cup\
\left(\tfrac12K_\eta+(1/2,-1/2)\right).
$$

Their total area is `(1−eta)^2|H|/2`. Every new height satisfies

$$
S_0+\eta\delta<s_w<S_0+\delta.
$$

Write `u(w)=s_w−S_0`, so `eta*delta<u(w)<delta`. Suppose an old endpoint `x`, new endpoint `z`, and new midpoint `y` form a modular progression. The ordinary real number `2s_y−s_z` lies in

$$
(S_0-\delta,S_0+2\delta)\subset(0,1).
$$

Because the old height is also in `[0,1)`, the modular height equation has **no wrap**:

$$
s_x=2s_y-s_z.
$$

The old-height bound `s_x<=S_0` implies

$$
u(z)\ge2u(y),\qquad
u(z)^2-2u(y)^2\ge2\eta^2\delta^2.
$$

Thus the active-facet potential can be based simply on excess height. Take

$$
F_W(w)=C u(w)^2+2\|k_w-c\|^2,
\qquad
C\eta^2\delta^2\ge2M+2+2R^2.
$$

The complete proof follows the same five cases as before:

* Old endpoints with new midpoint are excluded by the hole.
* An old and new endpoint with new midpoint have Jensen gap at least `2C eta^2 delta^2−4R^2>=2`.
* New endpoints with an old midpoint contribute at least `C eta^2 delta^2`, enough to pay all old terms and the squared endpoint distance.
* For all-new progressions, the ordinary doubled-coordinate midpoint equation and the endpoint sheet-parity argument still apply. The height excess is affine in the doubled coordinate, so its square is convex. The norm-square term controls actual endpoint distance.
* All-old progressions retain the old certificate.

There is no assertion that old points have height below a new midpoint *on the torus without choosing lifts*. The explicit interval calculation above is what eliminates the possible integer carry. Taking the old inner approximation arbitrarily close to its ideal area and then letting `eta` tend to zero gives valid block densities arbitrarily close to

$$
|T|+\frac{|H|}{2}.
$$

### The same region as a signed-width continuation

The new triangles extend the upper band from `t=b` to `t=h`. On this extra interval their profile is

$$
P(t)=U(t)=1-2pt<0,\qquad
V(t)=M(t)=1-2w-2qt>0.
$$

The displayed values `P,U` are signed offsets from the conventional arc centers; they need not be nonnegative for the actual intervals to exist. Both actual arc lengths are `(U+V)/4`, positive until `t=h`. The two arcs have total width

$$
\frac{U(t)+V(t)}2=1-w-(p+q)t=(p+q)(h-t).
$$

Their area is exactly

$$
\int_b^h(p+q)(h-t)\,dt=\frac12(p+q)(h-b)^2=|H|/2.
$$

This explains a restrictive assumption in the earlier six-width search: requiring the individual offsets `U,P` to be nonnegative forces an artificial cutoff even though the intervals can continue with their centers shifted. The potential proof above certifies the continuation without assuming that the old search constraints cover signed widths.

### Exact rational checkpoint

For

$$
p=69/56,\qquad q=25/28,\qquad w=3/28,
$$

the exact values are

$$
b=28/69,\quad h=50/119,\quad\delta=118/8211,\quad S_0=125/138,
$$

$$
S_0-\delta=14639/16422>0,\qquad
S_0+2\delta=15347/16422<1.
$$

The exact polygon verifier checks all fifteen periodic sum polygons and obtains

$$
|T|=\frac{19282409}{63454608},\qquad
|H|=\frac{3481}{7931826},\qquad
|T|+\frac{|H|}{2}=\frac{579}{1904}
\approx0.30409663865546216.
$$

For `eta=1/1000`, the ideal old area plus the actual two-triangle patch area is

$$
\frac{4824076291481}{15863652000000}
\approx0.3040962000099977.
$$

The separate six-width algebra calculation identifies the parameter choice

$$
p=\frac{15\sqrt2-4}{14},\qquad
q=\frac{3\sqrt2+2}{7},\qquad
w=\frac{5-3\sqrt2}{7},
$$

with ideal augmented area

$$
\frac{17-6\sqrt2}{28}\approx0.304097093777193918.
$$

The parent/literature verification of the original width constraints is still needed at that algebraic point; the rational certificate above is independent of floating-point optimization.

## 7. Converting the continuous old profile to valid layers

The following elementary lemma supplies a convenient analytic route. Let the old block use finitely many disjoint height intervals separated by a minimum gap `delta>0`. On each interval let its horizontal slice be constant. Assume the global no-upward property `2s_y<=s_x+s_z`. Suppose each slice has a potential `g_j` in `[0,B]` satisfying the one-dimensional strong Jensen inequality.

Then

$$
F(s,a)=K s^2+g_j(a),\qquad
K\ge\max\left(2,\frac{4B+4}{\delta^2}\right)
$$

satisfies the two-dimensional inequality.

If the endpoint intervals differ, their heights differ by at least `delta`; no-upward and nonnegative heights give a squared-height Jensen gap at least `(s_x−s_z)^2/2`. This contribution is at least `2B+2`, paying the worst secondary gap `−2B` and the maximum squared endpoint distance two.

If the endpoints are in the same interval and there is no height wrap, their midpoint is in the same interval; the slice certificate applies, and `K>=2` pays the height part. For a downward wrap by a positive integer, the squared-height gap is at least `1/2`, again sufficient to pay the bounded secondary potential and endpoint distance.

For a lower slice of length at most `1/2`, use `g(a)=2a^2`. For an upper slice with widths `P,U,V,M` satisfying

$$
P+U+2\max(V,M)\le2,
$$

use local coordinate `u=a−1/2` on the positive arc and `u=a` on the negative arc, and `g(a)=8u^2`. Its range is `[0,2]`.

The nontrivial upper-slice case has endpoints in different arcs. In local coordinates a possible midpoint is `u_y=(u_x+u_z)/2 ±1/4`. The more negative branch is excluded by the displayed width inequality and open boundaries. On the other branch, `u_y<=0` implies the local endpoint average is at most `−1/4`; the quadratic Jensen gap is at least `1/8`, so multiplying by eight pays the squared angular endpoint distance, which is at most one. Same-arc endpoints have the ordinary local midpoint equation, including when the midpoint changes torsion sheet.

Continuous piecewise affine profiles can be approximated from inside by constant slices and then separated by arbitrarily thin height gaps. Their area converges to the ideal area. The no-upward property is inherited by taking subsets, while each constant slice retains its one-dimensional width certificate.

## 8. Computational files and limits of the checks

* `polygon_extension.py` implements rational convex hulls, clipping, Minkowski sums, polygon difference, the triangular hole, and both patch shapes. Core geometry uses `fractions.Fraction` and no optimization solver.
* `verify_augmentations.py` is the consolidated reproduction command. It checks four rational checkpoints, all sixty periodic Minkowski exclusions, preimage areas, disjointness, small coordinate diameters, and the upper-patch height bounds. It writes `augmentation-certificates.json`.
* `hole-certificates.json` records the exact 1/13 examples and every periodic Minkowski intersection.
* `facet-hole-certificate.json` records the exact 1/7 candidate, its limiting area, and the concrete `epsilon=1/1000` patch.
* `upper-hole-certificate.json` records the exact 1/2 rational candidate, both height-wrap bounds, its limiting area, and the concrete `eta=1/1000` two-triangle patch.
* `residual-holes.json` records the three small triangles remaining after the simple benchmark's 1/13 patch. Each has area `|H|/169`; this is exploratory information, not a claimed iterative construction.
* `plot_torus_extension.py` generates `torus-extension.svg` and `torus-extension.png`. The plotted coordinates are floating-point renderings of the exact rational polygons; the figures are explanatory, not proof certificates.

These exact checks support the analytic geometry. They do not independently establish the six-width family's global no-upward inequalities, the finite-layer potential, the transfer from a torus block to integer progression-free sets, or a ratio-one asymptotic. Those require the proofs described here or the separate parent/literature/formal work.

Two explored variants were weaker: the ratio-bounded symmetric patch `max lambda_i < rho min lambda_i` has relative area `2(rho−1)^2/((rho+2)(2rho+1))`, tending only to `1/10` at `rho=2`; a related two-active-coordinate construction reaches `1/9`. Neither improves the one-facet `1/7` patch.

The initial FFT search on the older symmetric `71/240` block produced apparent sumset holes. Increasing the resolution showed that those were boundary-rasterization artifacts, with widths of one grid pixel and shrinking area. That route was discarded. The later six-width triangle is qualitatively different: its positive area and all sumset exclusions are proved by exact support inequalities and exact rational polygon clipping.

## 9. Broader signed-width search

After the signed continuation was found, the parent and formal/literature agents independently audited the larger family with all six offsets in `[-1,1]`, actual interval lengths nonnegative, lower length at most `1/2`, and the same upper-angle, LL, and LH inequalities. The broader search did not improve the algebraic construction in the grids tested.

`signed_width_lp.py` uses uniform nodal profiles. It imposes `0<=L+W<=1`, `P+V>=0`, `U+M>=0`, and all original angular and mixed constraints. A tiny convex combination with the strictly feasible constant profile `0.1`, followed by rational rounding, gives an exactly verified rational profile. The objective is its exact trapezoidal area.

| Grid denominator | Cutoffs searched | Best cutoff | Best verified ideal profile area |
| --- | --- | --- | --- |
| 96 | 38/96 through 44/96 | 5/12 | 0.3040798611085469 |
| 192 | 79/192 through 83/192 | 27/64 | 0.30409041206005144 |
| 384 | 160/384 through 164/384 | 161/384 | 0.30409580743296843 |

These are finite-profile lower bounds, not upper bounds on the continuous class. The constraints at grid pairs suffice because every vertex of the piecewise affine two-variable constraint arrangement is a grid pair, including its diagonal boundaries.

To remove the grid's inability to represent the exact kinks, `nonuniform_signed_lp.py` uses the three-parameter construction's breakpoints plus successively finer additional knots. It checks every vertex of the corresponding line arrangements, including vertices where a midpoint breakpoint meets one endpoint breakpoint. With up to 208 independent width variables and 12,472 constraints, the optimum remains numerically equal to `(17−6sqrt(2))/28`, within about `3e−16`. At the simpler rational knots, the analogous optimum remains `579/1904`. These nonuniform runs are floating-point optimization evidence; they are not a certified global upper bound or a new exact optimality theorem.

An earlier general affine-height search inside the triangular hole, recorded in `facet_height_lp.py`, returned the existing one-facet `1/7` patch and did not improve it. The later two-upper-preimage construction succeeds by changing which doubling sheets are included, rather than by enlarging that four-sheet patch family.
