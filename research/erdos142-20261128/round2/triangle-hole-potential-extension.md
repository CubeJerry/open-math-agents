# Filling a triangular sumset hole using a facet potential

**Status.** This is a direct extension lemma for a bounded-potential torus block. It supplies a patch whose area approaches one seventh of a sufficiently small triangular hole in the block's sumset. It is stronger than the constant-offset patch with area one thirteenth of the hole. The application below remains a lower-bound construction and does not solve Erdős 142's ratio-one asymptotic target.

## Hypotheses and conventions

Let `B` be a subset of the two-dimensional torus, with fixed representatives in a unit square, and let `F_B:B→[0,M]` satisfy

$$
F_B(x)+F_B(z)-2F_B(y)\ge \|\widetilde x-\widetilde z\|^2
$$

whenever `x+z=2y` in the torus and all three points lie in `B`. The fixed representative square has squared diameter 2.

Let `H` be a nondegenerate open triangle in an injective coordinate chart, disjoint from `B+B`. Assume its coordinate widths are less than `1/2`, and that it lies within one open unit coordinate rectangle. These smallness assumptions are satisfied with a large margin by the explicit holes in the six-width construction. Let `λ_1,λ_2,λ_3` be the affine barycentric coordinates on the plane of `H`.

## The patch

Fix `0<ε<1`. Set `s=1−ε`, and define

$$
K_\varepsilon=\left\{k:\lambda_1(k)>\varepsilon,
\quad\frac{2s}{7}<\lambda_2(k)<\frac{4s}{7},
\quad\frac{2s}{7}<\lambda_3(k)<\frac{4s}{7}\right\}.
$$

All barycentric coordinates are positive, so `K_ε⊂H`. The set is convex. In `(λ_2,λ_3)` coordinates it is a square of side `2s/7`, with one corner triangle of leg `s/7` removed by `λ_2+λ_3<s`. Thus

$$
\boxed{|K_\varepsilon|=\frac{(1-\varepsilon)^2}{7}|H|.}
$$

Let `W` consist of all four inverse images of `K_ε` under multiplication by 2 on the torus. Then `|W|=|K_ε|`. It is disjoint from `B`, since `2B⊂B+B` while `2W=K_ε⊂H`.

For `w∈W`, write `k_w` for the unique representative of `2w` in `K_ε`. Fix a point `c` and a bound `R` with `||k−c||≤R` for all `k∈K_ε`. Define

$$
F_W(w)=C\lambda_1(k_w)^2+2\|k_w-c\|^2,
$$

where

$$
C\varepsilon^2\ge2M+2+4R^2.
\tag{1}
$$

This is nonnegative and bounded by `C+2R²`. No constant offset is required.

## Audit of every progression type

Two old endpoints cannot have a new midpoint: `x,z∈B,y∈W,x+z=2y` would place `2y=k_y` in both `B+B` and `H`.

For an old endpoint `x∈B`, new endpoint `z∈W`, and new midpoint `y∈W`, put

$$
q=2k_y-k_z.
$$

Its torus class is `2x`. If the real point `q` lay in `H`, this would contradict `2x∈2B⊂B+B`. Hence `q∉H`. On the other hand,

$$
\lambda_i(q)=2\lambda_i(k_y)-\lambda_i(k_z)>0
\quad(i=2,3)
$$

by the two factor-two ranges defining `K_ε`. Consequently `λ_1(q)≤0`, and

$$
\lambda_1(k_z)\ge2\lambda_1(k_y)>2\varepsilon.
$$

Therefore

$$
\begin{aligned}
F_B(x)+F_W(z)-2F_W(y)
&\ge C\bigl(\lambda_1(k_z)^2-2\lambda_1(k_y)^2\bigr)-4R^2\\
&\ge2C\varepsilon^2-4R^2\ge2.
\end{aligned}
$$

This pays for the squared distance between the endpoint representatives. Notice that this argument does not require assigning `q` to a particular fundamental rectangle when `q` is outside `H`; only the implication `q∈H ⇒ its torus class lies in H` is used.

If the midpoint is old and at least one endpoint is new, the lower bound `F_W≥Cε²` gives, respectively,

$$
C\varepsilon^2-2M\ge2
\quad\text{or}\quad
2C\varepsilon^2-2M\ge2.
$$

It remains to consider three new points. Doubling their progression equation gives

$$
k_x+k_z-2k_y\in\mathbb Z^2.
$$

Each coordinate of this integer vector has absolute value less than 1 because the coordinate widths of `K_ε` are less than `1/2`; therefore it is zero. The lifted doubled points have an ordinary midpoint. Moreover, the endpoint inverse-image sheets must coincide: writing `2\widetilde w=k_w+n_w` with each coordinate of `n_w` in two consecutive integers, the original progression equation gives `n_x+n_z` even in each coordinate. Thus `n_x=n_z` and

$$
\widetilde x-\widetilde z=(k_x-k_z)/2.
$$

Quadratic convexity now yields

$$
\begin{aligned}
F_W(x)+F_W(z)-2F_W(y)
&=\frac C2\bigl(\lambda_1(k_x)-\lambda_1(k_z)\bigr)^2
+\|k_x-k_z\|^2\\
&\ge4\|\widetilde x-\widetilde z\|^2.
\end{aligned}
$$

Old progressions retain their original inequality. Hence `B∪W`, with the piecewise potential, is a valid bounded-potential block of area

$$
|B|+\frac{(1-\varepsilon)^2}{7}|H|.
$$

The limiting patch fraction `1/7` is a supremum supplied by these finite-potential blocks as `ε→0`; setting `ε=0` in (1) is not legitimate.

## Application to the six-width profiles

Use the notation and continuous profiles from `six-width-analytic-benchmark.md`. Let

$$
b=\frac1{2p},\qquad h=\frac{1-w}{p+q},\qquad h>b.
$$

In the parameter range independently checked by the polygon-hole analysis, the continuous block `T` has the triangular sumset hole with vertices

$$
(2b,1/2),\qquad (2b,w+qb),\qquad (2h,1-ph).
$$

Its exact area is

$$
H_0=(p+q)(h-b)^2
=\frac{(2pw-p+q)^2}{4p^2(p+q)}.
$$

Apply the lemma to any finite-layer inner approximation `B⊂T`. Since `B+B⊂T+T`, the same triangle remains a hole. Taking finer inner approximations and then smaller positive `ε` gives valid bounded-potential block areas approaching

$$
E(p,q,w)=A(p,q,w)+\frac{H_0}{7}.
$$

The continuous profile `T` itself is not being assumed to possess a bounded Jensen potential.

## Exact parameter optimization

For fixed `p,q` in the same switching regime, `E` is a strictly concave quadratic in `w`. Its maximizing intercept is

$$
w_* =\frac{p(48-14p-7q)-20q}{82p}.
$$

After substitution,

$$
E_*=-\frac{68p^4+68p^3q-396p^3+99p^2q^2-484p^2q+222p^2
-20pq^2+20pq+30q^2}{656p^2(p+q)}.
$$

An approximate stationary point is

$$
p=1.2070824754498455,\quad q=0.9021604447459381,\quad
w=0.1199748485716887,
$$

giving

$$
E=0.3040657286235537016\ldots.
$$

This is numerical stationarity, not a global optimality claim. A concrete rational choice is

$$
p=\frac{1125}{932},\qquad q=\frac{710}{787},\qquad
w=\frac{162359479}{1353277980}.
$$

At this point,

$$
\begin{aligned}
A&=\frac{39150986575333445821}{128759450182788150000},\\
H_0&=\frac{203852631623809}{10729954181899012500},\\
h-b&=\frac{14277697}{4757317125}>0,\\
E&=\boxed{\frac{190982127009695893}{628094878940430000}}
=0.30406572862347614\ldots.
\end{aligned}
$$

A simpler benchmark is

$$
p=6/5,\quad q=9/10,\quad w=99/820,
$$

for which `A=3434761/11296320`, `H_0=7/806880`, `h−b=1/492`, and

$$
E=\frac{5585}{18368}=0.30406141114982577\ldots.
$$

Every area strictly below the corresponding limiting value `E` is attained by sufficiently fine, sufficiently lightly gapped finite-layer inner approximations followed by a positive-ε patch. The separate discrete-density and tensor/shell/slope transfer is still needed for the final integer lower-bound statement.

## Comparison with a constant-offset patch

The hexagon defined by `3/13<λ_i<6/13` for all three coordinates satisfies `2K−K⊂H` and has area `|H|/13`. That construction excludes all mixed progressions with a new midpoint, allowing a large constant offset on the patch. The facet potential above pays for an allowed class of mixed progressions and increases the limiting patch fraction to `1/7`.

Within the stricter condition `2K−K⊂H`, the fraction `1/13` is optimal even for arbitrary measurable `K`: taking convex hull preserves this inclusion, and Minkowski averaging over the triangle's six affine symmetries preserves it while not decreasing area, by Brunn–Minkowski. For the resulting symmetric set, the coordinate minima are equal to some `m`, and the coordinate maxima are at most `2m`. It is contained in `{m≤λ_i≤2m}`. The area fraction of this latter polygon is maximized at `m=3/13`, where it equals `1/13`. This auxiliary observation is not needed for the facet-potential construction.
