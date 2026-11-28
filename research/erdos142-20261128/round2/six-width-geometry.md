# A certifiable six-width torus-block family

This note independently derives sufficient geometric conditions for the six-width family in team note 110197. That note's numerical claim `25541/84000` is not assumed. No exact profiles attaining its value have yet been checked in this investigation.

## Step profiles and slices

Fix an integer `D>0` divisible by four and an upper cutoff `K<=D/2`.
Lower height cells are `I_i=(i/D,(i+1)/D)`, `0<=i<D/2`. Upper height cells are `J_j=(1/2+j/D,1/2+(j+1)/D)`, `0<=j<K`.

Widths are constant on a cell and all lie in `[0,1]`. The lower angular slice is

$$
A_i=(-L_i/2,W_i/2).
$$

The upper slice is the union, modulo one, of

$$
B_j^+=(1/4-V_j/4,1/4+P_j/4),\qquad
B_j^-=(-1/4-M_j/4,-1/4+U_j/4).
$$

An interval with both widths zero is empty. Negative angular coordinates are retained as real lifts.

## LP constraints covering all real height pairs

Within a cell impose

$$
L_i+W_i\le1,\qquad
P_j+U_j+2V_j\le2,\qquad P_j+U_j+2M_j\le2.
\tag{A}
$$

For two lower cells `i,j`, possible upper-cell indices of an upward modular midpoint are among

$$
t=\lfloor(i+j)/2\rfloor,\quad t=\lceil(i+j)/2\rceil.
$$

For each such `0<=t<K`, impose

$$
\begin{aligned}
L_i+L_j+U_t&\le1,&L_i+L_j+P_t&\le1,\\
W_i+W_j+V_t&\le1,&W_i+W_j+M_t&\le1.
\end{aligned}
\tag{LL}
$$

For lower cell `i` and upper cell `j`, possible upper-cell indices of an upward midpoint are among

$$
t=D/4+\lfloor(i+j)/2\rfloor,\quad
t=D/4+\lceil(i+j)/2\rceil.
$$

For every such `t<K`, impose

$$
\begin{aligned}
P_j+2W_i+2V_t&\le1,&P_j+2W_i+2M_t&\le1,\\
M_j+2L_i+2U_t&\le1,&M_j+2L_i+2P_t&\le1.
\end{aligned}
\tag{LH}
$$

If `i+j` is even, the two indices coincide. These floor/ceiling indices cover the entire possible midpoint-height interval, not just nodal midpoints: the mean of two open grid cells has scaled endpoints `(i+j)/2` and `(i+j+2)/2`. Add `D/4` in the mixed case.

Keeping these constraints when an angular slice is empty is conservative. Deactivating them for empty slices would require disjunctive or integer variables.

The exact ungapped area objective is

$$
A_0=\frac1D\left[
\frac12\sum_{i<D/2}(L_i+W_i)
+\frac14\sum_{j<K}(V_j+P_j+M_j+U_j)\right].
\tag{Area}
$$

## Exclusion of upward midpoints

An upward vertical midpoint obeys `2s_y=s_x+s_z+1`. Its midpoint must be upper; two upper endpoints would force `s_y>1`. Only (LL) and (LH) occur.

For (LL), the endpoint angular sum lies in

$$
(-(L_i+L_j)/2,(W_i+W_j)/2).
$$

The doubled upper midpoint slice lies around half-integers, with maximum left radius `max(V_t,M_t)/2` and right radius `max(P_t,U_t)/2`. Conditions (LL) separate these intervals modulo one. The open angular endpoints exclude equality at a boundary.

For (LH), endpoint sums lie in the two intervals

$$
\left(\frac14-\frac{2L_i+V_j}{4},\frac14+\frac{2W_i+P_j}{4}\right),
\qquad
\left(-\frac14-\frac{2L_i+M_j}{4},-\frac14+\frac{2W_i+U_j}{4}\right).
$$

Conditions (LH) separate the positive interval's upper endpoint and negative interval's lower endpoint from the adjacent doubled-midpoint intervals. They also exclude the other integer translates. For example, `2L_i+2max(P_t,U_t)<=1-M_j` and `V_j<=1` imply

$$
\frac14-\frac{2L_i+V_j}{4}\ge\frac{\max(P_t,U_t)}2,
$$

which is safely above the negative half-integer interval's upper endpoint. The opposite bound follows using the `W_i` inequality and `U_j<=1`.

## Within-cell potential

For lower points use `u=a`. Since `L+W<=1`, the angular interval has width at most one half, so a modular midpoint in that interval is ordinary. Hence

$$
u_x^2+u_z^2-2u_y^2=(a_x-a_z)^2/2.
$$

For upper points fold both intervals into `(-1/2,0)`:

$$
u=a-1/2\text{ on }B^+,\qquad u=a\text{ on }B^-.
$$

If endpoint labels agree, the modular equation forces `u_x+u_z=2u_y`, and actual endpoint differences equal folded endpoint differences.

If labels differ, `delta=u_x+u_z-2u_y` is either `1/2` or `-1/2`. Condition (A) excludes `delta=1/2`, because

$$
\delta<\frac{P+U+2\max(V,M)}4\le\frac12.
$$

Thus `delta=-1/2`. Write `m=(u_x+u_z)/2`; then `u_y=m+1/4<0`, so `m<-1/4`. Consequently

$$
Q:=u_x^2+u_z^2-2u_y^2
=\frac{(u_x-u_z)^2}{2}-m-\frac18
\ge\frac{(u_x-u_z)^2}{2}+\frac18.
$$

The actual angular endpoint distance is at most `|u_x-u_z|+1/2`. The identity `( |u_x-u_z|-1/2 )^2>=0` therefore gives

$$
4Q\ge(a_x-a_z)^2.
\tag{J}
$$

Benign upper cross-label midpoints are thus allowed: their folded midpoint moves toward zero and lowers the potential. A dichotomy that requires either an ordinary local midpoint or a vertical gap would incorrectly omit this third case.

## Positive gaps give a complete finite-layer block

Choose `0<g<1/D` and trim `g/2` from each end of every height cell. Each retained cell has width `1/D-g`; distinct cells are separated by at least `g`. The exact resulting area is

$$
A_g=(1-Dg)A_0.
$$

Use

$$
F(s,a)=Cs^2+4u^2,\qquad C\ge2+6/g^2.
$$

Upward vertical wraps have already been excluded. If the vertical midpoint is ordinary and the endpoints lie in the same retained cell, its midpoint lies there too. Equation (J), or the lower-slice identity, plus vertical quadratic curvature gives

$$
F(x)+F(z)-2F(y)\ge(s_x-s_z)^2+(a_x-a_z)^2.
\tag{P}
$$

For endpoints in different cells, the vertical curvature is at least `(s_x-s_z)^2/2>=g^2/2`. After paying for the vertical endpoint distance, its contribution is at least `(C-2)g^2/2>=3`. The angular endpoint-square is less than one, and the negative angular contribution is at worst `-8u_y^2>=-2`. This proves (P).

A downward vertical wrap has curvature at least `1/2`, so the same estimate applies. The potential is nonnegative and bounded by `C+1`.

Thus every rational feasible LP solution with rational positive gaps yields a genuine bounded-potential torus block. An exact rectangle/grid-density certificate and the tensor/shell/slope transfer remain necessary to obtain the final lower-bound theorem. Floating-point or merely nodal feasibility is insufficient.
