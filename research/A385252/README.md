# A recurrence for ternary words with a minority of zeros

Enrique Navarrete's A385252 counts words of length $2n$ over $\{0,1,2\}$ that contain at least one zero and fewer zeros than nonzero symbols. R. J. Mathar proposed an order-five recurrence for this sequence on 31 July 2025. His formula gives no starting index. We prove that it holds for every $n\ge6$. At $n=5$, the first index at which all terms exist, its left side equals $-6912$. [OEIS A385252](https://oeis.org/A385252)

Let $a_n$ be the word count. The recurrence is

$$
\begin{aligned}
0={}& n a_n+(36-37n)a_{n-1}+4(131n-245)a_{n-2}\\
 &+16(605-221n)a_{n-3}+192(59n-213)a_{n-4}
   +6912(9-2n)a_{n-5}.
\end{aligned}
$$

## Counting after two more symbols

Let $U_n$ count all words with fewer than $n$ zeros, including words with no zeros. Then $U_n=a_n+4^n$ for $n\ge1$. Let $W_j=\binom{2n}{j}2^{2n-j}$ be the number of length-$2n$ words with exactly $j$ zeros. Append two symbols and raise the cutoff from $n$ to $n+1$. There are nine extensions of each word. Only two boundary classes need corrections.

| Zeros before extension | Correction to $9U_n$ | Reason |
|---|---:|---|
| $n-1$ | $-W_{n-1}$ | Appending two zeros gives $n+1$ zeros, one too many. |
| $n$ | $+4W_n$ | Appending two nonzero symbols now qualifies. |

Consequently $U_{n+1}=9U_n+4W_n-W_{n-1}$. Put $b_n=2^n C_n$, where $C_n=\binom{2n}{n}/(n+1)$ is the Catalan number. The two boundary counts are $W_n=(n+1)b_n$ and $W_{n-1}=2nb_n$. Substitution gives the simpler recurrence

$$
a_{n+1}=9a_n+5\cdot4^n+(2n+4)b_n,\qquad
(n+2)b_{n+1}=4(2n+1)b_n \quad(n\ge1).
$$

Starting from $a_1=0$ and $b_1=2$, these identities determine every positive-index count. They give $a_2=32$, $a_3=432$, $a_4=4608$, and $a_5=45440$. The empty word has no zero, so $a_0=0$. Substitution gives the claimed residual at index five.

## Recovering Mathar's coefficients

For $t\ge1$, multiply the first recurrence at $t,t+1,\ldots,t+4$, written with all terms on the left, by the five weights below. Add the four weighted copies of the second recurrence. The $4^t$ and $b$ terms cancel. The coefficients of $a_t,\ldots,a_{t+5}$ give Mathar's formula with $n=t+5$.

| Offset | Weight on the first recurrence | Weight on the second recurrence |
|---:|---:|---:|
| 0 | $1536t+768$ | $-384t-768$ |
| 1 | $-1088t-1664$ | $224t+704$ |
| 2 | $272t+704$ | $-40t-176$ |
| 3 | $-28t-104$ | $2t+12$ |
| 4 | $t+5$ | |

## A shorter homogeneous recurrence

Define $D_n=a_{n+2}-13a_{n+1}+36a_n$. Subtracting four times the first counting identity from its successor gives $(n+2)D_n=8(n^2+3n-1)b_n$. Eliminating $b_n$ between successive indices yields, for all $n\ge1$,

$$
(n+3)(n^2+3n-1)D_{n+1}
=4(2n+1)(n^2+5n+3)D_n .
$$

This determines $a_{n+3}$ from three preceding counts.

## Lean verification

[Proof.lean](Proof.lean) builds from finite sums over functions from $\mathrm{Fin}(2n)$ to $\mathrm{Fin}(3)$. The declarations `solution`, `residual_five`, and `short_recurrence` prove the three results above. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. Run the following in the pinned formal-conjectures checkout with Lean 4.33.1 and its Mathlib cache.

```sh
lake env lean /absolute/path/to/Proof.lean
```

[Formal Conjectures pin 9097e2f](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53)
