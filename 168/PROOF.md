# Natural and upper densities of sets avoiding $n,2n,3n$

Call a set $A\subseteq\mathbb N_{>0}$ **triple-free** if it contains no
$\{n,2n,3n\}$ with $n\geq1$. Write
$
A(N)=|A\cap\{1,\ldots,N\}|,
\qquad
\overline d(A)=\limsup_{N\to\infty}\frac{A(N)}N.
$
When the corresponding limit exists, denote it by $d(A)$.

Erdős and Graham separately asked whether the upper density of an infinite
triple-free set can exceed the densities obtainable by such sets whose natural
density exists. The question appears on printed page 336 of their 1979 paper.
The theorem below answers that comparison affirmatively. It does not determine
the greatest possible natural density, evaluate the finite-extremal density
constant, or decide its irrationality. Those are different questions appearing
alongside it in the original source and under modern problem #168.
[Erdős–Graham, p. 336](https://static.renyi.hu/~p_erdos/1979-07.pdf)

## Theorem

Let
$
F(N)=\max\{|S|:S\subseteq\{1,\ldots,N\}\text{ is triple-free}\},
\qquad
\lambda=\limsup_{N\to\infty}\frac{F(N)}N.
$
There is an infinite triple-free set $B$ such that
$
\overline d(B)=\lambda,
$
whereas every triple-free set $A$ whose natural density exists satisfies
$
\boxed{\quad d(A)\leq\lambda-\frac1{192}.\quad}
$
In particular, $\overline d(B)>d(A)$ for every such $A$.

The proof uses only the limsup defining $\lambda$. It does not assume the
known convergence of $F(N)/N$.

## 1. A finite incompatibility at two scales

For every triple-free $A\subseteq\mathbb N_{>0}$ and every integer $K\geq0$,
we claim that
$
A(48K)+A(144K)+K\leq F(48K)+F(144K). \tag{1}
$
The case $K=0$ is immediate. Suppose $K\geq1$, and set
$
m_i=18K+6i+1\qquad(0\leq i<K).
$
These are $K$ distinct integers satisfying
$
18K<m_i<24K,\qquad \gcd(m_i,6)=1.
$

Every positive integer has a unique expression $m2^a3^b$, with
$\gcd(m,6)=1$ and $a,b\geq0$. Thus the sets
$
\mathcal C_m=\{m2^a3^b:a,b\geq0\}
$
partition the positive integers. Each forbidden triple lies wholly within
one such set. Consequently the finite optimum $F(N)$ is the sum of the
optima on the finite sets $\mathcal C_m\cap[1,N]$.

For each chosen $m=m_i$, the bounds on $m$ give
$
\mathcal C_m\cap[1,48K]=m\{1,2\},
\qquad
\mathcal C_m\cap[1,144K]=m\{1,2,3,4,6\}.
$
Indeed, $2<48K/m<3$ and $6<144K/m<8$, and the positive
$3$-smooth integers below $8$ are $1,2,3,4,6$.

The optimum on the first set is $2$. The optimum on the second is $4$,
uniquely attained by
$
m\{1,3,4,6\}.
$
To see uniqueness, its only forbidden triples are $m\{1,2,3\}$ and
$m\{2,4,6\}$. Their only common point is $2m$, so deleting one point
hits both triples only when that point is $2m$.

If $A$ contains both $m$ and $2m$, it has at most three points in the
five-point set: $3m$ is forbidden, and at most one of $4m,6m$ can be
present. Otherwise it has at most one point in the two-point set. Therefore
its two deficits on this component obey
$
\bigl(2-|A\cap m\{1,2\}|\bigr)
+\bigl(4-|A\cap m\{1,2,3,4,6\}|\bigr)\geq1.
$
Sum over the $K$ distinct components. Every other component has
nonnegative deficit at each cutoff, proving (1).

This is also a local-exchange argument. A missing $2m$ can be added at
the smaller cutoff. If $2m$ is present, then at the larger cutoff one may
remove it and add a missing member of each of the pairs
$\{m,3m\}$, $\{4m,6m\}$, gaining one point. Distinct components do
not interfere. These exchanges are the route used in the accompanying
formal verification.

## 2. The bound for natural density

Suppose $d(A)=d$ exists. Divide (1) by $K$, obtaining
$
48\frac{A(48K)}{48K}
+144\frac{A(144K)}{144K}+1
\leq
48\frac{F(48K)}{48K}
+144\frac{F(144K)}{144K}.
$
The left side tends to $192d+1$. For every $\varepsilon>0$, the
definition of $\lambda$ gives
$F(N)/N\leq\lambda+\varepsilon$ for all sufficiently large $N$.
Hence
$
192d+1\leq192(\lambda+\varepsilon).
$
Letting $\varepsilon\downarrow0$ proves
$d\leq\lambda-1/192$.

## 3. Attaining the upper density

We construct $B$ from widely separated finite optimizers. Put $N_0=1$.
By the defining property of a limsup, choose recursively integers $N_k$
such that
$
N_k>3kN_{k-1},
\qquad
\frac{F(N_k)}{N_k}>\lambda-\frac1k.
$
Let $S_k\subseteq[1,N_k]$ be triple-free with $|S_k|=F(N_k)$, and define
$
B=\bigcup_{k\geq1}\bigl(S_k\cap(3N_{k-1},N_k]\bigr).
$

Each block is triple-free. A forbidden triple meeting two different blocks
would have a smallest member at most $N_{k-1}$ and a largest member greater
than $3N_{k-1}$, where $k$ is the index of its last block. This is
impossible: the largest member of $\{n,2n,3n\}$ is exactly three times
the smallest. Thus $B$ is triple-free.

At the selected cutoffs,
$
\frac{B(N_k)}{N_k}
\geq\frac{F(N_k)-3N_{k-1}}{N_k}
>\lambda-\frac2k.
$
It follows that $\overline d(B)\geq\lambda$. Conversely, every finite
prefix of $B$ is triple-free, so $B(N)\leq F(N)$ and
$\overline d(B)\leq\lambda$. Therefore $\overline d(B)=\lambda$.

Finally, $(N/3,N]\cap\mathbb N$ is triple-free, which gives
$\lambda\geq2/3$. In particular $\overline d(B)>0$, so $B$ is
infinite. This completes the proof.

## Context and verification

The decomposition by $m2^a3^b$, and the finite-extremal density framework,
are classical. Graham, Spencer and Witsenhausen proved convergence and gave
a series for the finite-extremal density. Chapman's treatment of
multiplicatively syndetic sets provides a complementary formulation and
carefully distinguishes density notions. These results are background;
their convergence conclusions are not needed in the proof above.
[Graham–Witsenhausen–Spencer, *On Extremal Density Theorems for Linear Forms*, 1977, pp. 103–109](https://mathweb.ucsd.edu/~ronspubs/77_05_extremal_density.pdf);
[Chapman, *Partition Regularity and Multiplicatively Syndetic Sets*, §3, Theorem 3.2](https://arxiv.org/html/1902.01149#S3).

The five-point incompatibility is already explicit in Proposition 6.2 of
Veselinov's paper: optimal subsets of successive smooth prefixes cannot
always be chosen nested. Its local witness is credited here. The argument
above repeats that witness on a linear number of disjoint components and
compares two scales, yielding the stated uniform density separation.
[Veselinov, *Extremal densities for forbidden configurations in $S$-smooth numbers*, Proposition 6.2, 2026](https://arxiv.org/html/2604.15515v1#S6).

The theorem with the displayed $1/192$ constant has been formalized in
Lean. The final theorem is `Erdos168.uniform_density_separation` in
[lean/Erdos168.lean](lean/Erdos168.lean); its checked dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`. The proof establishes the independently
posed infinite-density comparison, not the value or irrationality questions
in modern problem #168. No assertion of exhaustive bibliographic novelty is
made here.
