# Prior work and scope

The selected question is the infinite-density comparison explicitly posed
by Erdős and Graham on printed page 336 of their 1979 paper. The question
concerns sets avoiding every positive-integer triple $\{n,2n,3n\}$.
Our theorem compares one infinite set's upper density with the natural
density of every avoiding set for which that limit exists. It is stronger
than finding a single set with unequal lower and upper densities.
[Original source](https://static.renyi.hu/~p_erdos/1979-07.pdf).

## Mathematical antecedents

- Graham, Spencer and Witsenhausen developed the decomposition into
  components $m2^a3^b$, proved convergence of the finite extremal ratios,
  and obtained their series representation. These are classical ingredients,
  not contributions of this note.
  [1977 paper](https://mathweb.ucsd.edu/~ronspubs/77_05_extremal_density.pdf).
- Chapman's Theorem 3.2, attributed there to the 1977 theorem, gives a sharp
  lower-density bound for multiplicatively syndetic sets. Complementation
  yields the corresponding upper-density result for avoiding sets. The
  upper-density attainment in our proof is self-contained but is not claimed
  as a new result.
  [Chapman, §3](https://arxiv.org/html/1902.01149#S3).
- Veselinov's Proposition 6.2 explicitly exhibits the incompatible optima
  on $\{1,2\}$ and $\{1,2,3,4,6\}$. Our proof uses that same five-point
  witness. The additional step is to repeat the incompatibility over a
  linear number of distinct components and compare two cutoffs, obtaining
  a uniform loss for every existing natural density.
  [Veselinov, Proposition 6.2](https://arxiv.org/html/2604.15515v1#S6).
- McNew proves a related natural/logarithmic versus upper-density
  separation for geometric-progression avoidance. The forbidden patterns
  differ, and the prime-palette hypothesis in his extension does not hold
  for $\{2,3\}$. This is related precedent, not the theorem proved here.
  [McNew, §6](https://nathanmcnew.com/GPFsets.pdf).

## Literature check

Checks through 15 September 2026 covered the original source, the complete
1977 paper, the mathematical contents of Chung–Erdős–Graham's 2002 paper,
Chapman's density section, Veselinov's paper and current repository, and
relevant sections of papers on multiplicative syndeticity and
geometric-progression-free sets. Veselinov's arXiv history listed only v1;
his repository's complete current tree contained finite computations and
data, with no infinite-density comparison proof.

We also checked the current problem page, all nine ordinary discussion
comments and the separate proof-claims tab, Jig's complete returned
problem inventory, relevant GitHub formalizations, and recent arXiv
searches. No earlier proof of this precise comparison was found in the
material inspected. An open label or a missing search result was not
treated as sufficient evidence on its own.

These checks are not exhaustive: unindexed manuscripts and portions of
the older citation literature may remain unchecked. Accordingly, the
priority claim is limited to the absence of an earlier resolution in the
sources inspected, with the overlapping ingredients credited above.

The exact value of the maximum natural density, the evaluation of the
finite-extremal constant, and its irrationality are not resolved here.

Additional source links: [current problem and discussion](https://www.erdosproblems.com/forum/thread/168),
[Chung–Erdős–Graham](https://mathweb.ucsd.edu/~fan/wp/linear.pdf),
[Veselinov repository](https://github.com/nikolaveselinov/s-smooth-forbidden-configurations),
[Bergelson–Glasscock](https://arxiv.org/html/1610.09771v4),
[Jig inventory](https://jig.so/api/problems?limit=500&offset=0).
