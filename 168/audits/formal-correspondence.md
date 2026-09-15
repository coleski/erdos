# #168 independent formal correspondence audit

Verdict: PASS for the exact original independent infinite-density comparison. This is not an audit verdict resolving every clause of modern #168, proving irrationality, or guaranteeing novelty. The auditor authored none of these Lean modules and made no edits to them.

## Materials actually read

I read all five current Lean source files: Erdos168Core, Erdos168Finite, Erdos168Upper, Erdos168Limit, and the final Erdos168 aggregator. I read the complete frozen ROOT-168-INFINITE-DENSITY-TARGET.md. I independently visually inspected the complete saved original printed page336 (`combinatorics/source-168-ErGr79-page336.png`), including the paragraph asking the infinite-sequence density and upper-density questions. The primary is [Erdős–Graham1979](https://static.renyi.hu/~p_erdos/1979-07.pdf), PDF page12.

The final formal theorem establishes one positive infinite avoiding set B with upper density u, such that every positive avoiding set A having natural density d satisfies d≤u−1/192. The same B works for every A and every density d. This implies the separately posed original yes/no comparison, not merely unequal lower and upper densities of a single set.

## Definitions and quantifiers

- `TripleFree A` forbids x,2x,3x together for every natural x>0. The three values are distinct. The positive restriction is not vacuous and does not accidentally include the degenerate x=0 triple.
- `Positive A` excludes0. Both the constructed witness and every comparator in the final theorem satisfy this. Intermediate stronger lemmas allow0, harmlessly, because counts always filter the inclusive interval [1,N].
- `count` is literal finite cardinality, with no enumeration multiplicity or off-by-one offset. `density` casts to real division. At N=0 its value is0; one initial cutoff does not affect the atTop limits.
- `HasNaturalDensity` is ordinary convergence of count(A,N)/N along all natural cutoffs. It is not logarithmic density, a selected subsequence, or a condition merely asserting a limsup.
- `upperDensity` is the real limsup atTop. For every set, density is proved in [0,1], supplying the boundedness and coboundedness hypotheses needed to give this limsup its ordinary meaning. The extremal ratios have corresponding bounds.
- `extremal` is the maximum of the cardinalities of all avoiding subsets of [1,N]. The candidate family is nonempty, an actual maximizing witness is proved, and all avoiding prefixes are bounded by it. There is no imported extremal-density axiom.
- `InfiniteDensityComparison` existentially chooses one positive infinite B before universally quantifying A,d. Finite comparators are included and have density0. Infinite comparators are not excluded or restricted to any special construction.

## Finite mathematical interface

The formal arithmetic deliberately selects only K roots m=18K+6i+1, 0≤i<K. They lie in (18K,24K) and are coprime to2 and3. The smaller cutoff is48K and the larger144K.

At the small cutoff, 2m cannot occur in any contained forbidden triple and can be inserted if missing. At the large cutoff, a set containing2m misses at least one of {m,3m} and one of {4m,6m}; erasing2m and inserting those two values increases cardinality by1. The `root_good_closed` lemma checks all possible incidences of inserted values with triples at the large cutoff. The only possible affected triples use the erased2m. The root-range/congruence lemmas prevent changing another root's midpoint membership.

`upgrade_roots` inductively preserves the matching midpoint-membership condition between the two prefixes at every remaining root. Its input is satisfied by two prefixes of the SAME fixed infinite A. This point is essential: it does not incorrectly impose compatibility on unrelated finite optimizers. The final result is the unconditional inequality

    count A (48K) + count A (144K) + K
      ≤ extremal (48K) + extremal (144K).

K=0 is permitted and harmless. Positive K is explicitly chosen when dividing in the limit argument. Natural-number subtraction is avoided throughout this inequality.

## Upper-density attainment and infinity

The cutoff sequence is strictly increasing. Each new block is a finite extremizer restricted to values greater than three times the previous cutoff. The proof shows that two selected elements within a factor3 must come from the same block; hence a forbidden triple cannot span different blocks. This includes triples potentially touching three blocks, not only adjacent-block cases.

Deleting the initial range costs at most three times the previous cutoff. The next cutoff is chosen far enough away to make this loss small, while its extremal ratio approximates the extremal limsup. This yields equality `upperDensity upperSet = upperExtremal` without assuming convergence of the finite ratios or invoking GSW1977.

Infinity is not left as an implicit consequence of the construction: the Limit module proves every finite set has upper density0, proves upperExtremal>0 using the finite gap applied to the empty comparator, and derives B.Infinite. This reasoning is not circular: the finite gap is first proved for all sets/cutoffs and then discharged in the aggregator.

## Limit and final discharge

`FiniteGap` is a named proposition, not an axiom. The aggregator supplies its proof directly from `finite_two_scale_gap`, so the final result has no gap hypothesis. `natural_gap_of_finiteGap` uses eventual upper bounds on the extremal ratio and eventual lower bounds on the natural density at BOTH48K and144K. It concludes

    d ≤ upperExtremal − 1/192.

This weaker constant, compared with the preliminary human candidate1/96, reflects the use of only m≡1 mod6. It is sufficient for the exact frozen question; the formal artifact must not be advertised as proving1/96. The final strict inequality follows from the positive rational1/192, not from an unproved strict supremum inequality.

The existence of a strictly increasing sequence enumerating any infinite subset of positive integers is the ordinary set/sequence correspondence. The formal target uses its range as a set, as the frozen target explicitly permits. There is no ordering-sensitive property being lost: avoidance and both densities depend only on that range.

## Independent compilation and axioms

I independently compiled the final `Erdos168.lean` with the pinned sibling mathlib environment and the local lean168 import path. The process exited0 with no warnings. Both final printouts were exactly:

    Erdos168.uniform_density_separation:
      [propext, Classical.choice, Quot.sound]
    Erdos168.infinite_density_comparison:
      [propext, Classical.choice, Quot.sound]

No `sorryAx`, unproved mathematical axiom, unchecked native-decision axiom, or hidden FiniteGap premise occurs in these final dependencies. This independent compile used existing imported local oleans; the parent's separate clean build remains the gate establishing fresh dependency reconstruction. I additionally elaborated the current sources of Core, Finite, Upper and Limit independently: all four passed, the combined process exited0, and every printed intermediate dependency list contained only the same three standard axioms. No warnings were returned.

## Exact SHA256 source manifest

| Source | SHA256 |
|---|---|
| Erdos168.lean | 9e20f5421e5c6eb34eebd74d2c1b5e6b501328e71cee4fac504905cfda061320 |
| Erdos168Core.lean | 8b46b2c5966a5062d46ea33010fbe05c52feea03960c18de2001612b2fe9356b |
| Erdos168Finite.lean | 1fda852134d180c3e6362441d6eb7919fb31add621d6b2e03fd205de79f060e0 |
| Erdos168Limit.lean | 8acc16eafc0b8710cb83da30e4238c95f380f0dbc9e55d7561f65d8160f353fe |
| Erdos168Upper.lean | 8c3a3888ca1f3354f735407310ae958b26bf3c1bfde8b389a4ae2ced095b4fa2 |
| ROOT-168-INFINITE-DENSITY-TARGET.md | edda691bec0e7c75611fd3c684bdcd493ca860254f7032df826a821b4d6fdc89 |

The target note still contains historical pending-gate language and the stronger candidate constant. The exact theorem above, not that stale candidate-status prose, is what was audited. Prior-art qualifications are separately recorded in Round75 and Round76. No original irrationality or exact-density-value claim is authorized by this audit.
