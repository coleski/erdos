# #168: independent finite/limit/final-interface audit

Verdict: PASS, with no corrections requested. This audits the original
independently posed infinite-density comparison, not the separate density
value or irrationality questions. Novelty is not certified by this audit.
No audited source file was edited.

## Frozen sources read completely

All paths below are in `lean168/`.

| File | SHA256 |
| --- | --- |
| Erdos168Core.lean | 8b46b2c5966a5062d46ea33010fbe05c52feea03960c18de2001612b2fe9356b |
| Erdos168Finite.lean | 1fda852134d180c3e6362441d6eb7919fb31add621d6b2e03fd205de79f060e0 |
| Erdos168Limit.lean | 8acc16eafc0b8710cb83da30e4238c95f380f0dbc9e55d7561f65d8160f353fe |
| Erdos168.lean | 9e20f5421e5c6eb34eebd74d2c1b5e6b501328e71cee4fac504905cfda061320 |

The imported Upper module is frozen at
`8c3a3888ca1f3354f735407310ae958b26bf3c1bfde8b389a4ae2ced095b4fa2`.
I authored that module; its independent audit belongs to the parent, so this
report does not mislabel my own construction as independently reviewed.

I also reread `ROOT-168-INFINITE-DENSITY-TARGET.md`. My preceding human audit
independently visually checked the complete original printed page 336 of
[Erdős–Graham 1979](https://static.renyi.hu/~p_erdos/1979-07.pdf).

## Core correspondence

`TripleFree` excludes every positive integer x with x,2x,3x in the set.
`Positive` excludes zero. Counts use exactly the interval {1,...,N}; thus
finite-set and positive-integer conventions match the original. Density is
the real quotient of this count by N. Its value at N=0 does not affect any
atTop limit. Natural density is `Tendsto`, upper density is real `limsup`.
The finite extremum ranges over the full powerset of {1,...,N}, filtered by
the actual forbidden-triple predicate. Its supremum is attained because
the finite candidate family contains the empty set.

The final `InfiniteDensityComparison` quantifies ONE positive infinite
triple-free B, followed by EVERY positive triple-free A and EVERY real d
that is a natural density of A. It requires d<upperDensity B. It is not an
oscillation statement for B alone, nor an assertion restricted to a chosen
family of A, nor a conditional theorem assuming existence of an extremizer.

## Finite module: all-K swap and induction audit

For each K, the roots are exactly

    m_i = 18K+6i+1,  0<=i<K.

They are distinct, there are exactly K, and all satisfy 18K<m<24K and
m congruent to 1 modulo both 2 and 3. For K=0 the family is empty and all
arguments correctly reduce to vacuous or trivial assertions.

At cutoff 48K, the point 2m is isolated from every complete forbidden
triple in the interval. If it is the first member, 3x=6m>48K; if it is
the second, 3x=3m>48K; it cannot be the third because 3 does not divide m.
Thus inserting it in a triple-free S is always safe.

At cutoff 144K, any forbidden triple meeting one of m,3m,4m,6m has base
x=m or x=2m. This is exhaustive, not just a statement about the two visible
triples: checking each of the four possible added values against x,2x,3x
uses parity/divisibility or the upper cutoff. Thus every such triple also
contains 2m. Deleting 2m prevents all newly introduced forbidden triples.

If T contains 2m, it must omit at least one member a of {m,3m} and at least
one member b of {4m,6m}. These two pairs are disjoint. The replacement

    U = (T minus {2m}) union {a,b}

therefore gains exactly one point, remains in the interval, and remains
triple-free. The proof's `hold` argument is valid: a purported new triple
meeting either inserted point would necessarily contain the deleted middle;
otherwise all its points were already in T, also impossible.

Critically, no inserted good value for root m equals 2n for ANY selected
root n. This follows from the common interval for the roots (and positivity).
The sole removed selected middle is 2m. Hence each swap preserves every
remaining selected middle-membership test. The insert-at-small-cutoff case
also changes no other middle, by injectivity of n -> 2n.

`upgrade_roots` only assumes matching middle membership between S and T on
the finite remaining set P. At every induction step it either inserts a
missing isolated small-cutoff middle or swaps a present large-cutoff middle.
The matching premise remains true on P minus {m}. The accumulated cardinality
gain is therefore |P| with no overlap loss. The two updated sets need not
remain nested; the induction does not assume that they do. Initial segments
of one A do satisfy the matching premise because every selected 2m lies
below the smaller cutoff.

Consequently `finite_two_scale_gap` proves, with no premise except
`TripleFree A`, for EVERY natural K,

    A(48K)+A(144K)+K <= F(48K)+F(144K).

This is a uniform exact inequality, not a finite computational verification.
Using only roots 1 modulo 6 produces the formal constant 1/192. The earlier
human argument using both coprime residue classes has 1/96; the weaker formal
constant is still strictly positive and suffices for the exact target.

## Limit module: epsilon arithmetic and infinitude

`FiniteGap` is an explicit proposition containing the preceding all-A/all-K
inequality. The intermediate implication is honestly conditional on it.
Given natural density d and assuming d>lambda-1/192, put

    delta = d-lambda+1/192 > 0,
    epsilon = delta/4 > 0.

The definition of limsup and boundedness give an eventual upper estimate
F(N)/N<lambda+epsilon at ALL sufficiently large N. Natural convergence
gives A(N)/N>d-epsilon at ALL sufficiently large N. Taking
K=max(Nu,Nl)+1 makes both 48K and 144K lie beyond both thresholds, with K>0.
The finite inequality would then require

    192K*(d-lambda-2epsilon)+K < 0,

whereas the left side is 192K*(delta-2epsilon)=96K*delta>0.
The formal `nlinarith` is exactly this contradiction. There is no assumed
convergence of the extremal ratios and no invalid correlation assumption
between the two cutoffs.

The finite-set natural-density-zero lemma bounds A(N) by the fixed finite
cardinality, and squeezes by |A|/N -> 0. Its upper density is consequently
zero. Applying the already proved gap to the empty set yields
lambda>=1/192>0. Therefore the set attaining upper density lambda cannot
be finite. This is not circular: positivity follows from the finite gap
alone, before invoking infinitude of the attaining set.

## Final discharge and exact strength

`Erdos168.lean` defines `finiteGap` by direct application of
`finite_two_scale_gap`; it is a proved theorem, not an axiom or extra final
hypothesis. `uniform_density_separation` has NO premises and asserts an
infinite positive triple-free B attaining lambda, with

    d(A) <= upperDensity(B) - 1/192

for every positive triple-free A whose natural density exists.
`infinite_density_comparison` also has NO premises and proves the frozen
original yes/no target. None of these conclusions asserts irrationality,
computes the maximal natural density, or purports to resolve every question
collected on the modern numbered page.

## Independent compiler readback

Fresh non-mutating Lean invocations in the pinned environment:

- Finite: session25634, exit0; `finite_two_scale_gap` printed standard axioms.
- Limit: session34236, exit0; `natural_gap_of_finiteGap` and
  `comparison_of_finiteGap` printed standard axioms.
- Core: session39172, exit0.
- Final assembled module: session53602, exit0; both final theorems printed
  standard axioms.

In each printed report the complete axiom list was
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom mathematical
axiom, or unchecked decision procedure appears. These successful compiles
support, but do not substitute for, the meaning and mathematical audit above.
