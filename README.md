# Erdős problems

## 168: natural density versus upper density

There is an infinite set $B$ of positive integers containing no triple
$\{n,2n,3n\}$ whose upper density exceeds the natural density of every
such set whose natural density exists. More precisely,

$$
d(A)\leq\overline d(B)-\frac1{192}
$$

for every triple-free $A$ with natural density.

This answers the independently posed infinite-density comparison on
page 336 of [Erdős and Graham's 1979 paper](https://static.renyi.hu/~p_erdos/1979-07.pdf).
It does not determine the extremal constant or its irrationality, the other
questions grouped under [problem #168](https://www.erdosproblems.com/168).

[Complete proof](168/PROOF.md) · [Lean theorem](168/lean/Erdos168.lean) ·
[Verification and build instructions](168/VERIFICATION.md) · [Prior work](168/PRIOR_ART.md)

Cole Benefield, with OpenAI Codex. September 2026.

Thanks to Joshua Wolk for creating Jig, and to Declan Gessel for inspiring
me to try my hand at solving a problem.
