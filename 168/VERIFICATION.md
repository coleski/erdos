# Formal verification

## Exact result

`Erdos168.infinite_density_comparison` proves `InfiniteDensityComparison`
with no hypotheses. Its definition is in `lean/Erdos168Core.lean`:
one positive infinite triple-free set $B$ is chosen before quantifying over
every positive triple-free set $A$ and every real number $d$ that is its
natural density. The conclusion is $d<\overline d(B)$.

`Erdos168.uniform_density_separation` proves the stronger gap $1/192$ and
that $B$ attains the limsup of the finite extremal ratios. No convergence
theorem for those ratios is assumed.

## Reproduce

With Elan installed, from a fresh checkout:

```sh
cd 168/lean
lake exe cache get
lake build
lake env lean Erdos168.lean
```

For a repeated clean local-proof build, run `lake clean` followed by
`lake build` from the same directory. The checked-in manifest pins the
transitive dependencies.

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `141f6b6455959bfeb0b2a6b04118031191d62683`.

The final command prints:

```text
'Erdos168.uniform_density_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos168.infinite_density_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no admitted steps, custom mathematical axioms, or unchecked
native-evaluation dependencies in either final theorem.

## Build actually performed

On 15 September 2026 UTC, all five source files were copied into a fresh
package directory with no local proof artifacts. `lake build` rebuilt
Core, Upper, Finite, Limit, and the final Erdos168 module and exited
successfully: `Build completed successfully (8926 jobs).` Existing external
Mathlib and dependency caches were reused; they were not rebuilt from
source. No local proof `.olean` files were copied or reused. The installed
Lean compiler and external library caches are part of the trusted build
environment.

The build used Lean 4.34.0-rc2 on arm64 macOS, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`.

## Correspondence review

Separate Codex agent runs reviewed the mathematics and formal statement;
this is independent agent review, not a claim of external human review.
One reviewer authored none of the five modules, read every source and the
original printed page, and independently elaborated all five sources.
A second reviewer independently checked the finite exchanges, limit
argument, and final discharge. Both reported PASS.

The reviews specifically checked positive integers, inclusive counts,
natural rather than logarithmic density, bounded real limsups, all cutoffs,
the same witness for all comparators, genuine infinitude, and the discharge
of the intermediate `FiniteGap` premise. The selected question is the
original infinite-density comparison, not the separate irrationality or
exact-value questions.

The original review records are preserved in
[formal correspondence](audits/formal-correspondence.md) and
[finite and limit arguments](audits/finite-and-limit.md). Their working-folder
names refer to the research snapshot; the source hashes match this package.
The final readable proof also passed a separate complete-text audit at SHA256
`1b27a2b3a3e638dce0d406612f466fb4a91cdb3e78c71eb92c3df6b3c4ef7a8c`.

## Audited source hashes (SHA256)

```text
9e20f5421e5c6eb34eebd74d2c1b5e6b501328e71cee4fac504905cfda061320  Erdos168.lean
8b46b2c5966a5062d46ea33010fbe05c52feea03960c18de2001612b2fe9356b  Erdos168Core.lean
1fda852134d180c3e6362441d6eb7919fb31add621d6b2e03fd205de79f060e0  Erdos168Finite.lean
8acc16eafc0b8710cb83da30e4238c95f380f0dbc9e55d7561f65d8160f353fe  Erdos168Limit.lean
8c3a3888ca1f3354f735407310ae958b26bf3c1bfde8b389a4ae2ced095b4fa2  Erdos168Upper.lean
```
