---
id: ComplexTorus.FullComplexLattice
title: A lattice that carries its own evidence
summary: Discreteness is a separate field of this structure, not a consequence of the others, because a closed subgroup with a compact fundamental domain need not be discrete.
review: draft
authors:
- claude
caveats:
- 'This is a project-local structure, not Mathlib''s `ZLattice`/`IsZLattice`. The docstring says so explicitly: "A more polished implementation could replace these fields with established Mathlib predicates such as `ZLattice.IsZLattice`" (Jacobian/ComplexTorus/Defs.lean lines 53–55).'
- 'The ambient space `V` is only assumed to be a complex normed space. `FiniteDimensional ℂ V` is *not* a hypothesis of the structure (Jacobian/ComplexTorus/Defs.lean lines 32–33), so "full complex lattice in a finite-dimensional complex vector space" (the docstring) is a description of intended use, not of the definition.'
- 'No field records a rank. "Full" is encoded indirectly, by the compact fundamental domain. For the period lattice the rank is recovered later, from discreteness plus ℝ-spanning, by Mathlib''s `ZLattice` machinery (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 47–59).'
- '`fundamentalDomain` is *data*: a particular chosen set. Two terms of this structure with the same subgroup but different chosen domains are different terms. In the period-lattice case the domain is produced by `Classical.choose` (Jacobian/Periods/GenuinePeriodLatticeDiscrete.lean lines 80–87).'
quiz:
- q: Why does `FullComplexLattice` carry `isDiscrete` as its own field instead of deriving it?
  type: choice
  choices:
  - Because a closed subgroup with a compact fundamental domain need not be discrete; the docstring gives ℝ × ℤ ⊂ ℝ² as a counterexample
  - Because Lean cannot prove discreteness of any subgroup
  - Because discreteness follows from `isClosed` but Mathlib lacks the instance
  answer: 0
  explain: The docstring at Jacobian/ComplexTorus/Defs.lean lines 45–51 names the counterexample `ℝ × ℤ ⊂ ℝ²` and says discreteness "has to be witnessed explicitly".
- q: What does the structure assume about the ambient space `V`?
  type: choice
  choices:
  - That it is a normed additive commutative group and a normed space over ℂ, with no finite-dimensionality
  - That it is finite-dimensional over ℂ
  - That it is exactly `Fin g → ℂ`
  answer: 0
  explain: The `variable` line at Jacobian/ComplexTorus/Defs.lean lines 32–33 lists only `NormedAddCommGroup` and `NormedSpace ℂ`; `FiniteDimensional` appears later, in the chart and manifold files, not in this structure.
- q: Which field is used to make the quotient compact?
  type: choice
  choices:
  - '`fundamentalDomain` together with `fundamentalDomain_isCompact` and `fundamentalDomain_covers`'
  - '`isClosed`'
  - '`isDiscrete`'
  answer: 0
  explain: '`quotient_compactSpace` at Jacobian/ComplexTorus/Defs.lean lines 118–121 feeds exactly those three fields into `compactSpace_quotient_of_cover`.'
- q: Does a term of `FullComplexLattice V` record a ℤ-basis of the lattice?
  type: choice
  choices:
  - No; it records a subgroup plus topological and covering facts, and a chosen fundamental domain
  - Yes, a `Module.Basis` field
  - Yes, implicitly, as the rank of the subgroup
  answer: 0
  explain: The six fields at Jacobian/ComplexTorus/Defs.lean lines 57–69 are `subgroup`, `isClosed`, `isDiscrete`, `fundamentalDomain`, `fundamentalDomain_isCompact`, `fundamentalDomain_covers`. No basis appears.
---
## Plain English

A lattice in ℂ^g is the classical picture of a grid of points: integer combinations of 2g independent real directions. Quotienting ℂ^g by such a grid gives a torus. The Jacobian of a Riemann surface is exactly such a quotient, so the project needs a precise notion of "grid good enough to quotient by".

`FullComplexLattice V` is that notion, written as a bundle of one subgroup plus the facts about it that the later construction will need (Jacobian/ComplexTorus/Defs.lean lines 57–69):

- `subgroup : AddSubgroup V` — the grid itself, as an additive subgroup of `V`.
- `isClosed` — the subgroup is a closed subset. This is what makes the quotient Hausdorff ([quotient_t2Space](#/node/ComplexTorus.quotient_t2Space), Jacobian/ComplexTorus/Defs.lean lines 86–88).
- `isDiscrete` — the subgroup is discrete in its subspace topology. This is what gives small balls on which the projection is injective, hence charts.
- `fundamentalDomain`, with proofs that it is compact and that its translates by the subgroup cover all of `V`. This is what makes the quotient compact ([quotient_compactSpace](#/node/ComplexTorus.quotient_compactSpace), Jacobian/ComplexTorus/Defs.lean lines 118–121).

## Why discreteness is its own field

One might expect discreteness to come for free from "closed" plus "cocompact". It does not. The docstring gives the counterexample: ℝ × ℤ sitting inside ℝ² is closed, and its translates by the ℤ direction cover the plane from a compact strip, but it is not discrete — it contains a whole line. So the field has to be assumed, and the docstring says so (Jacobian/ComplexTorus/Defs.lean lines 45–51).

Because discreteness will be needed everywhere downstream, it is registered as a global instance (Jacobian/ComplexTorus/Defs.lean line 71).

## What "full" does and does not mean here

There is no field saying "the subgroup has rank 2g" or "the subgroup spans `V` over ℝ". Fullness is carried indirectly, by the compact fundamental domain: if `V` is nonzero and the subgroup were too small, no compact set could cover `V` by translates. For the actual period lattice, spanning is proved separately as [periodLattice_span](#/node/Periods.periodLattice_span) and then converted into a compact fundamental domain.

What the conditions do rule out is total collapse. A normed space carries the discrete topology only if it is zero, so for nonzero `V` the subgroup cannot be all of `V`, and the quotient cannot be a single point.
