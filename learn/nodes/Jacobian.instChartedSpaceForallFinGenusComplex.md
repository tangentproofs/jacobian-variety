---
id: Jacobian.instChartedSpaceForallFinGenusComplex
title: Coordinates on the Jacobian, g of them
summary: Every point of the Jacobian gets its own chart, built by choosing a representative vector in ℂ^g and inverting the projection on a ball of radius δ/4, where δ is a radius below which the period lattice has no nonzero vector.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — Jacobian/Solution.lean lines 98–99. The id used on this site, `Jacobian.instChartedSpaceForallFinGenusComplex`, is the name Lean generates for it; it is recorded in `comparator/jacobian.json`.'
- 'The charts are not canonical. `chartAtPoint` picks a representative of the quotient point with `Function.surjInv`, which uses `Classical.choice`, and picks the isolation radius δ with `.choose` from an existence lemma (Jacobian/ComplexTorus/ChartedSpace.lean lines 32–40). The atlas is the range of this one chosen chart per point, not a maximal atlas.'
- 'The chart radius is the same δ/4 everywhere. The file''s own docstring says this "keeps the construction simple" and that "a real mathlib-bound treatment would prefer either a global δ derived once or per-point optimal radii" (Jacobian/ComplexTorus/ChartedSpace.lean lines 18–20).'
- '`ChartedSpace` alone is weaker than "complex manifold". It says the space is covered by homeomorphisms onto open subsets of ℂ^g; it says nothing about the chart transitions. Holomorphy of the transitions is the separate [IsManifold](#/node/Jacobian.instIsManifoldModelWithCornersSelfComplexFinGenusForallComplex) instance.'
- 'The model space is `Fin (genus X) → ℂ`, coordinates with respect to an arbitrary chosen basis of holomorphic 1-forms, not the invariant dual H⁰(X, Ω¹)*. See [Jacobian](#/node/Jacobian).'
quiz:
- q: How is the chart at a Jacobian point built?
  type: choice
  choices:
  - Choose a representative vector `v` in ℂ^g, then invert the projection on the ball of radius δ/4 around `v`
  - Pull back a chart from the surface along the Abel–Jacobi map
  - Use the exponential map of a Riemannian metric
  answer: 0
  explain: '`chartAtPoint` at Jacobian/ComplexTorus/ChartedSpace.lean lines 32–40 sets `v := Function.surjInv (mk_surjective V Λ) q` and returns `chartAtBall Λ v …`, whose `toFun` is the local section of the projection (Jacobian/ComplexTorus/Chart.lean lines 29–45).'
- q: Why is the radius δ/4 rather than something arbitrary?
  type: choice
  choices:
  - δ is a lower bound on the length of every nonzero lattice vector, so on a ball of radius under δ/2 the projection is injective
  - δ/4 is the diameter of the fundamental domain
  - δ is the genus
  answer: 0
  explain: '`chartAtBall` requires `hr_lt : r < δ / 2` together with `hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖` (Jacobian/ComplexTorus/Chart.lean lines 29–33), and `chartAtPoint` supplies `δ / 4 < δ / 2`.'
- q: Which field of the lattice bundle produces δ?
  type: choice
  choices:
  - '`isDiscrete`, through `exists_pos_le_norm_of_discreteTopology`'
  - '`isClosed`'
  - '`fundamentalDomain_isCompact`'
  answer: 0
  explain: Jacobian/ComplexTorus/ChartedSpace.lean lines 36–39 call `exists_pos_le_norm_of_discreteTopology Λ.subgroup`, which needs the discrete topology registered as an instance at Jacobian/ComplexTorus/Defs.lean line 71.
- q: Does this instance establish that the Jacobian is a complex manifold?
  type: choice
  choices:
  - No; it supplies charts to ℂ^g, and holomorphy of the transitions is the separate `IsManifold` instance
  - Yes, a charted space on ℂ^g is a complex manifold by definition
  - Yes, because the charts are built from a holomorphic projection
  answer: 0
  explain: Jacobian/Challenge.lean line 78 marks the `ChartedSpace` requirement `-- data`, and Jacobian/Challenge.lean line 83 marks the `IsManifold` requirement `-- Prop`; they are two separate obligations.
- q: How does the `ULift` wrapper affect the charts?
  type: choice
  choices:
  - Each chart is composed with the homeomorphism `ULift M ≃ₜ M`, leaving the model space ℂ^g unchanged
  - The model space is lifted to a higher universe too
  - The charts are rebuilt from scratch on the lifted type
  answer: 0
  explain: '`complexTorusULiftChartAt` at Jacobian/ComplexTorus/ULiftTransport.lean lines 66–71 is `Homeomorph.ulift.transOpenPartialHomeomorph (chartAtPoint Λ q.down)`, and the instance at Jacobian/ComplexTorus/ULiftTransport.lean lines 79–88 keeps the model `V`.'
---
## Plain English

To say the Jacobian is a complex manifold of dimension `g`, you first have to put coordinates on it: around every point, a patch that looks like an open piece of ℂ^g. The specification asks for exactly this, with the model space `Fin (genus X) → ℂ`, so the dimension is forced to equal the genus (Jacobian/Challenge.lean lines 78–81).

The construction is the classical one for a torus. Near any point, the projection ℂ^g → ℂ^g/Λ is injective, provided you stay in a ball smaller than half the shortest nonzero lattice vector — otherwise two points of the ball could differ by a lattice vector and get glued. So invert the projection on such a ball, and you have a chart.

Three steps in the Lean (Jacobian/ComplexTorus/ChartedSpace.lean lines 32–40):

1. Pick a representative `v` in ℂ^g for the torus point `q`, using surjectivity of the projection.
2. Extract a radius δ > 0 below which the lattice has no nonzero vectors. This is where discreteness of the period lattice is cashed in.
3. Build the chart as the inverse of the projection on the ball of radius δ/4 around `v`, with source the image of that ball and target the ball itself (Jacobian/ComplexTorus/Chart.lean lines 29–45).

The atlas is the collection of these charts, one per point (Jacobian/ComplexTorus/ChartedSpace.lean lines 65–70).

## What is chosen

Both the representative and the radius are choices. There is no canonical representative of a point of a quotient, and `Function.surjInv` makes an arbitrary pick. The radius δ is likewise `.choose`d from an existence statement, and then used uniformly at every point rather than optimized locally. None of this affects the mathematics — any choice gives a valid atlas — but it does mean the charts are not objects you can compute with or name.

## What still has to be proved

A charted space is just a cover by coordinate patches. For the Jacobian to be a complex manifold the transition between two overlapping charts must be holomorphic. On a torus the transition is a translation by a lattice vector, which is as holomorphic as anything gets, and that is the content of the next instance, [IsManifold](#/node/Jacobian.instIsManifoldModelWithCornersSelfComplexFinGenusForallComplex).

For the Jacobian itself the whole structure is carried across the `ULift` wrapper by composing each chart with the trivial homeomorphism `ULift M ≃ₜ M` (Jacobian/ComplexTorus/ULiftTransport.lean lines 66–88). The model space does not move.
