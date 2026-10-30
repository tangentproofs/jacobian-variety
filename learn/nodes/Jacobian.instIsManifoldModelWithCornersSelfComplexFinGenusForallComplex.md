---
id: Jacobian.instIsManifoldModelWithCornersSelfComplexFinGenusForallComplex
title: The chart changes are holomorphic
summary: Changing charts on the Jacobian is locally just adding a fixed lattice vector, which is why the manifold structure is analytic rather than merely smooth.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — Jacobian/Solution.lean lines 100–101. The id used on this site is the name Lean is expected to generate, not a name written in the file.'
- 'This instance is not listed in `comparator/jacobian.json` and does not occur in any checked statement — `ContMDiff` needs only `ChartedSpace`, not `IsManifold` — so the harness that compares the solution with the frozen spec does not certify it. The proof is real; it is just checked by reading.'
- 'The smoothness exponent is `ω`, written `(⊤ : WithTop ℕ∞)` in the torus layer: analytic, the strongest level in Mathlib''s hierarchy. The model is `modelWithCornersSelf ℂ (Fin (genus X) → ℂ)`, a boundaryless model on ℂ^g, so "complex manifold of dimension g" is the right reading.'
- 'The instance body for the torus is an empty `where` (Jacobian/ComplexTorus/IsManifold.lean lines 66–68) and for the `ULift` likewise (Jacobian/ComplexTorus/ULiftTransport.lean lines 134–138). The content lives entirely in the `HasGroupoid` instances those bodies pick up, at Jacobian/ComplexTorus/IsManifold.lean lines 26–60 and Jacobian/ComplexTorus/ULiftTransport.lean lines 116–126.'
- 'The compatibility is checked only for pairs of charts from the chosen atlas (one chart per point), since the atlas is the range of `chartAtPoint`. That is what `HasGroupoid` requires; it is not a statement about all possible charts.'
quiz:
- q: Why is a chart transition on the Jacobian holomorphic?
  type: choice
  choices:
  - Near each overlap point it agrees with the translation `y ↦ y + g` for a locally fixed lattice vector `g`
  - Because the projection from ℂ^g is holomorphic and that is enough
  - Because every continuous map between open subsets of ℂ^g is holomorphic
  answer: 0
  explain: The file docstring of Jacobian/ComplexTorus/TransitionContDiffOn.lean lines 9–14 says the transition agrees with `y ↦ y + g` on a neighbourhood of each overlap point, and concludes by `ContDiffWithinAt.congr_of_eventuallyEq`.
- q: What level of regularity is proved?
  type: choice
  choices:
  - Analytic (`ω`), the top of Mathlib's smoothness hierarchy
  - Continuously differentiable once
  - Smooth but not analytic
  answer: 0
  explain: 'Jacobian/Challenge.lean line 84 asks for `IsManifold … ω …`, and the torus instance at Jacobian/ComplexTorus/IsManifold.lean lines 66–68 is over `(⊤ : WithTop ℕ∞)`, which is `ω`.'
- q: What does the `IsManifold` instance body contain?
  type: choice
  choices:
  - Nothing; it is an empty `where`, and the work is in the `HasGroupoid` instance it relies on
  - A proof that the Jacobian is a torus
  - The construction of the charts
  answer: 0
  explain: Jacobian/ComplexTorus/IsManifold.lean lines 66–68 end with `where` and no fields; `complexTorusHasGroupoid` at Jacobian/ComplexTorus/IsManifold.lean lines 26–60 carries the two `ContDiffOn ℂ ω` checks.
- q: How many `ContDiffOn` checks does the groupoid obligation reduce to?
  type: choice
  choices:
  - Two — the transition in each direction
  - One
  - One per lattice vector
  answer: 0
  explain: Jacobian/ComplexTorus/IsManifold.lean line 43 is `refine ⟨?_, ?_⟩`, the forward and inverse directions, each closed by `contDiffOn_localSection_mk` with the two representatives swapped at Jacobian/ComplexTorus/IsManifold.lean line 52 and Jacobian/ComplexTorus/IsManifold.lean line 60.
---
## Plain English

A charted space becomes a manifold once you check that passing from one chart to another is as smooth as you want it. For the Jacobian the check is pleasant, because the charts are all built the same way: each one inverts the projection ℂ^g → ℂ^g/Λ on a small ball around a chosen representative.

Take two charts, around representatives `v₁` and `v₂`. On the overlap, the transition takes a point `y` near `v₁`, projects it to the torus, and then finds the representative near `v₂`. The two representatives of the same torus point differ by a lattice vector. Locally that lattice vector cannot jump — the balls are small enough that only one works — so the transition is `y ↦ y + g` for a fixed `g` in the lattice (Jacobian/ComplexTorus/TransitionContDiffOn.lean lines 9–14). Translation is analytic. Done.

## How the Lean organizes it

Mathlib splits this into `HasGroupoid` (the transitions lie in a given groupoid of maps) and `IsManifold` (which, for these models, is that plus bookkeeping). The real proof is `complexTorusHasGroupoid` (Jacobian/ComplexTorus/IsManifold.lean lines 26–60): unfold the groupoid membership to two `ContDiffOn ℂ ω` statements, one per direction, and discharge each with the translation lemma. The `IsManifold` instance itself has an empty body (Jacobian/ComplexTorus/IsManifold.lean lines 66–68).

For `Jacobian X`, which is a `ULift` of the torus, the same pattern repeats one level up. The lifted transition is shown to coincide, on its source, with the unlifted one (Jacobian/ComplexTorus/ULiftTransport.lean lines 100–108), so membership in the groupoid transfers (Jacobian/ComplexTorus/ULiftTransport.lean lines 116–126), and the `IsManifold` instance is again empty (Jacobian/ComplexTorus/ULiftTransport.lean lines 134–138).

## What this buys the challenge

With this instance plus [ChartedSpace](#/node/Jacobian.instChartedSpaceForallFinGenusComplex), the Jacobian is a complex manifold of dimension exactly the genus, and the regularity is `ω`, analytic, not just smooth. The holomorphy statements [ofCurve_contMDiff](#/node/Jacobian.ofCurve_contMDiff), [pushforward_contMDiff](#/node/Jacobian.pushforward_contMDiff) and [pullback_contMDiff](#/node/Jacobian.pullback_contMDiff) are also at level `ω`; strictly they need only the charts, since Mathlib's `ContMDiff` is stated for a charted space. Adding the smooth group law on top gives [LieAddGroup](#/node/Jacobian.instLieAddGroupModelWithCornersSelfComplexFinGenusForallComplex), and that instance together with compactness and the ℂ^g charts is what rules out a trivial fake Jacobian.
