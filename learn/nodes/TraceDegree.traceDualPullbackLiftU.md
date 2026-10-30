---
id: TraceDegree.traceDualPullbackLiftU
title: Transposing the trace matrix
summary: 'The Jacobian pullback is built by taking the matrix of the trace of forms and literally transposing it, which is how a covariant map on forms becomes a contravariant map on Jacobians.'
review: draft
authors:
- claude
caveats:
- 'The dual map is taken as a *matrix* transpose (`LinearMap.toMatrix''` then `Matrix.transpose` then `Matrix.toLin''`), not as Mathlib''s `LinearMap.dualMap`. That is the same thing only because the source and target are already the coordinate spaces `Fin g → ℂ` with their standard bases; the identification of `Fin g → ℂ` with its own dual is the standard bilinear pairing (no complex conjugation).'
- 'Everything basis-dependent in [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) is inherited here, including the non-canonical choice of basis of H⁰(X, Ω¹) and the `Classical.choose`-selected trace form.'
- 'No theorem at this point says this map is the dual of the trace in any intrinsic sense. It is a definition; the transpose is simply declared to be "the correct representative for Jacobian pullback" in the docstring (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 62–66). An equivalence identifying `Fin g → ℂ` with the linear dual of the form space does exist (`Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean` lines 69–72), but nothing in this chain invokes it.'
- 'The `U` suffix is vestigial: the module docstring points at `Jacobian/TraceDegree/PullbackBasis.lean` and a Type-0 original `traceDualPullbackLift`, and neither exists in the tree (only an unbuilt `Attic/FalseGaps/PullbackBasis.lean` mentioning the old names).'
quiz:
- q: 'What is the source of `traceDualPullbackLiftU f hf`?'
  type: choice
  choices:
  - '`Fin (analyticGenus ℂ X) → ℂ`'
  - '`Fin (analyticGenus ℂ Y) → ℂ`'
  - '`HolomorphicOneForm ℂ Y`'
  answer: 1
  explain: '`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 67–70 types it `(Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ)`, the reverse of `traceFormsCoordU`.'
- q: 'Why is a transpose the right thing here?'
  type: choice
  choices:
  - 'Because transposing makes the matrix invertible'
  - 'Because `Fin g → ℂ` is being used as the coordinate model of the dual of the form space, and a map of duals is the transpose of a map of spaces'
  - 'Because the period lattice is symmetric'
  answer: 1
  explain: 'The Jacobian carrier is ℂ^g standing for H⁰(X, Ω¹)*; see [BasisAnalyticJacobianU](#/node/AbelJacobi.BasisAnalyticJacobianU).'
- q: 'How is the dual map actually computed in the Lean?'
  type: choice
  choices:
  - 'With `LinearMap.dualMap`'
  - 'Via `LinearMap.toMatrix''`, `Matrix.transpose`, and `Matrix.toLin'''
  - 'By an inner product and an adjoint'
  answer: 1
  explain: 'The body is `Matrix.toLin'' (traceFormsCoordU f hf).toMatrix''.transpose`.'
- q: 'Does the Lean prove this map is independent of the chosen basis of holomorphic 1-forms?'
  type: choice
  choices:
  - 'Yes, there is a basis-invariance lemma'
  - 'No, no such claim is made'
  - 'The question does not apply because there is no basis'
  answer: 1
  explain: 'The basis comes from `Module.Free.chooseBasis` and no invariance theorem accompanies these definitions.'
---
## Plain English

[traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) is a matrix sending X-coordinates to Y-coordinates. `traceDualPullbackLiftU f hf` is its transpose, so it sends Y-coordinates to X-coordinates (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 67–70).

The one-line body does exactly that and nothing more:

```lean
Matrix.toLin' (traceFormsCoordU f hf).toMatrix'.transpose
```

`toMatrix'` turns a linear map between standard coordinate spaces into a matrix, `transpose` flips it, and `toLin'` turns it back into a linear map.

## Why it is defined this way

The Jacobian of X is a quotient of `Fin g → ℂ`, and that ℂ^g is the coordinate model of the **dual** space H⁰(X, Ω¹)\*. A linear functional on H⁰(X, Ω¹) is recorded by its values on the chosen basis ω₁, …, ω_g, which is a vector in ℂ^g.

Composing a functional on H⁰(Y, Ω¹) with the trace Tr : H⁰(X, Ω¹) → H⁰(Y, Ω¹) gives a functional on H⁰(X, Ω¹). In the chosen bases, that operation is the transpose matrix. So the transpose is the ambient (pre-quotient) version of the Jacobian pullback J(Y) → J(X).

What makes this the right map in the Lean is not the dual reading but the theorem that the transpose carries periods of Y to periods of X: a vector of integrals of the traced basis forms along a chain of Y differs from the traced integrals at the two endpoints by a period of X, so a closed chain contributes a period (`traceDualPullbackLift_genuinePeriods`, `Jacobian/TraceDegree/TracePeriods.lean` lines 299–315).

## How it is used

Two thin wrappers sit on top: [traceDualPullbackLiftLinearMapU](#/node/TraceDegree.traceDualPullbackLiftLinearMapU) (a name alias) and [traceDualPullbackLiftCLMU](#/node/TraceDegree.traceDualPullbackLiftCLMU) (the same map, bundled as continuous). The continuous version is what descends through the period lattice in [analyticPullbackU](#/node/TraceDegree.analyticPullbackU).
