---
id: TraceDegree.pushforwardTraceLiftLinearMapU
title: Transposing f* to get the pushforward
summary: 'The Jacobian pushforward is the transpose of the pullback of forms, so the covariant map on Jacobians is produced by flipping a matrix that goes the other way.'
review: draft
authors:
- claude
caveats:
- 'The dual map is taken as a matrix transpose (`LinearMap.toMatrix''`, `Matrix.transpose`, `Matrix.toLin''`), not as `LinearMap.dualMap`. This is legitimate because both sides are already the standard coordinate spaces `Fin g → ℂ`; the pairing used to identify `Fin g → ℂ` with its dual is the standard bilinear one, with no complex conjugation.'
- 'Everything basis-dependent in [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU) is inherited, including the non-canonical choice of basis of holomorphic 1-forms on each surface.'
- 'No theorem here asserts that this is the dual of f* in an intrinsic sense, nor that it is independent of the basis. It is a definition. An equivalence identifying `Fin g → ℂ` with the linear dual of the form space does exist (`Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean` lines 72–75), but nothing in this chain uses it; the Lean transposes the matrix directly.'
- 'The `U` suffix is vestigial: the module docstring names a Type-0 original `pushforwardTraceLiftLinearMap` in `PushforwardBasis.lean`, a file it describes as "retired; now `Attic/FalseGaps/PushforwardBasis.lean`, not built". Neither the declaration nor the file is part of the built library, so this is the only version.'
quiz:
- q: 'What is being transposed?'
  type: choice
  choices:
  - 'The matrix of the trace of forms'
  - 'The matrix of the chain-rule pullback f* of forms'
  - 'The period matrix of X'
  answer: 1
  explain: 'The body is `Matrix.toLin'' (holomorphicTraceCoordU f hf).toMatrix''.transpose`, and `holomorphicTraceCoordU` is f* in coordinates.'
- q: 'Which direction does the transposed map go?'
  type: choice
  choices:
  - '`(Fin g_X → ℂ) →ₗ[ℂ] (Fin g_Y → ℂ)`'
  - '`(Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`'
  - 'Both'
  answer: 0
  explain: '`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 65–70 give source `Fin (analyticGenus ℂ X) → ℂ`, the covariant direction needed for the pushforward.'
- q: 'Why does transposing turn a contravariant map into a covariant one?'
  type: choice
  choices:
  - 'Because transposes are inverses'
  - 'Because the carrier ℂ^g stands for the dual of the form space, and dualising reverses arrows'
  - 'Because the genus of X equals the genus of Y'
  answer: 1
  explain: 'See [BasisAnalyticJacobianU](#/node/AbelJacobi.BasisAnalyticJacobianU): the torus is a quotient of the coordinate model of H⁰(X, Ω¹)*.'
- q: 'Does this declaration prove anything about period lattices?'
  type: choice
  choices:
  - 'Yes, that it preserves them'
  - 'No; lattice preservation is proved later, about the continuous version'
  - 'Yes, that the lattice is discrete'
  answer: 1
  explain: '`pushforwardTraceLift_preserves_latticeU` is in `Jacobian/TraceDegree/AnalyticPushforwardU.lean` lines 103–121.'
---
## Plain English

A point of the Jacobian of X is, in this project, a vector in ℂ^{g_X} modulo periods, and ℂ^{g_X} is the coordinate model of H⁰(X, Ω¹)\* — a linear functional on forms, recorded by its values on the chosen basis.

Suppose you have such a functional λ on the forms of X, and you want a functional on the forms of Y. The only natural thing to do is: given a form η on Y, pull it back to X and apply λ. That is λ ∘ f\*, and in coordinates it is the transpose of the matrix of f\*.

`pushforwardTraceLiftLinearMapU f hf` is exactly that transpose (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 65–70):

```lean
Matrix.toLin' (holomorphicTraceCoordU f hf).toMatrix'.transpose
```

Source `Fin g_X → ℂ`, target `Fin g_Y → ℂ`. Covariant, like a pushforward should be.

## Why this is the right map

Pushing a chain forward along f and integrating against a form η of Y gives the same number as integrating f\*η along the original chain. That is the change-of-variables identity `∫_{f∘γ} η = ∫_γ f*η`. So "push the chain forward, then integrate" equals "integrate against the pullback", which is precisely the transpose of f\* acting on period vectors.

That identity is not just motivation. It is the content of `pushforwardTraceLiftCLMU_periodVector` (`Jacobian/TraceDegree/AnalyticPushforwardU.lean` lines 57–88), which is the step that proves the transpose carries periods of X to periods of Y. What is *not* proved anywhere is a compatibility between this map and the Abel–Jacobi map [ofCurve](#/node/Jacobian.ofCurve); the geometric reading above is motivation for the construction, not a theorem about it.

## How it is used

Bundled as continuous in [pushforwardTraceLiftCLMU](#/node/TraceDegree.pushforwardTraceLiftCLMU), then descended through the period lattice in [analyticPushforwardU](#/node/TraceDegree.analyticPushforwardU), then lifted across `ULift` to the public [pushforward](#/node/Jacobian.pushforward).
