---
id: TraceDegree.holomorphicTraceCoordU
title: The misnamed trace coordinate map
summary: 'Despite "trace" in the name, this map has nothing to do with the trace: it is the chain-rule pullback f* of holomorphic 1-forms written in the chosen bases, and its own docstring admits as much.'
review: draft
authors:
- claude
caveats:
- 'The name is misleading. The body is built from [pullbackFormsBundledLM](#/node/HolomorphicForms.pullbackFormsBundledLM), the chain-rule pullback, not from the trace [traceFormsBundledLM](#/node/HolomorphicForms.traceFormsBundledLM). The docstring (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 46–49) says so: "the basis-coordinate form of the chain-rule pullback `f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`". The genuinely trace-based coordinate map is [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU).'
- 'The matrix depends on the choice of basis on both surfaces. `holomorphicOneFormFinBasis` comes from `Module.Free.chooseBasis` and its docstring (`Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean` lines 48–52) says the choice is non-canonical. No basis-independence lemma accompanies this definition.'
- 'The `FiniteDimensionalHolomorphicOneForms` instances for X and Y are bound in the signature here, not in the file''s `variable` block. They are what make `analyticGenus` and the finite basis available, and they are not an assumption: finite-dimensionality is proved by a Montel–Riesz argument (`finiteDimensional_holomorphicOneForm`, `Jacobian/HolomorphicForms/Finiteness.lean` lines 323–324, registered as an instance at `Jacobian/HolomorphicForms/Finiteness.lean` lines 372–373), and `Jacobian/Solution.lean` lines 34–37 installs it globally for every compact Riemann surface. The theorem it goes through is named `…_frontier`, which is historical only: the docstring at `Jacobian/Solution.lean` lines 39–44 says the suffix "is only historical — it is proved".'
- 'The `U` suffix is vestigial: the module docstring names a Type-0 original `holomorphicTraceCoord` in `PushforwardBasis.lean`, a file it describes as "retired; now `Attic/FalseGaps/PushforwardBasis.lean`, not built". Neither the declaration nor the file is part of the built library, so this is the only version.'
quiz:
- q: 'Which operation on forms does this map actually encode?'
  type: choice
  choices:
  - 'The trace, summing a form over the fibre of f'
  - 'The chain-rule pullback f*'
  - 'Integration over a closed chain'
  answer: 1
  explain: 'The body (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 51–58) sandwiches `pullbackFormsBundledLM X Y f hf` between the two basis isomorphisms.'
- q: 'Which direction does it go?'
  type: choice
  choices:
  - '`(Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`'
  - '`(Fin g_X → ℂ) →ₗ[ℂ] (Fin g_Y → ℂ)`'
  - 'It is an isomorphism'
  answer: 0
  explain: 'Pullback of forms is contravariant, so the coordinate version runs Y-coordinates to X-coordinates.'
- q: 'What role do the two basis isomorphisms play?'
  type: choice
  choices:
  - 'They orthonormalise the forms'
  - 'They translate between a form and its coordinate vector, so the abstract map becomes a matrix'
  - 'They prove the map is continuous'
  answer: 1
  explain: '`Module.Basis.equivFun` and its inverse are exactly the coordinate isomorphisms `H⁰(…, Ω¹) ≅ (Fin g → ℂ)`.'
- q: 'Why is a coordinate version needed at all?'
  type: choice
  choices:
  - 'Because `LinearMap.toMatrix''` and `Matrix.transpose` only apply to maps between standard coordinate spaces'
  - 'Because forms cannot be added'
  - 'Because the Jacobian is defined on forms, not on their coordinates'
  answer: 0
  explain: 'The next step, [pushforwardTraceLiftLinearMapU](#/node/TraceDegree.pushforwardTraceLiftLinearMapU), is `Matrix.toLin'' (…).toMatrix''.transpose`.'
---
## Plain English

Fix once and for all a basis of the holomorphic 1-forms on each surface, so that a form is the same as its vector of coordinates in `Fin g → ℂ`. `holomorphicTraceCoordU f hf` is the chain-rule pullback f\* written in those coordinates (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 51–58):

```
(Fin g_Y → ℂ) --equivFun.symm--> H⁰(Y, Ω¹) --f*--> H⁰(X, Ω¹) --equivFun--> (Fin g_X → ℂ)
```

Concretely, the (i, j) entry is the i-th coordinate of f\*ω_j^Y in the basis of X. In classical notation, if ω_1^Y, …, ω_{g_Y}^Y is the basis on Y and ω_1^X, …, ω_{g_X}^X the basis on X, then

```
f* ω_j^Y = Σ_i A_{i j} ω_i^X
```

and A is this matrix.

## Why the name says "trace"

It is a layer label, not a description. The declaration lives in `Jacobian/TraceDegree/PushforwardTraceLiftU.lean`, part of the `TraceDegree` layer that builds the two Jacobian maps and the identity `pushforward ∘ pullback = deg f`. On the pushforward side the ambient map is the transpose of f\*; on the pullback side it is the transpose of the actual trace. Both names carry the word "trace", so `holomorphicTraceCoordU` and [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) look like variants of one thing and are not. The docstrings are explicit about which is which.

## How it is used

Transposed immediately. [pushforwardTraceLiftLinearMapU](#/node/TraceDegree.pushforwardTraceLiftLinearMapU) takes `(holomorphicTraceCoordU f hf).toMatrix'.transpose`, which is the dual map on ℂ^g understood as the coordinate model of H⁰(X, Ω¹)\*. That transpose becomes continuous in [pushforwardTraceLiftCLMU](#/node/TraceDegree.pushforwardTraceLiftCLMU) and descends to the tori in [analyticPushforwardU](#/node/TraceDegree.analyticPushforwardU).
