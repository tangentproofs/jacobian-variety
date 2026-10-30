---
id: TraceDegree.traceFormsCoordU
title: The trace of 1-forms as a g×g matrix
summary: 'The trace map on holomorphic 1-forms written as a matrix in an arbitrary chosen basis, built on a trace form that is a `Classical.choose` witness specified only by its values at regular points of f.'
review: draft
authors:
- claude
caveats:
- 'The basis is `holomorphicOneFormFinBasis`, which is `Module.finBasis` on top of `Module.Free.chooseBasis` (`Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean` lines 53–55). Its own docstring says the choice is non-canonical. The matrix entries of this map therefore depend on that choice; nothing in the Lean asserts basis-independence.'
- 'The underlying trace `traceFormsBundled` is not a formula. In the case `f` nonconstant and `η ≠ 0` it is `Exists.choose` of `traceForm_global_extension` (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2744–2752), i.e. a chosen 1-form on `Y` whose only stated property is that it agrees with the finite fibre sum at regular values. That property does pin it down, because the regular locus is dense and holomorphic 1-forms agreeing on a dense set are equal; both facts are proved (`regularLocus_dense`, `Jacobian/HolomorphicForms/TraceSpec.lean` lines 278–280, and `holomorphicOneForm_ext_on`, `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2790–2793) and together they are what makes the trace linear (`traceFormsBundledLM`, `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2888–2927).'
- 'The trace is defined by a three-way case split on the input: `η = 0`, `f` constant, and otherwise (`traceFormsConstructionData_provider`, `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2764–2775). For constant `f` the trace is the zero form (`traceFormsBundled_eq_zero_of_constant`, `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2859–2873), so this coordinate map is the zero matrix there.'
- 'The `U` suffix and the docstring phrase "universe-polymorphic companion to `traceFormsCoord`" are vestigial. The module docstring names `PullbackBasis.lean` as the home of the Type-0 `traceFormsCoord` and says of it "retired; now `Attic/FalseGaps/PullbackBasis.lean`, not built"; no declaration called `traceFormsCoord` is in the built library. This is the only version.'
quiz:
- q: 'Which direction does `traceFormsCoordU f hf` go?'
  type: choice
  choices:
  - 'From X-coordinates to Y-coordinates, because the trace pushes forms from X to Y'
  - 'From Y-coordinates to X-coordinates, because it pulls forms back'
  - 'Both, it is an isomorphism'
  answer: 0
  explain: 'The stated type in `Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 56–61 is `(Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ)`, matching `traceFormsBundledLM : H⁰(X, Ω¹) →ₗ H⁰(Y, Ω¹)`.'
- q: 'What pins down the trace form that this map is built from?'
  type: choice
  choices:
  - 'An explicit integral formula valid at every point of Y'
  - 'Its agreement with the finite sum over the fibre at regular values of any compatible branched-cover datum'
  - 'A universal property of the Jacobian'
  answer: 1
  explain: '`TraceFormsConstructionData.regular_spec` (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 80–83) is the only positive specification; the form itself is a chosen witness.'
- q: 'If you replaced the chosen basis of H⁰(X, Ω¹) by a different one, what would happen to this definition?'
  type: choice
  choices:
  - 'Nothing, the Lean proves the matrix is basis-independent'
  - 'The matrix would change, and the Lean makes no basis-independence claim'
  - 'The definition would fail to type-check'
  answer: 1
  explain: 'The map is `equivFun ∘ traceFormsBundledLM ∘ equivFun.symm`, so it is conjugation by the basis isomorphisms; no invariance lemma accompanies it.'
- q: 'For a constant map f, what is `traceFormsCoordU f hf`?'
  type: choice
  choices:
  - 'The identity matrix'
  - 'The zero matrix'
  - 'Undefined'
  answer: 1
  explain: '`traceFormsBundled_eq_zero_of_constant` forces the trace form to be 0, and this is exactly the computation used in `Jacobian/TraceDegree/AnalyticPullbackU.lean` lines 73–83.'
---
## Plain English

Fix a compact Riemann surface X. Its holomorphic 1-forms form a finite-dimensional complex vector space H⁰(X, Ω¹), of dimension g = [analyticGenus](#/node/HolomorphicForms.analyticGenus) ℂ X. Pick a basis ω₁, …, ω_g once and for all: that is [holomorphicOneFormFinBasis](#/node/HolomorphicForms.holomorphicOneFormFinBasis). Through it, a form is the same thing as its coordinate vector in `Fin g → ℂ`.

Now let f : X → Y be an analytic map of compact Riemann surfaces. There is a *trace* operation that turns a 1-form on X into a 1-form on Y. At a point y with no ramification above it, you take the finitely many preimages of y, push the form at each one through the inverse of the derivative of f, and add the results. The project calls this [traceFormsBundledLM](#/node/HolomorphicForms.traceFormsBundledLM), a ℂ-linear map H⁰(X, Ω¹) → H⁰(Y, Ω¹).

`traceFormsCoordU f hf` is that same map written in coordinates (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 56–61). Read right to left: take a coordinate vector for X, turn it into a form on X, take its trace, read off the coordinates of the resulting form on Y.

```
(Fin g_X → ℂ) --equivFun.symm--> H⁰(X, Ω¹) --Tr--> H⁰(Y, Ω¹) --equivFun--> (Fin g_Y → ℂ)
```

So it is a `g_Y × g_X` matrix, up to the usual identification.

## Why it is defined this way

The Jacobian of X in this project is the quotient of `Fin g → ℂ` by the period lattice, and `Fin g → ℂ` is read as the coordinate model of the *dual* space H⁰(X, Ω¹)\*. A map between duals is the transpose of a map between the spaces themselves. So to build the Jacobian **pullback** J(Y) → J(X) you need the transpose of a map H⁰(X, Ω¹) → H⁰(Y, Ω¹), and the trace is exactly that map. That transpose is [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU), the next step.

This is why the arrow here looks "backwards" relative to the word *pullback*: the trace goes X → Y on forms, and transposing it gives Y → X on Jacobians.

The dual reading is motivation, not a Lean step. An equivalence `(H⁰(X, Ω¹) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` does exist in the project (`Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean` lines 72–75), but no theorem in this chain uses it. The Lean works with the coordinate space directly and transposes the matrix.

## How it is used

Only as the input to the transpose. [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU) takes `(traceFormsCoordU f hf).toMatrix'.transpose`, and that transpose descends through the period lattice to [analyticPullbackU](#/node/TraceDegree.analyticPullbackU) and then to the public [pullback](#/node/Jacobian.pullback).
