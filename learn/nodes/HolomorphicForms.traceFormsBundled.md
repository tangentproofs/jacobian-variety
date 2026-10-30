---
id: HolomorphicForms.traceFormsBundled
title: The trace of a holomorphic 1-form
summary: The trace form is read off a provider record, so it is pinned down only by its values at regular values of f, plus a separate theorem matching it to an explicit construction.
review: draft
authors:
- claude
caveats:
- 'For a nonconstant f and a nonzero η, the value is a `Classical.choose`n witness of an existence theorem. Uniqueness follows from density of the regular values and the identity principle, but is not part of this definition; traceFormsBundled_eq_traceHolomorphicForm (Jacobian/HolomorphicForms/TraceSpec.lean lines 2972–2996) is what ties it to an explicit construction.'
- For a constant f the value is 0 by convention; the specification imposes nothing in that case.
- 'Direction of use: in this project the trace on forms builds the Jacobian *pullback*. The Jacobian *pushforward* is built from the transpose of the pullback of forms instead. Both match the classical picture, but the names can mislead.'
quiz:
- q: What is traceFormsBundled, as a definition?
  type: choice
  choices:
  - The traceForm field of the construction-data provider
  - The fiber sum, evaluated at every point of Y
  - The integral of η over the fibers of f
  answer: 0
  explain: 'The body is `(traceFormsConstructionData_provider f hf η).traceForm` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2778–2781).'
- q: What is its value at a regular value y of a compatible branched-cover datum?
  type: choice
  choices:
  - The sum of the pushed-forward covectors over the finitely many preimages of y
  - Zero
  - The covector of η at one chosen preimage
  answer: 0
  explain: 'That is exactly the `regular_spec` field of the record it is extracted from (Jacobian/HolomorphicForms/TraceSpec.lean lines 80–83).'
- q: Which map between Jacobians does this trace produce?
  type: choice
  choices:
  - The pullback J(Y) → J(X), by transposing the trace in basis coordinates
  - The pushforward J(X) → J(Y), directly
  - Neither; it is only used for the degree
  answer: 0
  explain: 'traceFormsCoordU puts the trace in coordinates (Jacobian/TraceDegree/PullbackTraceLiftU.lean lines 56–61) and traceDualPullbackLiftU transposes it (Jacobian/TraceDegree/PullbackTraceLiftU.lean lines 68–71), which feeds analyticPullbackU.'
- q: What is the trace along a constant map?
  type: choice
  choices:
  - Zero, matching the convention that a constant map has degree 0
  - The zero form only when η is zero
  - Undefined
  answer: 0
  explain: 'traceFormsBundled_eq_zero_of_constant (Jacobian/HolomorphicForms/TraceSpec.lean lines 2859–2873), consistent with ContMDiff.degree (Jacobian/Solution.lean lines 210–222).'
---
## Plain English

This is the object that deserves the name "the trace of η along f", written Tr_f η classically. The definition itself is one line: take the provider's record and read off its form field (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2778–2781).

What that gives you, unwrapped:

- At a regular value of f, the value is the finite fiber sum: push the covector of η at each preimage forward through the inverse of the derivative, and add up ([traceAtRegularValue](#/node/HolomorphicForms.traceAtRegularValue)).
- At the finitely many branch values, the value is whatever the holomorphic extension gives. There is no fiber-sum formula there, and there cannot be: the derivative is not invertible at a ramification point.
- If f is constant, the value is 0 ([traceFormsBundled_eq_zero_of_constant](#/node/HolomorphicForms.traceFormsBundled_eq_zero_of_constant)).
- If η is zero, the value is 0.

For nonconstant f the form is unique, because regular values are dense in Y ([regularLocus_dense](#/node/HolomorphicForms.regularLocus_dense), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 278–287) and two holomorphic 1-forms that agree on a dense set are equal ([holomorphicOneForm_ext_on](#/node/HolomorphicForms.holomorphicOneForm_ext_on), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2790–2832). The definition does not rely on that, since it only reads a field; but a separate theorem does identify the chosen form with the explicitly built one ([traceFormsBundled_eq_traceHolomorphicForm](#/node/HolomorphicForms.traceFormsBundled_eq_traceHolomorphicForm), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2972–2996).

## What it is for

Two jobs in the Jacobian story.

First, the Jacobian pullback. The Jacobian of X is ℂ^g modulo the period lattice, and ℂ^g is the dual of the space of holomorphic 1-forms in a chosen basis. Dualising a linear map on forms therefore reverses its direction. The trace goes from forms on X to forms on Y, so its transpose goes from coordinates on Y to coordinates on X, which is the pullback [Jacobian.pullback](#/node/Jacobian.pullback) (`Jacobian/Solution.lean` lines 174–178). The chain is [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 56–61), then [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU) (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 68–71), then [analyticPullbackU](#/node/TraceDegree.analyticPullbackU) (`Jacobian/TraceDegree/AnalyticPullbackU.lean` lines 100–109). Symmetrically, the Jacobian pushforward [Jacobian.pushforward](#/node/Jacobian.pushforward) comes from transposing the *pullback of forms*, not from the trace: [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU) puts `pullbackFormsBundledLM` in coordinates (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 51–58) and `pushforwardTraceLiftLinearMapU` transposes it (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 65–70). Its name is a leftover; it has nothing to do with the trace.

Second, the degree identity. Tracing a pulled-back form multiplies it by the degree of f: [traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul](#/node/TraceDegree.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul) (`Jacobian/TraceDegree/AnalyticDegree.lean` lines 235–246). Dualising that is what makes pushforward after pullback equal multiplication by deg f on the Jacobian, which is the challenge's anti-hack requirement.

The linear-map packaging is [traceFormsBundledLM](#/node/HolomorphicForms.traceFormsBundledLM).
