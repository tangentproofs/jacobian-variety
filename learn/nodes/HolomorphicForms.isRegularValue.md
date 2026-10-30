---
id: HolomorphicForms.isRegularValue
title: Regular values, read off the chosen data
summary: '"Regular value" here is not a statement about derivatives: it asks the chosen branched-cover datum to report index 1 at every preimage.'
review: draft
authors:
- claude
caveats:
- 'The predicate is relative to a chosen `BranchedCoverData h`, not intrinsic to `f`. A different datum for the same `f` could declare different regular values; only `RamificationIndexCompatible` ties the index to the analytic order, and that predicate is not assumed here.'
- 'A point outside the image of `f` has an empty fibre, so it is vacuously regular. This matches the usual convention, but it means "regular value" does not imply "value".'
- 'The definition mentions no derivative. The link to the classical condition "the differential is invertible at every preimage" is a separate theorem, and it needs compatibility and holomorphy as hypotheses.'
quiz:
- q: 'What does `isRegularValue h y` say?'
  type: choice
  choices:
  - 'That `h.ramificationIndex x = 1` for every `x` with `f x = y`'
  - That the differential of `f` is invertible over `y`
  - 'That `y` has exactly `deg f` preimages'
  answer: 0
  explain: 'The definition is `∀ x ∈ f ⁻¹'' {y}, h.ramificationIndex x = 1` (Jacobian/TraceDegree/TraceDefinition.lean lines 62–63) — a condition on the datum''s own index function.'
- q: Is a point not in the image of `f` a regular value?
  type: choice
  choices:
  - 'No: the predicate requires at least one unramified preimage'
  - 'Yes, vacuously: there are no preimages to check'
  - 'Only if the branched-cover datum says so'
  answer: 1
  explain: 'The definition quantifies over `x ∈ f ⁻¹'' {y}` (Jacobian/TraceDegree/TraceDefinition.lean lines 62–63); an empty fibre satisfies it.'
- q: How large can the set of non-regular values be?
  type: choice
  choices:
  - 'Finite, because the source-side branch locus is finite and the branch values are its image'
  - Countable
  - Anything
  answer: 0
  explain: '`branchLocus_finite` (Jacobian/HolomorphicForms/TraceSpec.lean lines 237–251) rewrites the set of non-regular values as the image under `f` of the ramified set, then applies the `ramified_finite` field.'
- q: What is the predicate for?
  type: choice
  choices:
  - 'To state the degree'
  - 'To say where the trace (pushforward) of a 1-form can be defined by summing over the fibre'
  - To define the genus
  answer: 1
  explain: '`traceAtRegularValue` (Jacobian/TraceDegree/TraceDefinition.lean lines 90–95) takes `_hy : isRegularValue h y` and sums the pushed-forward cotangent vectors over the fibre.'
---
## Plain English

To push a differential 1-form forward along a map `f : X → Y`, the classical recipe at a point `y` of `Y` is: find the preimages of `y`, carry the form at each preimage down to `y` through the inverse of `f`, and add up the results. The recipe needs `f` to be locally invertible at each preimage, which fails exactly where sheets collide.

`isRegularValue h y` is the hypothesis that licenses the recipe. Given a branched-cover datum `h` for `f` ([BranchedCoverData](#/node/HolomorphicForms.BranchedCoverData)), it says

```
∀ x ∈ f ⁻¹' {y}, h.ramificationIndex x = 1
```

no preimage of `y` is ramified. Note what this is and is not. It is a question asked of the datum's index function. It is not a condition on a derivative, and nothing in the definition mentions one. If you hand over a datum whose indices are unrelated to `f`, the predicate still type-checks and reports nonsense; what rules that out downstream is `BranchedCoverData.RamificationIndexCompatible` (Jacobian/HolomorphicForms/BranchedCover.lean lines 91–95), which forces each index to equal [mapAnalyticOrderAt](#/node/HolomorphicForms.mapAnalyticOrderAt).

A point with no preimages at all is a regular value by default, since there is nothing to check. That is the usual convention and harmless here, because the maps in question are nonconstant holomorphic maps of compact connected surfaces.

## How it is used

Three facts, in order.

The regular values are almost all of `Y`. `branchLocus_finite` (Jacobian/HolomorphicForms/TraceSpec.lean lines 237–251) shows the non-regular values are the image of the finite ramified set, hence finite, and `regularLocus_dense` (Jacobian/HolomorphicForms/TraceSpec.lean lines 278–287) concludes the regular locus is dense in `Y`.

At a regular value the trace is defined. `traceAtRegularValue` (Jacobian/TraceDegree/TraceDefinition.lean lines 90–95) sums `cotangentPushforward` over the fibre, with the regularity proof as an argument.

Regularity gives an invertible differential. `mfderiv_isIso_of_ramificationIndex_one` (Jacobian/TraceDegree/TraceDefinition.lean lines 254–300) takes index 1 at `x`, plus compatibility and holomorphy, and produces an [IsIso](#/node/HolomorphicForms.IsIso) witness for the differential of `f` at `x` — explicitly, multiplication by the reciprocal of the local derivative.

So the trace of a form is first built on the dense set of regular values and then extended across the finitely many branch values. That is the shape of the trace used in the Jacobian's push-pull identity.
