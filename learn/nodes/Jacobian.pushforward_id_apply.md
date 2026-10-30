---
id: Jacobian.pushforward_id_apply
title: Pushing forward along the identity changes nothing
summary: 'The statement is pointwise, not an equality of homomorphisms, and it reduces to the fact that pulling a 1-form back along the identity map returns the same form.'
review: draft
authors:
- claude
caveats:
- 'The lemma is stated pointwise, `∀ P, pushforward id contMDiff_id P = P`, not as `pushforward id contMDiff_id = AddMonoidHom.id`. The two are equivalent for bundled maps but the Lean only gives the pointwise form, matching the spec.'
- 'The identity proof `contMDiff_id` is supplied explicitly as the smoothness argument. `ContMDiff` is a `Prop`, so by proof irrelevance the value of `pushforward f hf` cannot depend on which smoothness proof is handed to it.'
quiz:
- q: 'What shape does the lemma have?'
  type: choice
  choices:
  - 'An equality of group homomorphisms'
  - 'A pointwise equality: for every `P : Jacobian X`, `pushforward id contMDiff_id P = P`'
  - 'An equality of the two underlying linear maps on ℂ^g'
  answer: 1
  explain: 'Jacobian/Solution.lean line 152 quantifies over `P : Jacobian X`, matching Jacobian/Challenge.lean line 116.'
- q: 'What is the bottom fact the proof reduces to?'
  type: choice
  choices:
  - 'Pulling back a holomorphic 1-form along the identity map gives the same form, so the coordinate matrix is the identity matrix'
  - 'The period lattice is discrete'
  - 'The degree of the identity map is 1'
  answer: 0
  explain: '`holomorphicTraceCoord_idU` (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 49–56) rewrites with `pullbackFormsBundledLM_id`, and then `pushforwardTraceLiftLinearMapU_id` (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 75–79) turns the transpose of the identity matrix into the identity.'
- q: 'Why does the proof need `mk_surjective`?'
  type: choice
  choices:
  - 'To pick a representative vector in ℂ^g for the class `P`, so the statement can be checked on representatives'
  - 'To prove the Jacobian is compact'
  - 'To choose a basis of 1-forms'
  answer: 0
  explain: 'Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean line 100 obtains `⟨v, rfl⟩` from `ComplexTorus.mk_surjective` and then argues on `v`.'
---
## Plain English

[pushforward](#/node/Jacobian.pushforward) turns a holomorphic map `f : X → Y` into a homomorphism J(X) → J(Y). This lemma says that if `f` is the identity map of X, the induced homomorphism is the identity: for every point `P` of the Jacobian,

  `pushforward id contMDiff_id P = P`

(Jacobian/Solution.lean lines 152–156). The second argument `contMDiff_id` is the proof that the identity map is holomorphic, which the definition of `pushforward` requires as an argument.

## Why it matters

This is half of functoriality. The specification lists it (Jacobian/Challenge.lean line 116) alongside the composition law. Functoriality is what makes the Jacobian a *construction* on surfaces rather than a per-surface accident: a map of curves gives a map of Jacobians, identities to identities, composites to composites. It also rules out some lazy definitions. A `pushforward` that always returned 0, for example, would satisfy the type and continuity requirements but fail here on any Jacobian that is not a point.

## How the proof goes

The public proof (Jacobian/Solution.lean lines 152–156) unfolds the `ULift` wrapper, rewrites with [analyticPushforward_id_applyU](#/node/TraceDegree.analyticPushforward_id_applyU) (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 98–105), and closes with `rfl`.

The analytic lemma takes a representative: every class is `mk v` for some `v ∈ ℂ^g`. On representatives the pushforward is the linear map [pushforwardTraceLiftLinearMapU](#/node/TraceDegree.pushforwardTraceLiftLinearMapU), so the goal becomes that this linear map along `id` is the identity. That is `pushforwardTraceLiftLinearMapU_id` (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 75–79): the map is the transpose of the matrix of [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU), and [holomorphicTraceCoord_idU](#/node/TraceDegree.holomorphicTraceCoord_idU) (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 49–56) shows that coordinate map is the identity, because [pullback of forms along the identity is the identity](#/node/HolomorphicForms.pullbackFormsBundledLM_id). The transpose of the identity matrix is the identity matrix.

This side is cheap. The pushforward is built from pullback-of-forms, whose functoriality is the chain rule and already holds in Mathlib-style generality. The [pullback side](#/node/Jacobian.pullback_id_apply) rests on the trace of forms instead, and there the corresponding fact is a genuine branched-cover argument.

## What it does not say

- Not an equality of bundled homomorphisms, only a pointwise equality.
- Nothing about `pushforward` for an arbitrary isomorphism `f`, only for the literal identity function.
- No divisor-level or `ofCurve`-level interpretation.
