---
id: Jacobian.pullback_id_apply
title: Pulling back along the identity changes nothing
summary: 'Unlike its pushforward twin, this innocent-looking law rests on a real branched-cover computation: the trace of a 1-form along the identity map has to be shown equal to the form.'
review: draft
authors:
- claude
caveats:
- 'Stated pointwise, `∀ P : Jacobian X, pullback id contMDiff_id P = P`, not as an equality of homomorphisms.'
- '`traceFormsBundledLM_idU` and `traceFormsBundledLM_compU` are the two deep trace obligations the pullback side is cut at, and both are discharged. The file docstring at Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 34–44 says they "have since been discharged by the ''E2-trace-id'' route-β work" and that "there are no sorries in this file"; the section heading at lines 68–78 is "The two deep branched-cover trace-identity obligations (both discharged)". The delegations are at Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 85–87 (to `TraceFormsIdU`) and lines 93–99 (to `TraceFormsBundledCompU`).'
quiz:
- q: 'Why is this harder than the corresponding pushforward law?'
  type: choice
  choices:
  - 'Because `pullback` is built from the **trace** of forms, whose behaviour along the identity needs the branched-cover apparatus, while `pushforward` is built from pullback of forms, which is functorial by the chain rule'
  - 'Because the identity map has degree 0'
  - 'Because the Jacobian of X is bigger than the Jacobian of Y'
  answer: 0
  explain: 'Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 21–32 explain exactly this asymmetry; the id case goes through `idBranchedCoverData` and the identity principle on the regular locus.'
- q: 'What is the bottom lemma the proof calls?'
  type: choice
  choices:
  - '`traceFormsBundledLM_idU`, that the trace-of-forms linear map along `id` is the identity'
  - '`mk_nsmul`'
  - '`genus_eq_zero_iff_homeo`'
  answer: 0
  explain: 'Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 85–87 state it and delegate to `TraceFormsIdU.traceFormsBundledLM_id_genuineU`.'
- q: 'How does the proof get from classes to vectors?'
  type: choice
  choices:
  - 'By `QuotientAddGroup.induction_on`, which supplies a representative `v` for the class'
  - 'By choosing a basis'
  - 'By compactness'
  answer: 0
  explain: 'Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 154–164 do the induction and then use the descent identity `analyticPullback_mk_spec_rawU`.'
---
## Plain English

[pullback](#/node/Jacobian.pullback) turns a holomorphic map `f : X → Y` into a homomorphism J(Y) → J(X). This lemma says that for the identity map of X the result is the identity: for every `P : Jacobian X`,

  `pullback id contMDiff_id P = P`

(Jacobian/Solution.lean lines 192–196).

It looks like the mirror image of [the pushforward law](#/node/Jacobian.pushforward_id_apply), and as a statement it is. As a proof it is not. `pushforward` is built from pullback of 1-forms, where "along the identity, nothing happens" is immediate. `pullback` is built from the *trace* of 1-forms: the trace of ω at a point `y` is the sum of ω over the preimages of `y`, each pulled through the inverse of the local derivative. Showing that this operation along the identity returns ω means showing the identity map is an unramified cover with one-point fibres whose local derivative is the identity at every point.

## Why it matters

The specification lists it as functoriality (Jacobian/Challenge.lean line 140). With [the composition law](#/node/Jacobian.pullback_comp_apply) it makes pullback a contravariant functor to complex Lie groups, and it is a real constraint: a `pullback` that was secretly the zero map would fail here on any Jacobian that is not a point.

## How the proof goes

Jacobian/Solution.lean lines 192–196 unfold the `ULift` wrapper, rewrite with [analyticPullback_id_applyU](#/node/TraceDegree.analyticPullback_id_applyU) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 152–164), and close with `rfl`.

The analytic lemma takes a representative by `QuotientAddGroup.induction_on`, pushes through the descent identity [analyticPullback_mk_spec_rawU](#/node/TraceDegree.analyticPullback_mk_spec_rawU), and reduces to [traceDualPullbackLiftU_id](#/node/TraceDegree.traceDualPullbackLiftU_id) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 131–134). That unwinds a matrix transpose to [traceFormsCoordU_id](#/node/TraceDegree.traceFormsCoordU_id) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 109–116), which is the coordinate form of [traceFormsBundledLM_idU](#/node/TraceDegree.traceFormsBundledLM_idU) (Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean lines 85–87).

That last one is the content, and it is **proved in this repository**, by [traceFormsBundledLM_id_genuineU](#/node/TraceDegree.TraceFormsIdU.traceFormsBundledLM_id_genuineU) (Jacobian/TraceDegree/TraceFormsIdU.lean lines 217–222). The chain under it: the chart-local order of `id` is 1 at every point (Jacobian/TraceDegree/TraceFormsIdU.lean lines 46–79), so the [identity branched-cover datum](#/node/TraceDegree.TraceFormsIdU.idBranchedCoverDataU) with ramification index 1 and singleton fibres is compatible, and every point is a regular value for it (Jacobian/TraceDegree/TraceFormsIdU.lean lines 152–154); at such a point the trace is the single term `cotangentPushforward id`, which is the identity ([traceAtRegularValue_idU](#/node/TraceDegree.TraceFormsIdU.traceAtRegularValue_idU), Jacobian/TraceDegree/TraceFormsIdU.lean lines 166–170); the regular locus is all of X, so the identity principle for holomorphic 1-forms gives `traceFormsBundled id η = η` ([traceFormsBundled_idU](#/node/TraceDegree.TraceFormsIdU.traceFormsBundled_idU), Jacobian/TraceDegree/TraceFormsIdU.lean lines 194–210).

## What it does not say

- Not an equality of bundled homomorphisms, only pointwise.
- Nothing for a general biholomorphism `f`, only for the literal identity function.
- Nothing about divisors, and no compatibility with [ofCurve](#/node/Jacobian.ofCurve).
