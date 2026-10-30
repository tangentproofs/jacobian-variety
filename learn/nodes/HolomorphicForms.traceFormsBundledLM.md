---
id: HolomorphicForms.traceFormsBundledLM
title: The trace map on 1-forms is linear
summary: Linearity is not built into the trace construction; it has to be recovered by checking it at regular values and promoting it with the identity principle.
review: draft
authors:
- claude
caveats:
- 'Linearity is genuinely proved, but it is proved *after the fact*. The construction treats each input form separately, and in the analytic case each output form is a separately chosen witness, so nothing about the branch-value data is linear a priori. The identity principle is what rules out a mismatch.'
- 'The proof needs the canonical branched-cover datum, which only exists for nonconstant f; the constant case is handled separately and both sides are zero there (Jacobian/HolomorphicForms/TraceSpec.lean lines 2893–2897).'
- 'The underlying function is traceFormsBundled, so all the caveats about that definition carry over: in particular, for nonconstant f and nonzero η the trace form is a chosen witness of an existence theorem.'
quiz:
- q: How is linearity proved?
  type: choice
  choices:
  - By checking it at regular values, where the trace is a finite sum, and extending to all of Y by the identity principle
  - It is a field of TraceFormsConstructionData
  - By differentiating under the integral sign
  answer: 0
  explain: 'Both `map_add''` and `map_smul''` apply holomorphicOneForm_ext_on (regularLocus_dense hbc) and then traceAtRegularValue_add / _smul (Jacobian/HolomorphicForms/TraceSpec.lean lines 2887–2966).'
- q: Why can linearity not simply be checked pointwise everywhere?
  type: choice
  choices:
  - At a branch value the trace is defined by a holomorphic extension, with no fiber-sum formula to compute with
  - Because 1-forms cannot be added
  - Because the fibers are infinite
  answer: 0
  explain: 'The `regular_spec` field only describes the form at regular values (Jacobian/HolomorphicForms/TraceSpec.lean lines 80–83); branch values are reached only through density.'
- q: What happens in the constant-map case?
  type: choice
  choices:
  - Both sides are zero, by traceFormsBundled_eq_zero_of_constant
  - The canonical branched-cover datum is used anyway
  - Linearity fails and is excluded by hypothesis
  answer: 0
  explain: 'The first branch of each proof rewrites all three traces to 0 and closes with `add_zero` (Jacobian/HolomorphicForms/TraceSpec.lean lines 2893–2897).'
- q: Which classical fact about Riemann surfaces does the identity principle here rest on?
  type: choice
  choices:
  - The branch locus is finite, so the regular values are dense in a connected surface with no isolated points
  - Compact Riemann surfaces have finite genus
  - Holomorphic maps are open
  answer: 0
  explain: 'regularLocus_dense (Jacobian/HolomorphicForms/TraceSpec.lean lines 278–287) is built from branchLocus_finite (Jacobian/HolomorphicForms/TraceSpec.lean lines 237–251) plus the absence of isolated points.'
---
## Plain English

[traceFormsBundled](#/node/HolomorphicForms.traceFormsBundled) takes a holomorphic 1-form on X to one on Y. This declaration packages that assignment as a ℂ-linear map between the two spaces of holomorphic 1-forms, which is what the rest of the project needs in order to put it in coordinates and transpose it.

The interesting part is that linearity has to be proved here, inside the definition (`Jacobian/HolomorphicForms/TraceSpec.lean` lines 2887–2966). It is not a requirement of [TraceFormsConstructionData](#/node/HolomorphicForms.TraceFormsConstructionData): that record handles one input form at a time, and in the analytic case each output form is a separately chosen witness. Nothing in the construction relates the trace of η + ζ to the traces of η and ζ.

The proof is the standard argument.

If f is constant, all three traces are zero and there is nothing to check.

If f is nonconstant, the Lean builds the canonical branched-cover datum from f's smoothness and uses two facts about it. At any regular value, each of the three traces equals the corresponding finite fiber sum, by the record's `regular_spec`. And fiber sums are visibly additive and ℂ-homogeneous, because each summand is, in both branches of [cotangentPushforward](#/node/HolomorphicForms.cotangentPushforward) ([traceAtRegularValue_add](#/node/HolomorphicForms.traceAtRegularValue_add), [traceAtRegularValue_smul](#/node/HolomorphicForms.traceAtRegularValue_smul)). So the two sides agree at every regular value.

That is not yet everywhere: the branch values are left out. They are finitely many ([branchLocus_finite](#/node/HolomorphicForms.branchLocus_finite), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 237–251), so the regular values are dense ([regularLocus_dense](#/node/HolomorphicForms.regularLocus_dense), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 278–287), and two holomorphic 1-forms agreeing on a dense set are equal ([holomorphicOneForm_ext_on](#/node/HolomorphicForms.holomorphicOneForm_ext_on), `Jacobian/HolomorphicForms/TraceSpec.lean` lines 2789–2831). Linearity at the branch values comes for free from continuity, in that precise sense.

There is no shortcut available: a Riemann surface has no global frame for its 1-forms, so you cannot compare two forms by comparing coefficient functions. The identity principle is doing real work.

## How it is used

Put in a basis of holomorphic 1-forms, this linear map becomes a matrix ([traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU), `Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 55–60), whose transpose descends to the Jacobian pullback. It also satisfies the two functoriality laws, identity and composition ([traceFormsBundledLM_idU](#/node/TraceDegree.traceFormsBundledLM_idU) and [traceFormsBundledLM_compU](#/node/TraceDegree.traceFormsBundledLM_compU), `Jacobian/TraceDegree/AnalyticPullbackFunctorialU.lean` lines 81–94), and the degree identity with the pullback of forms (`Jacobian/TraceDegree/AnalyticDegree.lean` lines 235–246).
