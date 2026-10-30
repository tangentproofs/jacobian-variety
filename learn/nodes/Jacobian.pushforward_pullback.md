---
id: Jacobian.pushforward_pullback
title: Pull back then push forward multiplies by the degree
summary: 'Pulling a point of J(Y) back to J(X) and pushing it forward again returns the point added to itself deg f times, and the engine is the classical identity "trace of a pulled-back form = degree times the form".'
review: draft
authors:
- claude
caveats:
- '`•` here is `ℕ`-scalar multiplication on the additive group `Jacobian Y`, i.e. repeated addition (`nsmul`). There is no module structure on the Jacobian; `n • P` means `P + ⋯ + P` n times.'
- '[pushforward](#/node/Jacobian.pushforward) and [pullback](#/node/Jacobian.pullback) are the form-theoretic maps: in basis coordinates, pushforward is the transpose of pullback-of-forms, pullback is the transpose of trace-of-forms. No compatibility with divisors, and none with [ofCurve](#/node/Jacobian.ofCurve), is proved anywhere.'
- 'For constant `f` both sides are zero: [ContMDiff.degree](#/node/ContMDiff.degree) is 0 by definition and the trace of forms vanishes, so `pullback` is the zero map. The repository has no *exported* theorem stating that `pullback` is zero for constant `f`, even though the challenge docstring (Jacobian/Challenge.lean lines 128–129) promises it; the fact is visible inside the lattice-preservation proof at Jacobian/TraceDegree/AnalyticPullbackU.lean lines 73–85.'
- 'The identity holds in the stated direction only: `pushforward ∘ pullback = deg • id` on `Jacobian Y`. The opposite composite `pullback ∘ pushforward` on `Jacobian X` is not stated (classically it is not multiplication by the degree).'
- 'The whole weight of the theorem is cut at one named obligation, and that obligation is discharged. The file docstring at Jacobian/TraceDegree/AnalyticPushPullU.lean lines 17–42 explains why the deep branched-cover identity is genuinely required here (the `⊥`-shortcut cannot apply, since `mk`-equality on the period quotient needs exact representative equality), and records that it "has since been discharged by the route-β work" with "no sorries in this file"; the delegation to `TracePullbackProviderU.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU` is at Jacobian/TraceDegree/AnalyticPushPullU.lean lines 69–73.'
quiz:
- q: 'What does `•` mean in `(ContMDiff.degree f hf) • P`?'
  type: choice
  choices:
  - 'A complex scalar multiplication on a vector space'
  - 'Repeated addition in the abelian group `Jacobian Y`: `P + ⋯ + P`, `deg f` times'
  - 'Composition of group homomorphisms'
  answer: 1
  explain: '`Jacobian Y` is only an `AddCommGroup` (Jacobian/Solution.lean line 94) and `ContMDiff.degree f hf : ℕ`, so this is `nsmul`. The proof passes through `Nat.cast_smul_eq_nsmul` and `ComplexTorus.mk_nsmul` at Jacobian/TraceDegree/AnalyticPushPullU.lean lines 153–154.'
- q: 'What is the identity on 1-forms that drives this theorem?'
  type: choice
  choices:
  - 'Pulling back a form and then taking its trace along `f` gives `deg f` times the original form'
  - 'The wedge product of a form with its conjugate is positive'
  - 'Every holomorphic 1-form has a primitive'
  answer: 0
  explain: '`trace_pullback_providerU` (Jacobian/TraceDegree/TracePullbackProviderU.lean lines 78–115) proves `traceFormsBundled f hf (pullbackFormsBundled f hf η) = (analyticDegreeU f hf : ℂ) • η`.'
- q: 'How is that form identity proved for nonconstant `f`?'
  type: choice
  choices:
  - 'At a regular value the trace is the sum over the fibre of the inverse-derivative pullbacks, which telescopes to `#fibre` copies of the form; then the identity principle extends it from the dense regular locus to all of Y'
  - 'By a dimension count'
  - 'By assuming it as a structure field'
  answer: 0
  explain: '`trace_pullback_at_regular_value` (Jacobian/TraceDegree/TraceDefinition.lean lines 549–557) handles the regular values, and `holomorphicOneForm_ext_on (regularLocus_dense hbc)` extends it (Jacobian/TraceDegree/TracePullbackProviderU.lean lines 111–115).'
- q: 'What happens when `f` is constant?'
  type: choice
  choices:
  - 'The theorem fails'
  - 'Both sides are zero: degree 0 by definition, and the trace of forms along a constant map is 0, so pullback is the zero map'
  - 'The degree is 1, so the identity reads `P = P`'
  answer: 1
  explain: '`ContMDiff.degree_constant` (Jacobian/Solution.lean lines 224–229) gives degree 0, and the constant branch of `traceDualPullbackLift_preserves_latticeU` (Jacobian/TraceDegree/AnalyticPullbackU.lean lines 73–85) shows the vector-level map is 0.'
- q: 'Is the reverse composite `pullback (pushforward P) = deg • P` also proved?'
  type: choice
  choices:
  - 'Yes, by symmetry'
  - 'No. Only `pushforward ∘ pullback` appears, matching the specification'
  - 'Yes, but with the degree replaced by the genus'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 282–291 state only the one direction, as does Jacobian/Challenge.lean lines 152–153.'
---
## Plain English

Let `f : X → Y` be a holomorphic map between compact Riemann surfaces. It induces two maps on Jacobians, going opposite ways: [pullback](#/node/Jacobian.pullback) from J(Y) to J(X) and [pushforward](#/node/Jacobian.pushforward) from J(X) to J(Y). This theorem says that doing one and then the other, starting in J(Y), is multiplication by the degree of `f`:

  `pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P`

for every `P : Jacobian Y` (Jacobian/Solution.lean lines 282–291). The `•` is repeated addition in the group `Jacobian Y`, since the degree is a natural number and the Jacobian is an abelian group, not a vector space. If `f` is a 3-to-1 covering, the round trip sends P to P + P + P.

Classically this is `f_* ∘ f^* = deg f` on the Jacobian.

## Why it matters

This is the fourth anti-hack condition. Three homomorphisms and a number satisfying functoriality laws can be cooked up; making them satisfy this identity, with the degree fixed as the ramification-weighted count of preimages, forces them to interact the way the classical constructions do.

In this repository the three really are the classical constructions. [ContMDiff.degree](#/node/ContMDiff.degree) is the weighted fibre count of a [branched cover datum](#/node/HolomorphicForms.BranchedCoverData) whose ramification indices are pinned to the chart-local order of vanishing. `pullback` is the transpose of [trace of forms](#/node/HolomorphicForms.traceFormsBundled); `pushforward` is the transpose of [pullback of forms](#/node/HolomorphicForms.pullbackFormsBundled). So the theorem is the classical trace identity rather than a coincidence arranged to satisfy the specification. `ref/axiom-audit.md` reports that no public declaration depends on a `sorry` and that every public declaration prints only the axioms `propext`, `Classical.choice`, `Quot.sound`, with a strict comparator run on 2026-10-28; this page does not re-verify that.

## How the proof goes

Peel off the universe wrapper, then rewrite with [analyticPushforward_analyticPullbackU](#/node/TraceDegree.analyticPushforward_analyticPullbackU) (Jacobian/TraceDegree/AnalyticPushPullU.lean lines 134–154), then identify the public degree with the internal one using [degree_eq_analyticDegreeU](#/node/ContMDiff.degree_eq_analyticDegreeU) (Jacobian/Solution.lean lines 236–240), then `rfl`.

The internal theorem works down a tower. Pick a representative `v ∈ ℂ^g` of `P` (the quotient map is surjective). Both maps are descents of continuous linear maps on ℂ^g, so the question becomes one about those linear maps at `v`, and then about their matrices:

- vector level: [pushforwardTraceLiftU ∘ traceDualPullbackLiftU = (deg : ℂ) • id](#/node/TraceDegree.pushforwardTraceLiftU_traceDualPullbackLiftU_eq_degree_smul) (Jacobian/TraceDegree/AnalyticPushPullU.lean lines 104–128), proved by transposing matrices;
- matrix level: [the same](#/node/TraceDegree.traceFormsCoordU_holomorphicTraceCoordU_eq_degree_smul) for [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) composed with [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU) (Jacobian/TraceDegree/AnalyticPushPullU.lean lines 82–98);
- linear-map level on forms: [traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU](#/node/TraceDegree.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU) (Jacobian/TraceDegree/AnalyticPushPullU.lean lines 69–73).

That last one is where the mathematics lives, and it is **proved in this repository**, by [traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU](#/node/TraceDegree.TracePullbackProviderU.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU) (Jacobian/TraceDegree/TracePullbackProviderU.lean lines 123–132) on top of [trace_pullback_providerU](#/node/TraceDegree.TracePullbackProviderU.trace_pullback_providerU) (Jacobian/TraceDegree/TracePullbackProviderU.lean lines 78–115). That proof splits on whether `f` is constant. If it is, both sides are zero: the pullback of any form along a constant map is 0 because the derivative is 0. If it is not, a compatible branched-cover datum is built from `f` itself by [branchedCoverData_of_nonconstant_holomorphic](#/node/Blueprint.branchedCoverData_of_nonconstant_holomorphic), and at a regular value `y` the trace of a pulled-back form is computed fibre point by fibre point: each preimage contributes exactly `η(y)`, so the sum is `#f⁻¹(y) · η(y)`, which is the weighted fibre count because unramified points have multiplicity 1 ([trace_pullback_at_regular_value](#/node/HolomorphicForms.trace_pullback_at_regular_value), Jacobian/TraceDegree/TraceDefinition.lean lines 549–557). [Regular values are dense](#/node/HolomorphicForms.regularLocus_dense), and [two holomorphic forms agreeing on a dense set agree](#/node/HolomorphicForms.holomorphicOneForm_ext_on), so the identity holds everywhere on Y.

The final step turns the complex scalar multiple of the representative into repeated addition in the quotient: `Nat.cast_smul_eq_nsmul` rewrites `(deg : ℂ) • v` to `deg • v`, and [mk_nsmul](#/node/ComplexTorus.mk_nsmul) (Jacobian/ComplexTorus/Smul.lean lines 25–27) pushes it through the quotient map.

## What it does not say

- Nothing about divisors. The two maps are the dual, form-theoretic ones; no lemma relates them to divisors or to the Abel–Jacobi map.
- Not the other composite. `pullback ∘ pushforward` on `Jacobian X` is not addressed.
- No statement that a nonconstant map has degree at least 1. Positivity is proved only for a *surjective* branched cover ([branchedDegree_pos](#/node/HolomorphicForms.branchedDegree_pos), Jacobian/HolomorphicForms/BranchedCover.lean lines 197–208), and no theorem here says a nonconstant holomorphic map of compact surfaces is surjective, so nothing on the public path gives `0 < ContMDiff.degree f hf`. In the constant case the identity reads `0 = 0`.
- No Riemann–Hurwitz, and no relation between `genus X` and `genus Y` for a map of degree `n`.
