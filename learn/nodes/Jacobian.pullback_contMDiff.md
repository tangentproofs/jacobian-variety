---
id: Jacobian.pullback_contMDiff
title: Pullback is holomorphic
summary: 'The hard part of pullback is that it exists at all; once the trace-of-forms map is known to respect the period lattice, holomorphy is the same linear-algebra argument as for pushforward.'
review: draft
authors:
- claude
caveats:
- '"Holomorphic" is `ContMDiff` at level `ω` between the coordinate models `Fin (genus Y) → ℂ` and `Fin (genus X) → ℂ`, which depend on chosen bases of holomorphic 1-forms.'
- '[pullback](#/node/Jacobian.pullback) is the transpose of the **trace** of forms along `f`, not a divisor pullback. No divisor-level compatibility is proved.'
- 'For constant `f` the trace of forms is 0, so `pullback` is the zero map and this theorem is the (true but empty) statement that the zero map is analytic. The repository proves the vanishing inside Jacobian/TraceDegree/AnalyticPullbackU.lean lines 72–84 but exports no theorem stating it, even though the challenge docstring (Jacobian/Challenge.lean lines 128–129) promises it.'
quiz:
- q: 'Which direction does pullback go?'
  type: choice
  choices:
  - 'From `Jacobian X` to `Jacobian Y`'
  - 'From `Jacobian Y` to `Jacobian X`, contravariantly in `f : X → Y`'
  - 'From `Jacobian X` to itself'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 172–176 define `pullback f hf : Jacobian Y →ₜ+ Jacobian X`, and Jacobian/Solution.lean lines 178–180 state the smoothness with the models in that order.'
- q: 'Which linear map on ℂ^g underlies the pullback?'
  type: choice
  choices:
  - 'The transpose of the trace-of-forms map `H⁰(X, Ω¹) → H⁰(Y, Ω¹)`, in basis coordinates'
  - 'The identity'
  - 'The transpose of pullback-of-forms'
  answer: 0
  explain: '[traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) is the trace map in basis coordinates (Jacobian/TraceDegree/PullbackTraceLiftU.lean lines 55–60) and [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU) is its matrix transpose (Jacobian/TraceDegree/PullbackTraceLiftU.lean lines 67–70). The transpose of pullback-of-forms is what underlies the pushforward instead.'
- q: 'Where is the genuinely hard work for pullback, if not in holomorphy?'
  type: choice
  choices:
  - 'In the chart computation'
  - 'In showing that the trace map carries the period lattice of Y into that of X, which is done through a multiplicity-weighted fibre potential rather than by lifting curves'
  - 'In the universe transport'
  answer: 1
  explain: '[traceDualPullbackLift_preserves_latticeU](#/node/TraceDegree.traceDualPullbackLift_preserves_latticeU) (Jacobian/TraceDegree/AnalyticPullbackU.lean lines 64–90) splits on constancy and calls `traceDualPullbackLift_genuinePeriods` in the nonconstant case.'
---
## Plain English

A holomorphic map `f : X → Y` induces [pullback](#/node/Jacobian.pullback) from J(Y) to J(X), going the opposite way to `f`. This theorem says that map is holomorphic:

  `ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf)`

(Jacobian/Solution.lean lines 178–188).

As with [pushforward](#/node/Jacobian.pushforward_contMDiff), the reason is that the map on the quotient tori comes from a continuous linear map on ℂ^g. Specifically, the trace (or norm) of a holomorphic 1-form along `f` is a holomorphic 1-form on Y: at a point with no ramification you sum the form over the preimages, pulled back through the inverses of the local derivatives. That gives a linear map `H⁰(X, Ω¹) → H⁰(Y, Ω¹)`, and its transpose in basis coordinates is the linear map that descends to `pullback`.

The work that makes `pullback` exist is not in this theorem. It is in showing the transpose carries the period lattice of Y into that of X, proved without lifting curves, by a multiplicity-weighted sum of integrals over the fibre (Jacobian/TraceDegree/AnalyticPullbackU.lean lines 64–90). After that, holomorphy is the same chart argument as on the pushforward side.

## Why it matters

The specification asks for it (Jacobian/Challenge.lean lines 134–137). Pullback is a continuous group homomorphism by its type and analytic by this theorem, which makes it a morphism of complex Lie groups. The same trace map carries the degree identity in [pushforward_pullback](#/node/Jacobian.pushforward_pullback).

## How the proof goes

Jacobian/Solution.lean lines 181–188: unfold the bundled homomorphism to `fun a => ULift.up (analyticPullbackU f hf a.down)` and compose [contMDiff_uLift_down](#/node/ComplexTorus.contMDiff_uLift_down), [analyticPullback_contMDiffU](#/node/TraceDegree.analyticPullback_contMDiffU) and [contMDiff_uLift_up](#/node/ComplexTorus.contMDiff_uLift_up).

The analytic statement (Jacobian/TraceDegree/AnalyticPullbackContMDiffU.lean lines 65–112) works pointwise on the torus J(Y). On the chart source at `q`, the pullback agrees with `q' ↦ mk (traceDualPullbackLiftCLMU f hf (chart q'))`, because a chart on a complex torus is a local section of the quotient map and the descent is representative-compatible by `rfl` ([analyticPullback_mk_spec_rawU](#/node/TraceDegree.analyticPullback_mk_spec_rawU), Jacobian/TraceDegree/AnalyticPullbackContMDiffU.lean lines 51–57). The three factors are analytic: `contMDiffOn_chart`, `ContinuousLinearMap.contMDiff`, and [contMDiff_mk](#/node/ComplexTorus.contMDiff_mk). Congruence on the chart source then gives smoothness at `q`.

## What it does not say

- Not a divisor pullback. The construction is the trace of forms; nothing connects it to divisors, line bundles or Picard groups.
- No exported theorem that `pullback` is zero for constant `f`, although it is (the proof of lattice preservation establishes it along the way).
- Nothing about injectivity, surjectivity or the kernel of `pullback`.
