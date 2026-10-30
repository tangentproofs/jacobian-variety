---
id: Jacobian.pushforward_contMDiff
title: Pushforward is holomorphic
summary: 'Holomorphy of the pushforward is nearly free: the map on Jacobians descends from a continuous linear map on ℂ^g, and linear maps are analytic.'
review: draft
authors:
- claude
caveats:
- '"Holomorphic" is `ContMDiff` at level `ω` between the coordinate models `Fin (genus X) → ℂ` and `Fin (genus Y) → ℂ`. Those models use chosen bases of holomorphic 1-forms on X and on Y, so this is smoothness of a coordinate presentation of the pushforward.'
- '[pushforward](#/node/Jacobian.pushforward) is the form-theoretic map: in coordinates it is the transpose of pullback-of-forms `f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`. No compatibility with divisors or with [ofCurve](#/node/Jacobian.ofCurve) is proved.'
- 'The theorem is about the map underlying the bundled `Jacobian X →ₜ+ Jacobian Y`. Continuity is already part of that bundle; this upgrades it to analyticity.'
quiz:
- q: 'Why is holomorphy of the pushforward comparatively cheap?'
  type: choice
  choices:
  - 'Because the Jacobian is compact'
  - 'Because the map is the descent of a continuous linear map on ℂ^g, and locally the charts on the torus are sections of the quotient, so it is a composition of analytic maps'
  - 'Because the degree is finite'
  answer: 1
  explain: 'Jacobian/TraceDegree/AnalyticPushforwardContMDiffU.lean lines 65–112 run exactly that: `mk ∘ pushforwardTraceLiftCLMU ∘ chart` on each chart source, using `ContinuousLinearMap.contMDiff`.'
- q: 'What are the two source-to-target models in the statement?'
  type: choice
  choices:
  - '`𝓘(ℂ)` to `𝓘(ℂ)`'
  - '`modelWithCornersSelf ℂ (Fin (genus X) → ℂ)` to `modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)`'
  - 'ℝ² to ℝ²'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 140–142 state the models explicitly; the Jacobians have complex dimension `genus X` and `genus Y`.'
- q: 'What does the `show` step at the start of the Lean proof accomplish?'
  type: choice
  choices:
  - 'It unfolds the bundled homomorphism to the plain function `fun a => ULift.up (analyticPushforwardU f hf a.down)`, so the two `ULift` transport lemmas can be composed around the analytic statement'
  - 'It applies the chain rule'
  - 'It changes the smoothness index'
  answer: 0
  explain: 'Jacobian/Solution.lean lines 143–150 rewrite to that function and then compose `contMDiff_uLift_up`, `analyticPushforward_contMDiffU` and `contMDiff_uLift_down`.'
---
## Plain English

A holomorphic map `f : X → Y` of compact Riemann surfaces induces [pushforward](#/node/Jacobian.pushforward) from J(X) to J(Y). This theorem says that map is holomorphic as a map of complex manifolds:

  `ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf)`

(Jacobian/Solution.lean lines 140–150). The source has complex dimension `genus X`, the target `genus Y`, which need not be equal.

Why it is true is structural rather than deep. The pushforward on Jacobians is not defined directly on the quotients. It is defined upstairs, as a continuous linear map on ℂ^g, and then shown to carry the [period lattice](#/node/Periods.periodFullComplexLatticeU) of X into the period lattice of Y, which is what lets it descend. Continuous linear maps are analytic, and the charts on a complex torus are local sections of the quotient projection. So the composite is analytic chart by chart.

## Why it matters

The specification asks for it (Jacobian/Challenge.lean lines 110–113). Together with the group-homomorphism property packaged into the type `Jacobian X →ₜ+ Jacobian Y`, it makes the pushforward a morphism of complex Lie groups, which is the right notion for Jacobians. It is also where the manifold structure on the Jacobian gets used: `ContMDiff` is checked against the torus atlas, whose charts are local sections of ℂ^g → ℂ^g/Λ.

## How the proof goes

The public proof (Jacobian/Solution.lean lines 143–150) unfolds the bundled homomorphism to a plain function and composes three facts: [contMDiff_uLift_down](#/node/ComplexTorus.contMDiff_uLift_down) to leave the universe wrapper, [analyticPushforward_contMDiffU](#/node/TraceDegree.analyticPushforward_contMDiffU) for the real statement, and [contMDiff_uLift_up](#/node/ComplexTorus.contMDiff_uLift_up) to re-enter it (Jacobian/ComplexTorus/ULiftTransport.lean lines 380–399).

The analytic statement (Jacobian/TraceDegree/AnalyticPushforwardContMDiffU.lean lines 65–112) is checked at each point `q` of the torus. On the source of the chart at `q`, the pushforward agrees with

  `q' ↦ mk (pushforwardTraceLiftCLMU f hf (chart q'))`

because the chart is a section of `mk` (`chart.left_inv'`) and the descent is compatible with representatives ([analyticPushforward_mk_spec_rawU](#/node/TraceDegree.analyticPushforward_mk_spec_rawU), Jacobian/TraceDegree/AnalyticPushforwardContMDiffU.lean lines 52–58, which holds by `rfl`). That composite is analytic: `contMDiffOn_chart` for the chart, `ContinuousLinearMap.contMDiff` for [pushforwardTraceLiftCLMU](#/node/TraceDegree.pushforwardTraceLiftCLMU), and [contMDiff_mk](#/node/ComplexTorus.contMDiff_mk) for the projection. `ContMDiffOn.congr` transfers it, and `ContMDiffOn.contMDiffAt` concludes.

## What it does not say

- Nothing about the pushforward being injective, surjective, or an isogeny.
- Nothing about divisors. The underlying linear map is the transpose of pullback-of-forms, and no divisor-level interpretation is proved.
- No compatibility with [ofCurve](#/node/Jacobian.ofCurve): there is no lemma saying the pushforward of an Abel–Jacobi image is the Abel–Jacobi image of the mapped point.
