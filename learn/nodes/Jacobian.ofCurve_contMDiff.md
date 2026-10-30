---
id: Jacobian.ofCurve_contMDiff
title: The Abel–Jacobi map is holomorphic
summary: 'The integral from a base point is holomorphic in its endpoint even though the chain used to compute it is picked by a non-canonical choice, because changing the chain only changes the answer by a period.'
review: draft
authors:
- claude
caveats:
- 'The underlying vector of integrals is *not* a holomorphic function X → ℂ^g, and could not be: a holomorphic map from a compact surface into ℂ^g is constant. Only the composite with the quotient by the lattice is holomorphic. The file history note at Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 17–22 records a former placeholder whose smoothness field was unsatisfiable for exactly this reason.'
- 'The chain from P to Q is chosen by `Classical.choose` ([chosenChain](#/node/AbelJacobi.chosenChain), Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 37–38), so `ofCurve` is not given by a canonical formula. Independence of the choice holds only modulo the period lattice.'
- 'Holomorphy is expressed as `ContMDiff` at level `ω`, which is `(⊤ : WithTop ℕ∞)` in Mathlib''s smoothness scale, between the models `𝓘(ℂ)` on X and `modelWithCornersSelf ℂ (Fin (genus X) → ℂ)` on the Jacobian. Reading this as *complex* analyticity rather than real analyticity relies on the meaning of `ω`-`ContMDiff` over a complex model with corners in the pinned Mathlib; that is standard but is a Mathlib-side fact, not proved here.'
- 'The target is `Jacobian X`, which is `ULift` of ℂ^g/Λ, and ℂ^g uses a chosen basis of holomorphic 1-forms (`holomorphicOneFormFinBasis`). So this is holomorphy into a coordinate model of the Jacobian, which is canonical only up to the basis choice.'
quiz:
- q: 'Is the vector of integrals `Q ↦ (∫_P^Q ω₁, …, ∫_P^Q ω_g)` itself a holomorphic map X → ℂ^g?'
  type: choice
  choices:
  - 'Yes, that is what the theorem says'
  - 'No. It is not even well defined without choosing a chain, and a holomorphic map from a compact surface to ℂ^g would be constant. Only its class modulo the lattice is holomorphic'
  - 'Only for genus 1'
  answer: 1
  explain: 'The theorem is about `ofCurve P`, whose values live in the quotient (Jacobian/Solution.lean lines 105–107). Jacobian/AbelJacobi/PathIntegralFunctionalU.lean lines 17–22 note explicitly that a genuine single-valued holomorphic X → ℂ^g would have to be constant.'
- q: 'What is the local formula used to prove holomorphy near a point Q₀?'
  type: choice
  choices:
  - '`Q ↦ [v₀ + G(c Q)]`, where `c` is the chart at Q₀, `v₀` the period vector of a chain from P to Q₀, and `G` a vector of holomorphic primitives of the chart readings of the basis forms'
  - '`Q ↦ 0` near Q₀'
  - 'A power series in the genus'
  answer: 0
  explain: 'Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 103–118 set up exactly that `h` and prove `analyticOfCurveU X P =ᶠ[nhds Q₀] h`.'
- q: 'Which fact lets the proof replace the globally chosen chain by "chain to Q₀, then one straight segment"?'
  type: choice
  choices:
  - 'The chosen chain is already of that form'
  - 'The value of the map is the class of the period vector of *any* chain with the right endpoints, because two such chains differ by a lattice element'
  - 'Compactness of X'
  answer: 1
  explain: '`analyticOfCurveU_eq_mk_periodVector` (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 64–72) rests on `pathIntegralFunctionalU_sub_mem`, which is immediate from how the period lattice is generated.'
- q: 'What role does `ULift` play in the statement?'
  type: choice
  choices:
  - 'It makes the quotient compact'
  - 'It moves ℂ^g/Λ into the universe of X, as the spec demands; `contMDiff_uLift_up` transports smoothness across it'
  - 'It records the choice of basis of holomorphic 1-forms'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 109–113 compose `ComplexTorus.contMDiff_uLift_up` (Jacobian/ComplexTorus/ULiftTransport.lean lines 380–386) with the analytic statement.'
---
## Plain English

The [Abel–Jacobi map](#/node/Jacobian.ofCurve) sends a point Q of the surface to the integrals of a basis of holomorphic 1-forms from the base point P to Q, read modulo the [period lattice](#/node/Periods.periodFullComplexLatticeU). This theorem says that map is holomorphic, as a map of complex manifolds from X to the Jacobian:

  `ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P)`

(Jacobian/Solution.lean lines 109–113). The source model is one complex dimension, the target model is `genus X` complex dimensions, and `ω` is the top (analytic) level of Mathlib's smoothness scale.

To compute the integrals you need a path, and the definition picks one by [Classical choice](#/node/AbelJacobi.chosenChain). As Q moves the chosen path can jump arbitrarily, so the raw vector of integrals is a wildly discontinuous function of Q. What saves the statement is that two paths with the same endpoints give integrals differing by a lattice element, so after projecting to ℂ^g/Λ the jumps vanish. The quotient is not an inconvenience to be worked around; it is what makes the map continuous at all.

## Why it matters

The challenge requires the Jacobian to be a compact complex Lie group and the Abel–Jacobi map to be a holomorphic map into it (Jacobian/Challenge.lean lines 79–87 and Jacobian/Challenge.lean lines 92–93). Together with [injectivity](#/node/Jacobian.ofCurve_inj), holomorphy is what makes `ofCurve` a map of complex manifolds and not just a set-theoretic labelling. A `Jacobian X := PUnit` answer satisfies holomorphy trivially; a definition that satisfies holomorphy *and* injectivity for positive genus cannot be trivial.

It also uses the manifold structure on the Jacobian: `ContMDiff` into it makes sense because the quotient carries charts built from local sections of ℂ^g → ℂ^g/Λ, with analytic transitions.

## How the proof goes

Two steps (Jacobian/Solution.lean lines 109–113): compose [contMDiff_uLift_up](#/node/ComplexTorus.contMDiff_uLift_up) (Jacobian/ComplexTorus/ULiftTransport.lean lines 380–386), the universe move, with [analyticOfCurve_contMDiffU](#/node/AbelJacobi.analyticOfCurve_contMDiffU) (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 82–128).

The analytic statement is proved pointwise. Fix Q₀. Let `c` be the chart at Q₀ and take a ball `B = ball (c Q₀) r` inside the chart's target. Define, for `w ∈ B`,

  `G w i = ∫ along the straight segment from c Q₀ to w of the chart reading of ω_i`.

Each component is a holomorphic primitive on the ball, by [chartForm_hasFDerivAt_primitive](#/node/Periods.chartForm_hasFDerivAt_primitive): the chart reading of a holomorphic 1-form is a holomorphic function times `dz`, and integrating it along segments from a fixed centre gives a function whose derivative is that function (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 96–101).

Now the local formula. Let `v₀` be the [period vector](#/node/Periods.periodVector) of the chosen chain from P to Q₀. For Q in the chart neighbourhood, the single chart segment from Q₀ to Q is a legal [ChartSegment](#/node/Periods.ChartSegment), so "chain to Q₀, then that segment" is a chain from P to Q. Its period vector is `v₀ + G (c Q)` because [chainIntegral](#/node/Periods.chainIntegral) is additive over concatenation. And the value of the map on *any* chain with those endpoints is the same class, by [analyticOfCurveU_eq_mk_periodVector](#/node/AbelJacobi.analyticOfCurveU_eq_mk_periodVector) (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 64–72). Hence

  `ofCurve P` agrees, on a neighbourhood of Q₀, with `Q ↦ [v₀ + G (c Q)]`.

That function is a composition of three holomorphic things: the chart `c`, the affine map `w ↦ v₀ + G w`, and the quotient projection [mk](#/node/ComplexTorus.mk), whose holomorphy is [contMDiff_mk](#/node/ComplexTorus.contMDiff_mk). `ContMDiffAt.congr_of_eventuallyEq` finishes it (Jacobian/AbelJacobi/AnalyticOfCurveU.lean line 119).

Note where the lattice enters: only in the step "any chain with the same endpoints gives the same value". That is not a theorem about homotopy or homology. It holds by the definition of the [period subgroup](#/node/Periods.genuinePeriodSubgroup), which is generated by exactly the differences of period vectors of same-endpoint chains.

## What it does not say

- Not that the integral vector is a holomorphic function into ℂ^g. It is not a function at all until a chain is chosen, and after choosing it is not continuous. The theorem is about the composite with the quotient map.
- Not that `ofCurve P` is an immersion or an embedding, and nothing about its differential being nonzero. Injectivity is a separate theorem with a genus hypothesis.
- Not biholomorphy onto its image, and nothing about the image being a subvariety.
- Nothing about independence of the base point P, or about the canonical-up-to-basis status of the coordinate model ℂ^g: the identification uses a chosen basis of holomorphic 1-forms.
