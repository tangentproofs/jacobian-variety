---
id: AbelJacobi.analyticOfCurveU
title: The Abel–Jacobi map
summary: 'The map built from a discontinuous choice of paths becomes holomorphic once you pass to the quotient, because locally the integral differs from a chart primitive only by a constant.'
review: draft
authors:
- claude
caveats:
- 'The map depends on the base point P, which is an argument. There is no canonical base point and no claim of independence from it.'
- 'Three things are proved in Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 56–128: the base point goes to 0, the value is the class of the period vector of any chain from P to Q, and the map is holomorphic. Injectivity is proved elsewhere and only for positive genus.'
- 'Nothing about surjectivity, Jacobi inversion, the divisor form of Abel theorem, or a group structure on divisor classes appears anywhere. Abel–Jacobi is treated here as a map of points, not of divisors.'
- 'The target is the basis-aligned carrier ℂ^g/Λ, which depends on the arbitrary chosen basis of holomorphic 1-forms.'
quiz:
- q: 'How is `analyticOfCurveU X P` defined?'
  type: choice
  choices:
  - 'As the quotient class of the chosen-path integral vector from P to Q'
  - 'As a limit of integrals over shorter and shorter paths'
  - 'As the unique holomorphic map sending P to 0'
  answer: 0
  explain: 'Lines 48–54 of Jacobian/AbelJacobi/AnalyticOfCurveU.lean apply `ComplexTorus.mk` to `pathIntegralFunctionalU X P Q`.'
- q: 'Why is the value independent of which chain is used?'
  type: choice
  choices:
  - 'Because any two chains from P to Q have equal period vectors'
  - 'Because their period vectors differ by an element of Λ, which is quotiented out'
  - 'Because the chosen chain is canonical'
  answer: 1
  explain: '`analyticOfCurveU_eq_mk_periodVector` at Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 60–72 derives the equality of classes from `pathIntegralFunctionalU_sub_mem`, which gives membership in Λ, not equality in ℂ^g.'
- q: 'What local formula makes the map holomorphic?'
  type: choice
  choices:
  - 'Near Q₀ it equals the class of a constant plus a vector of chart primitives of the basis forms'
  - 'Near Q₀ it equals a linear map in the chart coordinate'
  - 'Near Q₀ it is constant'
  answer: 0
  explain: 'The proof at Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 74–128 rewrites the map near Q₀ as `Q ↦ [periodVector l₀ + G (c Q)]`, where G integrates the chart readings of the basis forms along the segment from the chart coordinate of Q₀, and is holomorphic by `chartForm_hasFDerivAt_primitive`.'
- q: 'What does the theorem about the base point say?'
  type: choice
  choices:
  - 'That the integral from P to P is zero'
  - 'That the integral from P to P is a period, so its class is zero'
  - 'That P is the only point mapping to zero'
  answer: 1
  explain: '`analyticOfCurve_selfU` at Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 56–58 goes through `mk_eq_zero_iff` and `pathIntegralFunctionalU_self_mem`, which says the self-integral lies in Λ.'
- q: 'Is the map injective?'
  type: choice
  choices:
  - 'Yes, always'
  - 'Yes when the genus is positive, by a separate theorem'
  - 'No'
  answer: 1
  explain: '`analyticOfCurve_injectiveU` in Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean needs `0 < analyticGenus ℂ X`, and rests on the two-point form of Abel theorem at Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean lines 31–48. For genus 0 the Jacobian is a single point.'
---
## Plain English

This is the Abel–Jacobi map. Fix a base point P. Send Q to the class modulo the [period lattice](#/node/Periods.periodFullComplexLatticeU) of the vector of integrals from P to Q (`Jacobian/AbelJacobi/AnalyticOfCurveU.lean` lines 48–54):

  Q ↦ [(∫_P^Q ω₁, …, ∫_P^Q ω_g)] ∈ ℂ^g/Λ.

Three facts are proved about it in this file.

The value does not depend on the path. More precisely, for *any* chain l from P to Q, the value is the class of the period vector of l (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 60–72). This follows from lattice membership, not from equality of integrals.

The base point goes to zero (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 56–58). Note the shape of the argument: the integral from P to P along the chosen closed chain need not vanish, but it is a period, so its class is 0.

The map is holomorphic (Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 74–128). This is the surprising one, given that the vector it is built from is not even continuous.

## Why holomorphy works

Pick a point Q₀ and a chart c around it, and a ball B inside the chart target. For Q in that ball, append to the chosen chain from P to Q₀ one extra segment, the straight line from c Q₀ to c Q. That gives a chain from P to Q, so by the path-independence lemma the value is the class of

  periodVector(chain to Q₀) + (∫ ω₁, …, ∫ ω_g over the extra segment).

The first term is a constant. The second is a vector of integrals from the fixed point c Q₀, which is exactly the local primitive of the chart reading of each basis form, holomorphic on B by [chartForm_hasFDerivAt_primitive](#/node/Periods.chartForm_hasFDerivAt_primitive). So locally the map is a constant plus a holomorphic function, followed by the quotient projection, which is holomorphic.

The path-choosing arbitrariness is invisible in this local formula. It is absorbed into the constant.

The public version of this map is [Jacobian.ofCurve](#/node/Jacobian.ofCurve), which is this followed by a universe relabelling.
