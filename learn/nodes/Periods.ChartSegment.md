---
id: Periods.ChartSegment
title: Chart segments, the atoms of a curve
summary: 'A piece of a curve on the surface is recorded as a straight line in one chart together with a ball containing it, so every integral becomes an ordinary integral in ℂ.'
review: draft
authors:
- claude
caveats:
- 'The docstring says the segment "is the curve t ↦ c⁻¹((1-t)a + tb)" on the surface. The Lean never builds that curve. It only integrates the chart reading of ω along the straight segment from `a` to `b` inside ℂ.'
- 'There is no field saying `radius > 0`. Positivity is forced by `a_mem : a ∈ ball center radius`, since an empty ball has no members.'
- 'Nothing forbids `a = b`. A degenerate segment is allowed, and `ChartSegment.integral_eq_sub` (Jacobian/Periods/ChartChain.lean lines 205–208) writes its integral as a difference of the same primitive value, hence 0.'
- 'The structure is defined for any complex 1-manifold modelled on ℂ with analytic chart transitions. Compactness and connectedness of X are not assumed here.'
quiz:
- q: 'What data does a `ChartSegment X` carry?'
  type: choice
  choices:
  - 'A continuous map from the interval [0,1] into X'
  - 'A point `p` of X, two chart coordinates `a` and `b`, and a ball in the chart target containing both'
  - 'A finite set of points of X together with a chart around each'
  answer: 1
  explain: 'The structure fields at Jacobian/Periods/ChartChain.lean lines 143–156 are `p`, `a`, `b`, `center`, `radius` and three proofs. No map out of an interval appears.'
- q: 'Why does the structure insist that the ball lies inside the chart target (`ball_subset`)?'
  type: choice
  choices:
  - 'So that the chart reading of ω is defined on the whole ball and has a primitive there'
  - 'So that the segment has positive length'
  - 'So that the chart is injective on the ball'
  answer: 0
  explain: '`ChartSegment.integral_eq_sub` at Jacobian/Periods/ChartChain.lean lines 205–208 uses `chartForm_segment_eq_sub` at Jacobian/Periods/ChartChain.lean lines 104–116, the Poincaré-lemma argument that needs ω readable and closed on the whole ball.'
- q: 'What are `start` and `stop` of a segment?'
  type: choice
  choices:
  - 'The numbers `a` and `b` themselves'
  - 'The images of `a` and `b` under the inverse of the chart at `p`'
  - 'The two endpoints of a diameter of the ball'
  answer: 1
  explain: 'Jacobian/Periods/ChartChain.lean lines 162–166 define start as `(chartAt ℂ s.p).symm s.a` and stop as `(chartAt ℂ s.p).symm s.b`, which are points of X.'
- q: 'Does the Lean require the radius to be positive?'
  type: choice
  choices:
  - 'Yes, there is an explicit positivity field'
  - 'No, and the radius may be zero or negative'
  - 'There is no explicit field, but `a_mem` forces positivity'
  answer: 2
  explain: 'Jacobian/Periods/ChartChain.lean lines 150–156 list no positivity field, but `a ∈ ball center radius` is impossible unless the radius is positive, which is how Jacobian/Periods/ChartChain.lean line 109 extracts it.'
---
## Plain English

To build the Jacobian of a Riemann surface X you have to integrate holomorphic 1-forms along curves in X. Doing that for an arbitrary piecewise-smooth path on a manifold takes a lot of machinery. This file takes a cheaper route: it only integrates along pieces that are straight lines when you look at them through a single chart.

A `ChartSegment X` is exactly that piece of data (`Jacobian/Periods/ChartChain.lean` lines 143–156):

- a point `p` of X, whose chart `c = chartAt ℂ p` will be used;
- two complex numbers `a` and `b`, the start and end in chart coordinates;
- a ball in the chart target, given by `center` and `radius`, with proofs that the ball sits inside the chart target and that both `a` and `b` lie in it.

Because a ball is convex, the whole straight line from `a` to `b` stays inside it, hence inside the chart target (Jacobian/Periods/ChartChain.lean lines 172–174). The two endpoints of the segment on the surface are `start` and `stop`, the chart inverse applied to `a` and `b` (Jacobian/Periods/ChartChain.lean lines 162–166).

The integral of a form ω along the segment is defined in the chart (Jacobian/Periods/ChartChain.lean lines 168–170): take [chartForm](#/node/Periods.chartForm), the reading of ω in the chart at `p`, and integrate it along the straight path from `a` to `b` in ℂ. So "integrate over a curve in X" has been reduced to a one-variable curve integral.

## Why the ball matters

The ball is not decoration. On a ball inside the chart target the chart reading of ω has a holomorphic primitive, so the segment integral is a difference of primitive values at the two ends (Jacobian/Periods/ChartChain.lean lines 205–208). That local exactness is what makes everything downstream work. It is the reason the Abel–Jacobi map turns out to be holomorphic.

Segments glue into [chains](#/node/Periods.IsChain), and chains are integrated by [chainIntegral](#/node/Periods.chainIntegral).
