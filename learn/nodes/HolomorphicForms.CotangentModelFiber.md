---
id: HolomorphicForms.CotangentModelFiber
title: The model fiber of the cotangent bundle
summary: A cotangent vector on a Riemann surface is a continuous ℂ-linear map ℂ → ℂ, which is the same as a single complex number, the coefficient of dz.
review: draft
authors:
- claude
caveats:
- 'This is an `abbrev`, so it is not a new type: it unfolds to `E →L[ℂ] ℂ` and Lean treats the two as interchangeable.'
- It is the ℂ-linear dual of E, not the real dual. On a complex manifold that makes it the holomorphic cotangent bundle (the (1,0) part), not the full real cotangent bundle, which would also contain dz̄.
- Nothing here is holomorphic yet. This is only the type a cotangent vector lives in; holomorphy enters when you ask for sections.
quiz:
- q: What is `CotangentModelFiber E` literally defined to be?
  type: choice
  choices:
  - The continuous ℂ-linear maps from E to ℂ
  - The continuous ℝ-linear maps from E to ℝ
  - E itself
  answer: 0
  explain: 'The body is `E →L[ℂ] ℂ` (Jacobian/HolomorphicForms/CotangentBundle.lean lines 85–87); `→L[ℂ]` is Mathlib notation for continuous ℂ-linear maps.'
- q: For a Riemann surface the model space is E = ℂ. How many complex numbers does it take to pin down an element of `CotangentModelFiber ℂ`?
  type: choice
  choices:
  - One
  - Two
  - Infinitely many
  answer: 0
  explain: '`clm_apply_eq_mul''` (Jacobian/HolomorphicForms/Finiteness.lean lines 59–60) proves `L v = v * L 1`, so L is determined by the single number `L 1`.'
- q: Why does a vector bundle in Mathlib need a declared model fiber at all?
  type: choice
  choices:
  - Because local trivialisations identify the bundle over a small open set with (open set) × (model fiber)
  - Because the fibers at different points are literally the same type
  - Because the bundle has to be finite-dimensional
  answer: 0
  explain: The model fiber is the fixed type F in Mathlib's trivialisation data; it is why `CotangentModelFiber E` is passed alongside the fiberwise [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) in the bundle instance checked at Jacobian/HolomorphicForms/CotangentBundle.lean lines 95–100.
- q: Does this declaration say anything about the surface X?
  type: choice
  choices:
  - No, it only mentions the model space E
  - Yes, it quantifies over all points of X
  - Yes, it requires X to be compact
  answer: 0
  explain: The declaration takes only `E` and its norm/ℂ-vector-space instances (Jacobian/HolomorphicForms/CotangentBundle.lean lines 85–87). X appears in [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) instead.
---
## Plain English

A 1-form is a thing you integrate along a path. To integrate, at every point of the surface you need a rule that eats a tangent direction and returns a number. `CotangentModelFiber E` is the type of such rules on the model space E:

```
CotangentModelFiber E = E →L[ℂ] ℂ
```

`→L[ℂ]` is Mathlib's notation for continuous ℂ-linear maps. So an element is a continuous linear functional on E with complex values.

For a Riemann surface the model space is E = ℂ, one complex dimension. Then this type is `ℂ →L[ℂ] ℂ`, and any such map is multiplication by its value at 1: `L v = v * L 1` (Jacobian/HolomorphicForms/Finiteness.lean lines 59–60). That one complex number is the classical coefficient `a` in `ω = a dz`. The project uses exactly this later: [chartCoeff](#/node/HolomorphicForms.chartCoeff) reads a form in a chart by evaluating it at 1.

## Why it is defined this way

Mathlib's vector bundles are indexed families of fibers plus local trivialisations, and a trivialisation needs one fixed type to trivialise *onto*. That type is the model fiber. Here the fiber at a point is [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) and the model fiber is `CotangentModelFiber E`; supplying both lets Mathlib's hom-bundle instance produce `VectorBundle ℂ (CotangentModelFiber E) (CotangentSpace E X)` with no extra work, which is checked as a sanity `example` at Jacobian/HolomorphicForms/CotangentBundle.lean lines 95–100.

Defined at Jacobian/HolomorphicForms/CotangentBundle.lean lines 85–87.
