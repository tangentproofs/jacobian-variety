---
id: HolomorphicForms.CotangentSpace
title: The cotangent space at a point
summary: The target is written as the trivial line bundle `Bundle.Trivial X ℂ` rather than plain ℂ, and that bookkeeping choice is what makes Mathlib hand over the whole cotangent vector bundle for free.
review: draft
authors:
- claude
caveats:
- 'This is an `abbrev`, not a structure: it unfolds to a type of continuous linear maps, with no cocycle or compatibility condition written by hand. All the bundle compatibility comes from Mathlib''s tangent bundle and hom-bundle instances.'
- 'The model space E is an explicit argument rather than inferred, because Mathlib''s `TangentSpace` is indexed by a `ModelWithCorners` and the file wants `modelWithCornersSelf ℂ E` fixed. The docstring at Jacobian/HolomorphicForms/CotangentBundle.lean lines 72–77 says so.'
- 'Two norm instances are transported onto `TangentSpace` from E through the type synonym (Jacobian/HolomorphicForms/CotangentBundle.lean lines 55–70). They are honest transports of E''s own structure, not new assumptions, but downstream files must set `backward.isDefEq.respectTransparency false` for Lean to see through the synonym; the file flags this at Jacobian/HolomorphicForms/CotangentBundle.lean lines 45–49.'
- It is the ℂ-linear dual of the tangent space, so this is the holomorphic cotangent space, not the full real cotangent space.
quiz:
- q: What is an element of `CotangentSpace E X x`?
  type: choice
  choices:
  - A continuous ℂ-linear map from the tangent space at x to ℂ
  - A tangent vector at x
  - A holomorphic function defined near x
  answer: 0
  explain: The body is `TangentSpace (modelWithCornersSelf ℂ E) x →L[ℂ] (Bundle.Trivial X ℂ) x` (Jacobian/HolomorphicForms/CotangentBundle.lean lines 78–82), and the fiber of the trivial line bundle at x is ℂ.
- q: Why is the target written `(Bundle.Trivial X ℂ) x` instead of just `ℂ`?
  type: choice
  choices:
  - So that Mathlib's bundle-of-continuous-linear-maps construction applies and the `VectorBundle` instance is automatic
  - Because the value of a 1-form is not really a complex number
  - Because ℂ is not a normed space
  answer: 0
  explain: The file header (Jacobian/HolomorphicForms/CotangentBundle.lean lines 6–21) explains that the cotangent bundle is `Bundle.ContinuousLinearMap` applied to the tangent bundle and the trivial line bundle; the `example` at Jacobian/HolomorphicForms/CotangentBundle.lean lines 95–100 confirms the instance is found by `inferInstance`.
- q: Does `CotangentSpace` impose a holomorphy condition?
  type: choice
  choices:
  - No, it is just the type of the fiber at one point
  - Yes, it requires the functional to be holomorphic in x
  - Yes, it requires the functional to be ℂ-analytic on the tangent space
  answer: 0
  explain: A single point has no room for a regularity condition. Holomorphy appears one level up, in [HolomorphicOneForm](#/node/HolomorphicForms.HolomorphicOneForm), which asks for an analytic *section* of this bundle.
- q: For a Riemann surface (E = ℂ), what is the complex dimension of `CotangentSpace ℂ X x`?
  type: choice
  choices:
  - '1'
  - '2'
  - It depends on the genus of X
  answer: 0
  explain: The tangent space is modeled on ℂ, so the ℂ-linear dual is `ℂ →L[ℂ] ℂ`, one-dimensional (see [CotangentModelFiber](#/node/HolomorphicForms.CotangentModelFiber) and `clm_apply_eq_mul'` at Jacobian/HolomorphicForms/Finiteness.lean lines 59–60).
---
## Plain English

Fix a point `x` on the surface. The tangent space at `x` holds the directions you can move in. The cotangent space holds the things that measure those directions:

```
CotangentSpace E X x = TangentSpace 𝓘(ℂ, E) x →L[ℂ] (Bundle.Trivial X ℂ) x
```

An element is a continuous ℂ-linear functional on the tangent space at `x`. For a Riemann surface the tangent space is one complex dimension, so the cotangent space is too; its elements are the "`a dz` at the point `x`" of a calculus course.

Defined at Jacobian/HolomorphicForms/CotangentBundle.lean lines 78–82.

## Why it is defined this way

Two details look like noise and are not.

First, the target is `(Bundle.Trivial X ℂ) x` and not `ℂ`. As a type these are the same thing, but writing it as a fiber of the trivial line bundle makes the whole family `x ↦ CotangentSpace E X x` literally an instance of Mathlib's `Bundle.ContinuousLinearMap` applied to two bundles over X. The payoff is that `VectorBundle ℂ (CotangentModelFiber E) (CotangentSpace E X)` needs no proof at all: the sanity `example` at Jacobian/HolomorphicForms/CotangentBundle.lean lines 95–100 closes it with `inferInstance`. The classical "a 1-form is a collection of chart coefficients satisfying a transformation rule" is never written down here; it is inherited from Mathlib's trivialisations.

Second, `E` is passed explicitly. Mathlib's `TangentSpace` is indexed by a `ModelWithCorners`, so the file fixes `modelWithCornersSelf ℂ E` and hands `E` along (docstring at Jacobian/HolomorphicForms/CotangentBundle.lean lines 72–77).

One wrinkle the file is open about: in the pinned Mathlib, `TangentSpace I x` is a non-reducible synonym for `E` that carries no norm, so the operator norm on the cotangent fiber cannot be synthesized. The file transports E's norm through the synonym at Jacobian/HolomorphicForms/CotangentBundle.lean lines 55–70, and notes at Jacobian/HolomorphicForms/CotangentBundle.lean lines 45–49 that consumers need `set_option backward.isDefEq.respectTransparency false` to use it.
