---
id: HolomorphicForms.pullbackFormsFunFiber
title: Pulling back a 1-form at a single point
summary: 'This is the chain rule and nothing else, and it takes no differentiability hypothesis on f: if f happens not to be differentiable at x, Mathlib''s `mfderiv` returns 0 and the pullback silently returns the zero functional.'
review: draft
authors:
- claude
caveats:
- 'No hypothesis on `f` is required. `mfderiv` is a total function: by Mathlib''s convention it is `0` at points where `f` is not `MDifferentiableAt`. So for a badly behaved `f` this definition quietly returns the zero functional rather than failing. Every use in the project supplies an analytic `f`, but the definition itself does not demand one.'
- 'The docstring (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 52–54) states the composition is natively a map `TangentSpace 𝓘(ℂ,ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ,ℂ) (f x)`. That is a slip: the target of the composition is the trivial-bundle fibre, which reduces to ℂ. The rest of the docstring''s point stands, which is that `(Bundle.Trivial Y ℂ) (f x)` and `(Bundle.Trivial X ℂ) x` are both ℂ, so the composite already has the cotangent-fibre type over `x`.'
- 'This is only the value at one point. That the resulting family of functionals is a smooth section is a separate theorem, `pullbackFormsFunFiber_contMDiff_section` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 96–125).'
quiz:
- q: 'What is the formula being written down here?'
  type: choice
  choices:
  - '(f*η)_x = η_{f(x)} ∘ df_x'
  - '(f*η)_x = df_x ∘ η_x'
  - 'The sum of η over the fibre of f above x'
  answer: 0
  explain: 'The body is `(η.toFun (f x)).comp (mfderiv … f x)` — apply the derivative of f first, then the functional η at `f x`.'
- q: 'What differentiability hypothesis does this definition require?'
  type: choice
  choices:
  - '`ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f`'
  - '`MDifferentiableAt` at the point x'
  - 'None at all'
  answer: 2
  explain: 'The signature in `Jacobian/HolomorphicForms/PullbackBundled.lean` lines 58–63 takes only `f`, `η` and `x`; `mfderiv` is total and returns 0 where `f` is not differentiable.'
- q: 'Why does the composite already have the right type, without a cast?'
  type: choice
  choices:
  - 'Because a cast is inserted silently by Lean'
  - 'Because the cotangent fibre is `TangentSpace x →L[ℂ] (Bundle.Trivial X ℂ) x` and the trivial bundle''s fibre is the constant ℂ on both surfaces'
  - 'Because X and Y are assumed equal'
  answer: 1
  explain: '`CotangentSpace` is defined in `Jacobian/HolomorphicForms/CotangentBundle.lean` lines 78–82 with target `(Bundle.Trivial X ℂ) x`.'
- q: 'Is this a definition or a theorem?'
  type: choice
  choices:
  - 'A `noncomputable def`'
  - 'A theorem about the chain rule'
  - 'A typeclass instance'
  answer: 0
  explain: 'It introduces the object; the chain rule is being used as the definition of pullback, not proved here.'
---
## Plain English

A holomorphic 1-form η on a Riemann surface Y assigns to each point y a continuous ℂ-linear functional η_y on the tangent space at y. That is what [HolomorphicOneForm](#/node/HolomorphicForms.HolomorphicOneForm) ℂ Y means: a smooth section of the cotangent bundle, where the cotangent space at y is [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) ℂ Y y, continuous ℂ-linear maps from the tangent space at y to ℂ.

Given a map f : X → Y, you can move η backwards to X by the chain rule. At a point x of X, feed a tangent vector v at x through the derivative of f, landing in the tangent space at f(x), then apply η there:

```
(f*η)_x (v) = η_{f(x)} (df_x v)
```

That is exactly the body of `pullbackFormsFunFiber` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 58–63): the composition of `η.toFun (f x)` with `mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x`.

In coordinates, if η reads as h(w) dw near f(x) and f reads as w = φ(z), this is h(φ(z)) φ'(z) dz. The familiar substitution rule for integrals.

## Why it is defined this way

The word "natively" in the docstring is the point of this declaration. Lean has to be convinced that the composition really belongs to the cotangent fibre of X at x, not merely to something isomorphic to it. It does, because the cotangent space is defined with the *trivial* line bundle as target, whose fibre is the constant ℂ over every point of every surface. So `η_{f(x)} ∘ df_x` lands in `TangentSpace x →L[ℂ] ℂ`, which is literally the cotangent fibre over x. No transport, no coercion.

That matters later: the family `x ↦ (f*η)_x` has to be recognised as a section of a bundle over X, and bundle smoothness arguments are much harder if there is a cast in the way.

## How it is used

It is the underlying function of [pullbackFormsBundled](#/node/HolomorphicForms.pullbackFormsBundled), the honest 1-form f\*η on X, and through that of [pullbackFormsBundledLM](#/node/HolomorphicForms.pullbackFormsBundledLM), the linear map H⁰(Y, Ω¹) → H⁰(X, Ω¹) that drives the Jacobian pushforward. It also agrees by `rfl` with the unbundled [pullbackFormsFun](#/node/TraceDegree.pullbackFormsFun).
