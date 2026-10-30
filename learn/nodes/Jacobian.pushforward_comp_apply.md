---
id: Jacobian.pushforward_comp_apply
title: Pushforward respects composition
summary: 'Pushing forward along g ∘ f is the same as pushing along f then along g, and the whole proof is the chain rule for pullback of 1-forms plus a matrix transpose.'
review: draft
authors:
- claude
caveats:
- 'Stated pointwise for each `P : Jacobian X`, not as an equality of homomorphisms.'
- 'The smoothness argument on the left is literally `hg.comp hf`. `ContMDiff` is a `Prop`, so by proof irrelevance the value cannot depend on which proof that `g ∘ f` is holomorphic is supplied.'
- 'Covariant direction: `(g ∘ f)_* = g_* ∘ f_*`. The three surfaces X, Y, Z live in three independent universes `u_1`, `u_2`, `u_3`, pinned by hand at Jacobian/Solution.lean lines 90–92, Jacobian/Solution.lean lines 127–129 and Jacobian/Solution.lean lines 160–162, which is why [pushforward](#/node/Jacobian.pushforward) is built with the universe-heterogeneous [ULiftContinuousAddMonoidHom''](#/node/ComplexTorus.ULiftContinuousAddMonoidHom'') (Jacobian/ComplexTorus/ULiftTransport.lean lines 429–443).'
quiz:
- q: 'Which way round is the composition law?'
  type: choice
  choices:
  - '`pushforward (g ∘ f) P = pushforward g (pushforward f P)`, covariantly'
  - '`pushforward (g ∘ f) P = pushforward f (pushforward g P)`, contravariantly'
  answer: 0
  explain: 'Jacobian/Solution.lean lines 166–167 state the covariant form; the contravariant one belongs to [pullback](#/node/Jacobian.pullback_comp_apply).'
- q: 'What is the bottom fact the proof reduces to?'
  type: choice
  choices:
  - 'Functoriality of pullback of 1-forms: `(g ∘ f)^* = f^* ∘ g^*` on holomorphic 1-forms'
  - 'Multiplicativity of the degree'
  - 'Discreteness of the period lattice'
  answer: 0
  explain: '`holomorphicTraceCoord_compU` (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 62–71) rewrites with [pullbackFormsBundledLM_comp](#/node/HolomorphicForms.pullbackFormsBundledLM_comp).'
- q: 'Why does the contravariance of pullback-of-forms become covariance here?'
  type: choice
  choices:
  - 'Because the degree is multiplicative'
  - 'Because `pushforward` is built from the matrix *transpose* of the coordinate map, and transposing reverses the order of a product'
  - 'Because the surfaces are compact'
  answer: 1
  explain: '`pushforwardTraceLiftLinearMapU_comp` (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 85–92) uses `LinearMap.toMatrix''_comp` then `Matrix.transpose_mul`, which swaps the factors back.'
---
## Plain English

Let `f : X → Y` and `g : Y → Z` be holomorphic maps of compact Riemann surfaces. This lemma says the [pushforward](#/node/Jacobian.pushforward) of the composite is the composite of the pushforwards: for every `P : Jacobian X`,

  `pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P)`

(Jacobian/Solution.lean lines 166–171).

This is the covariant direction, which is what "pushforward" should do. Note that the underlying construction on 1-forms runs the other way: `pushforward` is, in basis coordinates, the transpose of the pullback map on holomorphic 1-forms, and pullback of forms is contravariant. Transposing a product of matrices reverses the order, which turns contravariance back into covariance.

## Why it matters

Functoriality is one of the structural requirements of the challenge (Jacobian/Challenge.lean lines 123–126). With [the identity law](#/node/Jacobian.pushforward_id_apply) it makes J into a functor on the category of compact Riemann surfaces and holomorphic maps, at the level the specification asks about. A definition that merely produced *some* homomorphism for each `f` would not generally satisfy this.

## How the proof goes

Jacobian/Solution.lean lines 168–171: unfold both sides through the `ULift` wrapper and rewrite with [analyticPushforward_comp_applyU](#/node/TraceDegree.analyticPushforward_comp_applyU) (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 111–122).

That lemma picks a representative `v ∈ ℂ^g` of `P` (`mk_surjective`), uses the descent compatibility [analyticPushforward_mk_spec_rawU](#/node/TraceDegree.analyticPushforward_mk_spec_rawU) three times to reduce everything to representatives, and finishes with [pushforwardTraceLiftLinearMapU_comp](#/node/TraceDegree.pushforwardTraceLiftLinearMapU_comp) (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 85–92). That in turn is [holomorphicTraceCoord_compU](#/node/TraceDegree.holomorphicTraceCoord_compU) (Jacobian/TraceDegree/AnalyticPushforwardFunctorialU.lean lines 62–71), the coordinate form of `(g ∘ f)^* = f^* ∘ g^*` for pullback of 1-forms, plus `LinearMap.toMatrix'_comp` and `Matrix.transpose_mul`.

No branched covers, no ramification, no analysis: once pullback of forms is known to be functorial (which is the chain rule, [pullbackFormsBundledLM_comp](#/node/HolomorphicForms.pullbackFormsBundledLM_comp)), this is linear algebra. The [pullback side](#/node/Jacobian.pullback_comp_apply) is where the expensive argument lives.

## What it does not say

- Not an equality of bundled homomorphisms, only pointwise.
- Nothing about degrees. The multiplicativity `deg (g ∘ f) = deg g · deg f` is not stated anywhere in the public interface.
- No divisor-level or `ofCurve`-level compatibility.
