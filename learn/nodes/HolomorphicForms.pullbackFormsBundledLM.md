---
id: HolomorphicForms.pullbackFormsBundledLM
title: Pullback of forms is linear
summary: 'Linearity of f* needs no analysis: it reduces to the fact that composing with a fixed derivative is additive and commutes with scalars, checked pointwise in the cotangent fibre.'
review: draft
authors:
- claude
caveats:
- 'This declaration takes `X` and `Y` as *explicit* arguments, unlike its neighbours in the file. Call sites therefore read `pullbackFormsBundledLM X Y f hf`, which is why the argument order looks redundant.'
- 'The two proofs are pointwise. They apply `ContMDiffSection.coe_inj` to reduce equality of forms to equality of their underlying functions, then unfold `pullbackFormsFunFiber` and finish with `ContinuousLinearMap.add_comp` and `ContinuousLinearMap.smul_comp`. No smoothness or holomorphicity is used in either proof; `hf` appears only because it is needed to form the output.'
- 'The module header of `Jacobian/HolomorphicForms/PullbackBundled.lean` lines 23–29 still describes this layer as `opaque` with a characterising axiom. That is out of date: this is a concrete `noncomputable def`, and `pullbackFormsBundledLM_apply_fun` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 174–177) is proved by `rfl`.'
quiz:
- q: 'What does this declaration add to `pullbackFormsBundled`?'
  type: choice
  choices:
  - 'Proofs that f* is additive and commutes with scalar multiplication'
  - 'A proof that f* is injective'
  - 'Continuity of f*'
  answer: 0
  explain: 'The fields are `map_add''` and `map_smul''` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 153–171); the output type is `→ₗ[ℂ]`.'
- q: 'Which direction is this linear map?'
  type: choice
  choices:
  - '`HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y`'
  - '`HolomorphicOneForm ℂ Y →ₗ[ℂ] HolomorphicOneForm ℂ X`'
  - 'It is a linear isomorphism'
  answer: 1
  explain: 'Pullback is contravariant: forms on the target become forms on the source (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 150–151).'
- q: 'What does the linearity proof actually rely on?'
  type: choice
  choices:
  - 'Cauchy''s integral theorem'
  - 'Additivity of composition with a fixed continuous linear map, checked in each cotangent fibre'
  - 'Finite-dimensionality of the space of forms'
  answer: 1
  explain: '`ContinuousLinearMap.add_comp` and `ContinuousLinearMap.smul_comp` are the final steps of the two field proofs.'
- q: 'What is the smoothness hypothesis `hf` used for in the two linearity proofs?'
  type: choice
  choices:
  - 'Nothing; it is needed only to form the output form, and neither proof uses it'
  - 'To show the sums of the pulled-back forms are again holomorphic'
  - 'To rule out branch points'
  answer: 0
  explain: 'Both field proofs reduce to equality of the underlying functions via `ContMDiffSection.coe_inj` and finish with `ContinuousLinearMap.add_comp` / `smul_comp` (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 153–171); `hf` only enters through `pullbackFormsBundled`.'
---
## Plain English

[pullbackFormsBundled](#/node/HolomorphicForms.pullbackFormsBundled) takes one form η on Y and returns the form f\*η on X. `pullbackFormsBundledLM X Y f hf` says that this operation is ℂ-linear in η (`Jacobian/HolomorphicForms/PullbackBundled.lean` lines 145–171):

```
f* : H⁰(Y, Ω¹) →ₗ[ℂ] H⁰(X, Ω¹)
```

Both proofs are three lines of unfolding plus one lemma. To show f\*(η + ζ) = f\*η + f\*ζ you check it at each point x of X. There, both sides are built from the same derivative `df_x`, and

```
(η_{f(x)} + ζ_{f(x)}) ∘ df_x = η_{f(x)} ∘ df_x + ζ_{f(x)} ∘ df_x
```

which is `ContinuousLinearMap.add_comp`. Scalars are the same story with `smul_comp`. The only fiddly part is pushing the addition on forms (addition of smooth sections) down to addition of their values, which is what the `ContMDiffSection.coe_add` steps do.

## Why it is defined this way

The Jacobian pushforward J(X) → J(Y) is, classically, the dual of f\* : H⁰(Y, Ω¹) → H⁰(X, Ω¹). To dualise you need an actual linear map, not just a function on forms, and you need it as a bundled `→ₗ[ℂ]` so that `LinearMap.toMatrix'` can be applied after conjugating by a basis. That is the whole reason this wrapper exists.

Note the direction. Pullback of forms goes Y → X. Transposing it gives a map X → Y on the dual spaces, hence on Jacobians, and that is the *pushforward*. The naming in the layer above reflects the mathematics but not the word: [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU) is called a "trace coordinate" map and is in fact this pullback written in coordinates.

## How it is used

Three ways. It is conjugated by the chosen bases to give [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU), whose transpose becomes the Jacobian pushforward. It appears in the change-of-variables statement `∫_{f∘γ} η = ∫_γ f*η` that proves the pushforward preserves periods (`Jacobian/TraceDegree/AnalyticPushforwardU.lean` lines 55–86). And the functoriality lemmas [pullbackFormsBundledLM_id](#/node/HolomorphicForms.pullbackFormsBundledLM_id) and [pullbackFormsBundledLM_comp](#/node/HolomorphicForms.pullbackFormsBundledLM_comp) make it a contravariant functor, which is what makes the Jacobian pushforward functorial.
