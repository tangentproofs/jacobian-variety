---
id: TraceDegree.pushforwardTraceLiftCLMU
title: The ambient pushforward, now continuous
summary: 'Continuity costs nothing here: `LinearMap.toContinuousLinearMap` supplies it from finite-dimensionality alone, and it is the only reason this declaration exists.'
review: draft
authors:
- claude
caveats:
- 'No analysis happens in this declaration. `LinearMap.toContinuousLinearMap` is Mathlib''s packaging of automatic continuity for linear maps on finite-dimensional normed spaces; the underlying function is unchanged.'
- 'All upstream caveats carry over, in particular the non-canonical basis of holomorphic 1-forms used by [holomorphicTraceCoordU](#/node/TraceDegree.holomorphicTraceCoordU), and the fact that the map underneath is the chain-rule pullback f* transposed, not a trace.'
- 'The `U` suffix is vestigial: the module docstring names a Type-0 original `pushforwardTraceLiftCLM` in `Jacobian/TraceDegree/PushforwardBasis.lean`, and neither the declaration nor the file exists in the tree.'
quiz:
- q: 'Where does the continuity proof come from?'
  type: choice
  choices:
  - 'From the analytic hypothesis `hf` on f'
  - 'From `LinearMap.toContinuousLinearMap`, i.e. automatic continuity in finite dimensions'
  - 'From compactness of X'
  answer: 1
  explain: 'The body (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 75–80) is a single application of `LinearMap.toContinuousLinearMap`.'
- q: 'Why is the continuous packaging needed?'
  type: choice
  choices:
  - 'Because `ComplexTorus.mapClm` and `mapClm_continuous` take a `→L[ℂ]` argument'
  - 'Because the period lattice is closed'
  - 'Because the Jacobian is Hausdorff'
  answer: 0
  explain: '[analyticPushforwardU](#/node/TraceDegree.analyticPushforwardU) calls both of those with this map as the argument.'
- q: 'What two theorems is this map the subject of, in the file that follows?'
  type: choice
  choices:
  - 'That it is injective, and that it is surjective'
  - 'That it sends the period vector of a chain to the period vector of a pushed-forward chain, and that it preserves the period lattice'
  - 'That it is an isometry, and that it is holomorphic'
  answer: 1
  explain: '`pushforwardTraceLiftCLMU_periodVector` and `pushforwardTraceLift_preserves_latticeU`, `Jacobian/TraceDegree/AnalyticPushforwardU.lean` lines 55–86 and 101–119.'
---
## Plain English

`pushforwardTraceLiftCLMU f hf` is the transposed pullback matrix of [pushforwardTraceLiftLinearMapU](#/node/TraceDegree.pushforwardTraceLiftLinearMapU), retyped as a *continuous* ℂ-linear map `(Fin g_X → ℂ) →L[ℂ] (Fin g_Y → ℂ)` (`Jacobian/TraceDegree/PushforwardTraceLiftU.lean` lines 75–80).

One line, one lemma. Over ℂ in finite dimensions every linear map is continuous, so the proof is handed over by Mathlib.

## Why it is defined this way

The next step is to pass from ℂ^g to the torus ℂ^g / Λ. The descent tool, [mapClm](#/node/ComplexTorus.mapClm), takes a continuous linear map together with a proof that it carries one lattice into the other, and returns a group homomorphism of quotients; [mapClm_continuous](#/node/ComplexTorus.mapClm_continuous) then gives continuity of the quotient map from `f.continuous`. Both need the `→L[ℂ]` form. That is the entire purpose of this declaration.

## How it is used

It is the ambient map in the two theorems that make the pushforward exist. First, `pushforwardTraceLiftCLMU_periodVector` says: if a chain l' in Y satisfies `∫_{l'} η = ∫_l f*η` for every form η on Y, then this map sends the period vector of l to the period vector of l'. Second, `pushforwardTraceLift_preserves_latticeU` combines that with the existence of pushed-forward chains to conclude that the period lattice of X lands inside the period lattice of Y. With that in hand, [analyticPushforwardU](#/node/TraceDegree.analyticPushforwardU) is a one-step descent.
