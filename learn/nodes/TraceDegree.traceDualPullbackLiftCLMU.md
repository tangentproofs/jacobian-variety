---
id: TraceDegree.traceDualPullbackLiftCLMU
title: The ambient pullback, now continuous
summary: 'Continuity here is free: `LinearMap.toContinuousLinearMap` hands it over because every linear map out of a finite-dimensional space is automatically continuous, and continuity is what lets the map descend to the quotient torus.'
review: draft
authors:
- claude
caveats:
- 'No analysis is done in this declaration. `LinearMap.toContinuousLinearMap` is Mathlib''s packaging of the fact that a linear map on a finite-dimensional normed space over a complete field is continuous; the underlying function is unchanged.'
- 'All upstream caveats carry over: the non-canonical basis of H⁰(X, Ω¹), and the fact that the trace form feeding [traceFormsCoordU](#/node/TraceDegree.traceFormsCoordU) is a `Classical.choose` witness specified only at regular values.'
- 'The `U` suffix is vestigial; the Type-0 original `traceDualPullbackLiftCLM` named in the docstring is not in the tree, and neither is the `Jacobian/TraceDegree/PullbackBasis.lean` that the module docstring points at.'
quiz:
- q: 'What does bundling the map as a continuous linear map buy?'
  type: choice
  choices:
  - 'It makes the map injective'
  - 'It supplies the continuity hypothesis that `ComplexTorus.mapClm` needs to descend the map to the quotient'
  - 'It makes the map holomorphic as a map of manifolds'
  answer: 1
  explain: '[mapClm](#/node/ComplexTorus.mapClm) takes a `→L[ℂ]` argument, and [mapClm_continuous](#/node/ComplexTorus.mapClm_continuous) uses `f.continuous`.'
- q: 'Where does the continuity proof come from?'
  type: choice
  choices:
  - 'From a hand-written estimate on the matrix entries'
  - 'From `LinearMap.toContinuousLinearMap`, i.e. automatic continuity in finite dimensions'
  - 'From the smoothness hypothesis `hf` on the map of surfaces'
  answer: 1
  explain: 'The body in `Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 85–88 is a single application of `LinearMap.toContinuousLinearMap`.'
- q: 'Does the underlying function change when the map is bundled?'
  type: choice
  choices:
  - 'No, it is the same function with a continuity proof attached'
  - 'Yes, it is restricted to a bounded set'
  - 'Yes, it is composed with the quotient map'
  answer: 0
  explain: 'Bundling only attaches the proof; the descent to the torus happens later, in `Jacobian/TraceDegree/AnalyticPullbackU.lean` lines 99–108.'
---
## Plain English

`traceDualPullbackLiftCLMU f hf` is the transposed trace matrix of [traceDualPullbackLiftU](#/node/TraceDegree.traceDualPullbackLiftU), re-typed as a *continuous* ℂ-linear map `(Fin g_Y → ℂ) →L[ℂ] (Fin g_X → ℂ)` (`Jacobian/TraceDegree/PullbackTraceLiftU.lean` lines 85–88).

The body is one call to `LinearMap.toContinuousLinearMap`. Nothing is estimated or proved by hand. In finite dimensions over ℂ every linear map is continuous, and Mathlib already knows that, so the continuity proof is handed over for free.

## Why it is defined this way

The next step is to pass from ℂ^g down to the torus ℂ^g / Λ. The tool for that is [mapClm](#/node/ComplexTorus.mapClm): given a continuous linear map between the ambient spaces that sends one lattice into the other, you get a group homomorphism between the quotients, and [mapClm_continuous](#/node/ComplexTorus.mapClm_continuous) says the quotient map is continuous too. Both of those need the ambient map packaged as `→L[ℂ]`, not just `→ₗ[ℂ]`. That is the only reason this declaration exists.

Continuity matters in the end because the public Jacobian maps are required to be continuous group homomorphisms (`→ₜ+`), and in fact analytic; the analyticity is proved separately in `Jacobian/TraceDegree/AnalyticPullbackContMDiffU.lean`.

## How it is used

It is the ambient map in the two statements that finish the pullback: the lattice-preservation theorem `traceDualPullbackLift_preserves_latticeU` (`Jacobian/TraceDegree/AnalyticPullbackU.lean` lines 64–90) and the descent [analyticPullbackU](#/node/TraceDegree.analyticPullbackU).
