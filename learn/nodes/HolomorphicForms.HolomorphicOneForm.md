---
id: HolomorphicForms.HolomorphicOneForm
title: Holomorphic 1-forms
summary: The whole space of holomorphic 1-forms is a single `abbrev`, because "holomorphic" is spelled as Mathlib's top smoothness level ⊤ = ω, which over ℂ means complex-analytic.
review: draft
authors:
- claude
caveats:
- 'An element is a bundled section: a structure carrying a function `x ↦ ω x` together with a proof that it is `ContMDiff` of order ⊤. It is not a quotient, and no chart-by-chart cocycle condition is written by hand; chart compatibility comes from the vector-bundle structure on [CotangentSpace](#/node/HolomorphicForms.CotangentSpace).'
- 'The smoothness exponent is `(⊤ : WithTop ℕ∞)`, which is Mathlib''s `ω` (analytic), the top of the scale above `∞`. Over the field ℂ, `ContDiff ℂ ω` is complex analyticity, so this really is holomorphy and not merely smoothness. The same `⊤` appears in the `IsManifold` hypothesis, so X is required to be a complex-analytic manifold.'
- 'The definition is stated for an arbitrary complex model space E, not only E = ℂ. For a general E it is the space of holomorphic sections of the ℂ-linear cotangent bundle, that is, holomorphic (1,0)-forms; the Riemann surface case is E = ℂ.'
- 'Nothing here makes the space finite-dimensional, and nothing here mentions compactness. Finiteness is a separate theorem, packaged as [FiniteDimensionalHolomorphicOneForms](#/node/HolomorphicForms.FiniteDimensionalHolomorphicOneForms).'
quiz:
- q: What is an element of `HolomorphicOneForm ℂ X`?
  type: choice
  choices:
  - An analytic section of the cotangent bundle of X, bundled with its own analyticity proof
  - A holomorphic function on X
  - An equivalence class of chart coefficient families
  answer: 0
  explain: The body is a `ContMDiffSection` of order ⊤ of `CotangentSpace E X` (Jacobian/HolomorphicForms/Defs.lean lines 23–29); `ContMDiffSection` bundles the section with its regularity proof.
- q: 'What does the smoothness exponent `(⊤ : WithTop ℕ∞)` mean here?'
  type: choice
  choices:
  - Analytic, Mathlib's `ω`, the level above `∞`, which over ℂ means complex-analytic
  - Infinitely differentiable but possibly not analytic
  - Continuous
  answer: 0
  explain: 'In the pinned Mathlib the smoothness scale is `WithTop ℕ∞` with `∞ = (⊤ : ℕ∞)` and `ω = (⊤ : WithTop ℕ∞)`; `ContDiff ℂ ω` is complex analyticity. This is what earns the word "holomorphic" in the name.'
- q: Where do the addition and the ℂ-scalar multiplication on the space of forms come from?
  type: choice
  choices:
  - They are inherited from Mathlib's `ContMDiffSection`, with nothing to prove
  - They are defined by hand later in the file
  - They only exist after the finiteness theorem is proved
  answer: 0
  explain: The two sanity `example`s at Jacobian/HolomorphicForms/Defs.lean lines 31–45 obtain `AddCommGroup` and `Module ℂ` by `inferInstance`.
- q: What evidence in the project shows this type really is "a(z) dz with a holomorphic"?
  type: choice
  choices:
  - '`chartForm` reads a form in a chart and `chartForm_contDiffOn` proves the reading is analytic on the chart target'
  - The docstring says so
  - The genus is finite
  answer: 0
  explain: '[chartForm](#/node/Periods.chartForm) is defined at Jacobian/Periods/ChartChain.lean lines 41–43 and [chartForm_contDiffOn](#/node/Periods.chartForm_contDiffOn) at Jacobian/Periods/ChartChain.lean lines 45–47; [chartCoeff](#/node/HolomorphicForms.chartCoeff) then evaluates the reading at 1 to get the coefficient a.'
- q: Does this definition assume X is compact?
  type: choice
  choices:
  - No, only that X is a ℂ-charted analytic manifold modeled on E
  - Yes, `CompactSpace X` is a hypothesis
  - Yes, compactness is hidden in `ContMDiffSection`
  answer: 0
  explain: The binders at Jacobian/HolomorphicForms/Defs.lean lines 23–27 ask only for `TopologicalSpace X`, `ChartedSpace E X` and `IsManifold (modelWithCornersSelf ℂ E) ⊤ X`.
---
## Plain English

This is the object the whole project is built on. The genus is its dimension, and the Jacobian is built out of integrals of its elements.

A holomorphic 1-form is the thing you integrate along a path on a Riemann surface. Classically you write it as `ω = a(z) dz` in each chart, with `a` holomorphic, and you require the coefficients in overlapping charts to agree after the chain rule. The Lean definition says the same thing in a more structural way:

```
HolomorphicOneForm E X = Cₛ^⊤⟮𝓘(ℂ, E); CotangentModelFiber E, CotangentSpace E X⟯
```

Read right to left: [CotangentSpace](#/node/HolomorphicForms.CotangentSpace) is the cotangent space at each point, [CotangentModelFiber](#/node/HolomorphicForms.CotangentModelFiber) is the model fiber they are trivialised onto, and `Cₛ^⊤⟮…⟯` is Mathlib's notation for sections of that bundle which are `ContMDiff` of order ⊤. So an element is a choice of cotangent vector at every point of X, varying analytically.

Defined at Jacobian/HolomorphicForms/Defs.lean lines 23–29.

## Where the word "holomorphic" comes from

Nothing in the name is doing the work; the exponent is. Mathlib's regularity scale is `WithTop ℕ∞`: natural numbers, then `∞`, then a top element `ω`. Here the exponent is `(⊤ : WithTop ℕ∞)`, which is that top element. Over the complex field, `ContDiff ℂ ω` is exactly complex analyticity. So an element of this type is an analytic, hence holomorphic, section. The same `⊤` sits in the `IsManifold` hypothesis, so X itself is a complex-analytic manifold.

The classical chart picture is recovered, not assumed. [chartForm](#/node/Periods.chartForm) (Jacobian/Periods/ChartChain.lean lines 41–43) pulls a form back through a chart to a map `ℂ → (ℂ →L[ℂ] ℂ)`, [chartForm_contDiffOn](#/node/Periods.chartForm_contDiffOn) (Jacobian/Periods/ChartChain.lean lines 45–47) proves that reading is analytic on the chart target, and [chartCoeff](#/node/HolomorphicForms.chartCoeff) (Jacobian/HolomorphicForms/Finiteness.lean lines 42–44) evaluates it at 1 to get the single complex coefficient `a`. That is `ω = a(z) dz` with `a` holomorphic.

## How it is used

Because the declaration is an `abbrev` over `ContMDiffSection`, the algebra is free: the two `example`s at Jacobian/HolomorphicForms/Defs.lean lines 31–45 confirm `AddCommGroup` and `Module ℂ` are found by `inferInstance`. That matters, because [genus](#/node/genus) is the ℂ-dimension of this space and the period lattice is built from integrals of a basis of it.
