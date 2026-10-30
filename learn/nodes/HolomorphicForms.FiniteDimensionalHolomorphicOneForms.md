---
id: HolomorphicForms.FiniteDimensionalHolomorphicOneForms
title: Packaging "the space of 1-forms is finite-dimensional"
summary: This is a typeclass holding one proof, so downstream files can take finite-dimensionality as a hypothesis; for a compact Riemann surface it is discharged by a real Montel–Riesz proof, not assumed.
review: draft
authors:
- claude
caveats:
- 'As written, this declaration is a `class`, which means a hypothesis, not a theorem. It mentions no compactness and asserts nothing on its own: `FiniteDimensionalHolomorphicOneForms E X` is a statement about E and X that somebody has to prove.'
- For compact Riemann surfaces it is proved, and registered so that Lean finds it with no user input. Jacobian/HolomorphicForms/Finiteness.lean lines 372–373 makes it an instance for every compact Hausdorff X modelled on ℂ, and Jacobian/Solution.lean lines 34–37 registers the same thing on the public signature through `compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier`. Both reduce to `finiteDimensional_holomorphicOneForm`, the Montel plus Arzelà–Ascoli plus Riesz argument in Jacobian/HolomorphicForms/Finiteness.lean. That proof file contains no `sorry` and takes no typeclass assumptions beyond the manifold structure, compactness and Hausdorffness.
- The suffix `_frontier` and the history paragraph in the docstring at Jacobian/HolomorphicForms/CompactRiemannSurface.lean lines 778–787 record that this statement was once routed through a refuted `StableChartAt` adapter and then stood as a named classical input. In the code as it is now, it is proved. The name is a leftover.
- 'The field name is `finiteDimensional` and it holds `Module.Finite ℂ (HolomorphicOneForm E X)`, which for a ℂ-vector space is the same as finite-dimensionality. The `attribute [instance]` on the field (Jacobian/HolomorphicForms/FiniteDimensional.lean line 21) is what lets Lean use it wherever `FiniteDimensional ℂ (HolomorphicOneForm E X)` is wanted.'
quiz:
- q: Is `FiniteDimensionalHolomorphicOneForms` a theorem?
  type: choice
  choices:
  - No, it is a one-field `Prop`-valued class, so it is a hypothesis you can assume or prove
  - Yes, it proves that holomorphic 1-forms form a finite-dimensional space
  - Yes, but only for compact X
  answer: 0
  explain: '`class FiniteDimensionalHolomorphicOneForms … : Prop where finiteDimensional : Module.Finite ℂ (HolomorphicOneForm E X)` at Jacobian/HolomorphicForms/FiniteDimensional.lean lines 14–19 declares a class; the proof lives elsewhere.'
- q: For a compact connected Riemann surface, is finite-dimensionality assumed or proved in this repository?
  type: choice
  choices:
  - Proved, by a Montel–Riesz argument on a finite cover by chart discs
  - Assumed as an axiom
  - Assumed via a typeclass the reader must supply
  answer: 0
  explain: Jacobian/HolomorphicForms/Finiteness.lean lines 321–324 proves `finiteDimensional_holomorphicOneForm` using Arzelà–Ascoli and Riesz, and Jacobian/HolomorphicForms/Finiteness.lean lines 372–373 turns it into the instance.
- q: Does the class statement itself mention compactness of X?
  type: choice
  choices:
  - No, it only requires X to be a ℂ-charted analytic manifold modeled on E
  - Yes, `CompactSpace X` is one of its binders
  - Yes, compactness is part of the field's type
  answer: 0
  explain: The binders at Jacobian/HolomorphicForms/FiniteDimensional.lean lines 14–17 are `TopologicalSpace X`, `ChartedSpace E X` and `IsManifold (modelWithCornersSelf ℂ E) ⊤ X`. Compactness enters only in the theorem that discharges the class.
- q: What would go wrong if this class were never discharged for compact surfaces?
  type: choice
  choices:
  - '[analyticGenus](#/node/HolomorphicForms.analyticGenus) and the chosen basis would only exist under an unproved hypothesis, so the genus and the period lattice would be conditional'
  - Nothing, since `Module.finrank` is defined anyway
  - The forms would stop being holomorphic
  answer: 0
  explain: '[analyticGenus](#/node/HolomorphicForms.analyticGenus) and [holomorphicOneFormFinBasis](#/node/HolomorphicForms.holomorphicOneFormFinBasis) both take `[FiniteDimensionalHolomorphicOneForms E X]` as an instance argument, so without the instance they cannot be applied.'
---
## Plain English

On a compact Riemann surface the space of holomorphic 1-forms is finite-dimensional, and its dimension is the genus. That fact is a real theorem, not a definition: without it the genus would be the dimension of a possibly infinite-dimensional space, and the Jacobian would have no `ℂ^g` to live in.

This declaration is not that theorem. It is a container for it:

```
class FiniteDimensionalHolomorphicOneForms E X : Prop where
  finiteDimensional : Module.Finite ℂ (HolomorphicOneForm E X)
```

One field, holding the finiteness of [HolomorphicOneForm](#/node/HolomorphicForms.HolomorphicOneForm). Declaring it as a `class` lets later files write `[FiniteDimensionalHolomorphicOneForms E X]` in their signatures and have Lean find the proof automatically, instead of threading it by hand. The `attribute [instance]` on the field (Jacobian/HolomorphicForms/FiniteDimensional.lean line 21) makes the stored proof usable wherever Mathlib wants `FiniteDimensional ℂ (…)`.

Declared at Jacobian/HolomorphicForms/FiniteDimensional.lean lines 14–19.

## Is it assumed or proved?

This is exactly the kind of place where a formalization can smuggle in the hard part, so it is worth following the chain.

At this level of generality, for an arbitrary model space E and an arbitrary ℂ-charted analytic X, it is a hypothesis. Nothing here says X is compact, and for a non-compact surface the statement is false (the plane has infinitely many independent holomorphic 1-forms).

For the surfaces the challenge is about, it is proved. `finiteDimensional_holomorphicOneForm` at Jacobian/HolomorphicForms/Finiteness.lean lines 321–324 proves `FiniteDimensional ℂ (HolomorphicOneForm ℂ X)` for `[T2Space X] [CompactSpace X]` by the classical Montel–Riesz route: cover X by finitely many chart discs, read each form as a holomorphic coefficient on each disc, bound the sup norm on the bigger disc by the sup norm on the smaller one, apply Cauchy estimates and Arzelà–Ascoli to get a totally bounded ball, then conclude by Riesz. That file has no `sorry`, and it closes the class on the spot: the instance at Jacobian/HolomorphicForms/Finiteness.lean lines 372–373 is `⟨finiteDimensional_holomorphicOneForm⟩`. `compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier` (Jacobian/HolomorphicForms/CompactRiemannSurface.lean lines 788–793) is the same wrapper on the public signature, and Jacobian/Solution.lean lines 34–37 registers it there.

Two cosmetic warnings for a reader of the source. The name ends in `_frontier`, and its docstring at Jacobian/HolomorphicForms/CompactRiemannSurface.lean lines 778–787 records that the statement used to be a named classical input routed through an adapter that was later refuted. Neither is true of the code as it now stands.
