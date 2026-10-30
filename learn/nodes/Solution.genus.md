---
id: Solution.genus
title: The genus, as the solution defines it
summary: The genus is the dimension of the space of holomorphic 1-forms, spelled out as `Module.finrank` on purpose so that the number does not depend on the finiteness proof.
review: draft
authors:
- claude
caveats:
- 'The body does not use any of the hypotheses. `T2Space`, `CompactSpace`, `ConnectedSpace` and the manifold structure sit in the signature because the public spec and the theorems need them; the number itself is just `Module.finrank ℂ (HolomorphicOneForm ℂ X)`.'
- 'It deliberately does not call [analyticGenus](#/node/HolomorphicForms.analyticGenus), even though the two are definitionally equal. Going through `analyticGenus` would put the `[FiniteDimensionalHolomorphicOneForms ℂ X]` instance into the definition; inlining `Module.finrank` keeps the value independent of it. The docstring at Jacobian/Solution.lean lines 39–44 states this reasoning.'
- 'This is the analytic genus. It is not defined topologically, and the only link to topology that the project proves is at zero: [genus_eq_zero_iff_homeo](#/node/Solution.genus_eq_zero_iff_homeo) gives genus 0 iff X is homeomorphic to the round 2-sphere in ℝ³. That is a homeomorphism, not a biholomorphism to ℙ¹, and nothing is claimed for genus > 0.'
- '`Module.finrank` would return 0 for an infinite-dimensional space, so this number is only the genus because finite-dimensionality is proved separately for compact surfaces; see [FiniteDimensionalHolomorphicOneForms](#/node/HolomorphicForms.FiniteDimensionalHolomorphicOneForms).'
quiz:
- q: What is `Solution.genus X`?
  type: choice
  choices:
  - '`Module.finrank ℂ (HolomorphicOneForm ℂ X)`, the ℂ-dimension of the space of holomorphic 1-forms'
  - The number of handles of X
  - Half the rank of H₁(X, ℤ)
  answer: 0
  explain: The body at Jacobian/Solution.lean lines 45–47 is exactly that `finrank`.
- q: Why does the definition write `Module.finrank` instead of calling `analyticGenus ℂ X`?
  type: choice
  choices:
  - So the value does not depend on the finite-dimensionality instance, which `analyticGenus` takes as an argument
  - Because `analyticGenus` computes a different number
  - Because `analyticGenus` is not imported
  answer: 0
  explain: The docstring at Jacobian/Solution.lean lines 39–44 says the value is stated directly "so that the *value* does not depend on the finiteness proof"; the two expressions are definitionally equal.
- q: Which hypotheses in the signature does the body actually use?
  type: choice
  choices:
  - Only `ChartedSpace ℂ X` and `IsManifold 𝓘(ℂ) ω X`, which are needed for `HolomorphicOneForm ℂ X` to typecheck
  - All of them
  - None of them
  answer: 0
  explain: '`HolomorphicOneForm ℂ X` (Jacobian/HolomorphicForms/Defs.lean lines 23–29) needs the charted-space and manifold instances; `T2Space`, `CompactSpace` and `ConnectedSpace` are inert in the body at Jacobian/Solution.lean lines 45–47.'
- q: Does this definition on its own rule out the hack answer "genus X = 0 for every X"?
  type: choice
  choices:
  - No; what rules it out is the separate theorem that genus 0 forces X to be homeomorphic to a sphere
  - Yes, because `finrank` is always positive
  - Yes, because X is connected
  answer: 0
  explain: '[genus_eq_zero_iff_homeo](#/node/Solution.genus_eq_zero_iff_homeo), proved at Jacobian/Solution.lean lines 49–53 from `analyticGenus_eq_zero_iff_homeomorphic_sphere`, is the anti-hack constraint; the definition by itself just names a number.'
---
## Plain English

```
Solution.genus X = Module.finrank ℂ (HolomorphicOneForm ℂ X)
```

Count the independent holomorphic 1-forms on X. That count is the genus. Defined at Jacobian/Solution.lean lines 45–47.

This is the project's answer to the `genus` stub in the frozen challenge file. It is an analytic definition: no handles, no triangulation, no homology. Classically it agrees with the number of handles, but the project proves the two agree only at zero.

The hypotheses `[T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` make X a compact Riemann surface, and they are there because the public specification demands that exact signature. Only the last two are used in the body, to make `HolomorphicOneForm ℂ X` meaningful at all.

## Why it is written this way

There are two equal ways to write this number, and the file picks the one with fewer dependencies. [analyticGenus](#/node/HolomorphicForms.analyticGenus) is the same `finrank`, but it takes `[FiniteDimensionalHolomorphicOneForms ℂ X]` as an instance argument. Writing the `finrank` out by hand means the *value* of `genus` mentions nothing but the space of forms, and the finiteness theorem is used only where a basis is actually needed. The docstring at Jacobian/Solution.lean lines 39–44 spells this out, and notes that the `_frontier` suffix on the finiteness theorem's name is only historical — the theorem is proved.

Just above this definition, Jacobian/Solution.lean lines 34–37 registers the global instance that discharges finite-dimensionality for every compact connected Riemann surface, built from the Montel–Riesz proof. So a basis of the right size is available whenever downstream work wants one.

## What keeps it honest

A definition can be gamed; `genus X := 0` would compile. The constraint comes immediately after: [genus_eq_zero_iff_homeo](#/node/Solution.genus_eq_zero_iff_homeo) at Jacobian/Solution.lean lines 49–53 proves that `genus X = 0` holds exactly when X is homeomorphic to the unit sphere in ℝ³. A constant-zero genus would make every compact Riemann surface a sphere, which is false.

What the project does *not* prove is a link between this number and the topological genus for positive genus. Read "genus" on this site as "dimension of the space of holomorphic 1-forms" unless a node says otherwise.
