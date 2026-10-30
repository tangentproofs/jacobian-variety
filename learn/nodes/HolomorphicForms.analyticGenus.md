---
id: HolomorphicForms.analyticGenus
title: The analytic genus
summary: The genus is defined analytically, as the dimension of the space of holomorphic 1-forms, with no mention of handles, triangulations or topology.
review: draft
authors:
- claude
caveats:
- '`Module.finrank` returns 0 for an infinite-dimensional space. So the number this definition produces is only the genus because finite-dimensionality is separately proved; the `[FiniteDimensionalHolomorphicOneForms E X]` instance argument records the intent but the value does not depend on it.'
- 'This is a definition, not a theorem, and it is not connected to the topological genus here. The only tie to topology in the project is at genus zero, through [genus_eq_zero_iff_homeo](#/node/genus_eq_zero_iff_homeo), which says genus 0 iff X is *homeomorphic* to the round 2-sphere. That is a weaker statement than the classical "biholomorphic to ℙ¹".'
- 'The public [genus](#/node/genus) does not call this declaration. Jacobian/Solution.lean lines 45–47 inlines `Module.finrank ℂ (HolomorphicOneForm ℂ X)` instead, which is definitionally the same thing but keeps the *value* independent of the finiteness instance. The docstring at Jacobian/Solution.lean lines 39–44 says this is deliberate.'
- Nothing in the signature requires X to be compact or connected.
quiz:
- q: What number does `analyticGenus E X` compute?
  type: choice
  choices:
  - The ℂ-dimension of the space of holomorphic 1-forms on X
  - The number of handles of X
  - The rank of the first homology group of X
  answer: 0
  explain: The body is `Module.finrank ℂ (HolomorphicOneForm E X)` at Jacobian/HolomorphicForms/FiniteDimensional.lean lines 27–32.
- q: What does `Module.finrank` return if the space happened to be infinite-dimensional?
  type: choice
  choices:
  - '0'
  - '∞'
  - It would fail to typecheck
  answer: 0
  explain: '`Module.finrank` is Mathlib''s natural-number rank and is 0 when no finite rank exists. This is why finite-dimensionality has to be a real theorem; see [FiniteDimensionalHolomorphicOneForms](#/node/HolomorphicForms.FiniteDimensionalHolomorphicOneForms).'
- q: Why is `[FiniteDimensionalHolomorphicOneForms E X]` in the signature even though `Module.finrank` does not need it?
  type: choice
  choices:
  - To record that the number is only meaningful when the space is finite-dimensional, and to make a basis available downstream
  - Because `Module.finrank` requires it
  - Because it changes the computed value
  answer: 0
  explain: '`analyticGenus_def` at Jacobian/HolomorphicForms/AnalyticGenus.lean lines 23–25 is proved by `rfl`, so the instance does not enter the value; it is there so callers such as [holomorphicOneFormFinBasis](#/node/HolomorphicForms.holomorphicOneFormFinBasis) can get a basis of that size.'
- q: Does `analyticGenus E X = 0` mean the space of forms is empty?
  type: choice
  choices:
  - No, it means the space has only the zero form
  - Yes, there are no forms at all
  - No, it means the space is one-dimensional
  answer: 0
  explain: '`analyticGenus_eq_zero_iff_subsingleton` at Jacobian/HolomorphicForms/AnalyticGenus.lean lines 32–36 shows genus 0 is equivalent to `Subsingleton (HolomorphicOneForm E X)`; a vector space always contains 0.'
---
## Plain English

```
analyticGenus E X = Module.finrank ℂ (HolomorphicOneForm E X)
```

That is the whole definition (Jacobian/HolomorphicForms/FiniteDimensional.lean lines 27–32). Count how many independent holomorphic 1-forms X carries; that number is the genus.

This is the analytic definition, and it is the one the project commits to. The classical topological genus, the number of handles, never appears, and no theorem in the project relates the two numbers except at zero. Classically a torus carries one independent holomorphic 1-form, `dz`, and the sphere carries none but 0; the project computes neither example, but it does prove that genus 0 happens exactly for surfaces homeomorphic to the 2-sphere.

`Module.finrank` is Mathlib's ℕ-valued dimension, so the result is a natural number. It is also 0 on any space with no finite basis, which is why the finiteness theorem matters: without it, `analyticGenus` on a non-compact surface would silently report 0. The instance argument `[FiniteDimensionalHolomorphicOneForms E X]` flags the intended regime, but it does not change the value, as `analyticGenus_def` (Jacobian/HolomorphicForms/AnalyticGenus.lean lines 23–25, proved by `rfl`) makes explicit.

## How it is used

Two places. First, the size of the chosen basis: [holomorphicOneFormFinBasis](#/node/HolomorphicForms.holomorphicOneFormFinBasis) is indexed by `Fin (analyticGenus E X)`, which is how `ℂ^g` gets its g. Second, the genus-zero classification: the small API file proves `analyticGenus E X = 0` is equivalent to the space of forms being a single point (Jacobian/HolomorphicForms/AnalyticGenus.lean lines 32–36), which is the entry point to the proof that genus 0 surfaces are spheres.

The public [genus](#/node/genus) is the same number but is not written through this declaration; see that node for why.
