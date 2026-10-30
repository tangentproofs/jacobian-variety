---
id: Jacobian.ofCurve_inj
title: A point is determined by its integrals
summary: 'Once the genus is positive, a point of the surface is pinned down by the integrals of holomorphic 1-forms from a base point to it, taken modulo periods.'
review: draft
authors:
- claude
caveats:
- 'Only one direction is proved. The statement is `0 < genus X → Function.Injective (ofCurve P)`. The challenge *docstring* says "injective iff the genus is positive" (Jacobian/Challenge.lean line 25), but no converse is stated or proved anywhere.'
- 'Injective, not an embedding. Nothing about immersion, closed image, properness, or the differential being nonzero is proved.'
- 'The base point P is an argument, and the map depends on it. No theorem compares `ofCurve P` with `ofCurve P''`.'
- 'This is the two-point separation form of Abel''s theorem only. There is no divisor group, no Pic⁰, no Jacobi inversion (surjectivity), and no Abel criterion for principal divisors in this repository.'
- 'The lemma does not exhibit any X with `0 < genus X`. The only concrete compact Riemann surface built in the repository is ℂ̂ (Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean line 166), whose genus is proved to be 0 (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 629–633), so the hypothesis is never discharged on a concrete example.'
quiz:
- q: 'What is the exact hypothesis under which injectivity is proved?'
  type: choice
  choices:
  - 'None; `ofCurve P` is always injective'
  - '`0 < genus X`'
  - '`genus X = 1`'
  answer: 1
  explain: 'Jacobian/Solution.lean line 117 reads `lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P)`.'
- q: 'Why is the hypothesis necessary?'
  type: choice
  choices:
  - 'For genus 0 the Jacobian is a single point, so `ofCurve P` is constant and cannot be injective on a surface with more than one point'
  - 'Because the integrals diverge in genus 0'
  - 'It is only a technical convenience and could be removed'
  answer: 0
  explain: 'With `genus X = 0` the carrier is `Fin 0 → ℂ` modulo its lattice, a one-point group, so every map into it is constant. The proof also runs the other way: the whole argument derives genus 0 from a failure of injectivity.'
- q: 'What is the mathematical content of the proof?'
  type: choice
  choices:
  - 'The period lattice is discrete'
  - 'Abel''s theorem in two-point form: if two chains from P have period vectors differing by a period and the endpoints differ, X is a sphere'
  - 'The Abel–Jacobi map is holomorphic'
  answer: 1
  explain: '`Surface.FChain.eq_of_periodVector_sub_mem` (Jacobian/Surface/Abel.lean lines 297–321) is the engine, reached through `AbelJacobi.pathIntegralFunctional_separates_pointsU`.'
- q: 'How does the proof reach a contradiction from Q₁ ≠ Q₂?'
  type: choice
  choices:
  - 'It builds a formal chain whose boundary is Q₂ − Q₁ with all integrals zero, concludes X is homeomorphic to the sphere, hence every holomorphic 1-form vanishes, hence the genus is 0'
  - 'It uses a dimension count on H₁(X, ℤ)'
  - 'It invokes Riemann–Roch'
  answer: 0
  explain: 'Jacobian/Surface/Abel.lean lines 297–321: `homeomorph_of_null_chain`, then `holomorphicOneForm_eq_zero_of_homeomorph_sphere`, then `analyticGenus_eq_zero_iff_subsingleton`, then `omega` against `0 < genus X`.'
- q: 'Does the lemma say the Abel–Jacobi map is an embedding of X into its Jacobian?'
  type: choice
  choices:
  - 'Yes, injective plus holomorphic gives an embedding'
  - 'No. Only injectivity is stated; `ofCurve_contMDiff` separately gives holomorphy, and no immersion or closed-image claim is made'
  - 'Yes, because X is compact'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 117–120 prove `Function.Injective` and nothing more. The audit lists "ofCurve is an embedding" on its do-not-say list.'
---
## Plain English

Fix a compact Riemann surface X and a base point P. The [Abel–Jacobi map](#/node/Jacobian.ofCurve) sends a point Q to the vector of integrals

  (∫ from P to Q of ω₁, …, ∫ from P to Q of ω_g)

for a chosen basis ω₁, …, ω_g of the holomorphic 1-forms, taken modulo the [period lattice](#/node/Periods.periodFullComplexLatticeU). This lemma says: if `0 < genus X`, that assignment is injective. Two different points of X always have different integral vectors, even after reducing modulo periods.

That is a strong statement. The surface is a two-real-dimensional object and the integrals are a finite list of complex numbers computed along a path; the lemma says they already contain the point.

The Lean statement (Jacobian/Solution.lean lines 117–120) is exactly `(P : X) (h : 0 < genus X) : Function.Injective (ofCurve P)`. The genus hypothesis is not decoration. When `genus X = 0` the Jacobian is a one-point group and `ofCurve P` is constant, so the statement would be false.

## Why it matters

This is the anti-hack lemma for the Jacobian itself. The specification says so: "this is the lemma which stops the hack answer `J(X)=0` for all `X`" (Jacobian/Challenge.lean lines 97–98). Define [Jacobian](#/node/Jacobian) X to be `PUnit`, give it the obvious group, topology and manifold structures, let `ofCurve` be constant, and every other requirement of the challenge is satisfiable. Injectivity on a positive-genus surface destroys that: the target must be at least as large as X.

Note what carries the weight. The theorem constrains the *definition* of the Jacobian. Here the definition is a genuine complex torus ℂ^g/Λ and the injectivity is a real theorem about integrals, not an artifact.

## How the proof goes

The public proof is four lines. Strip the universe wrapper with `ULift.up_injective`, rewrite `genus` to the analytic genus, and apply [analyticOfCurve_injectiveU](#/node/AbelJacobi.analyticOfCurve_injectiveU) (Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean lines 55–60). That lemma turns equality of two classes in the quotient into membership of a difference in the [period subgroup](#/node/Periods.genuinePeriodSubgroup) (`QuotientAddGroup.eq.mp`) and hands it to [pathIntegralFunctional_separates_pointsU](#/node/AbelJacobi.pathIntegralFunctional_separates_pointsU) (Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean lines 41–48).

The content is [eq_of_periodVector_sub_mem](#/node/Surface.FChain.eq_of_periodVector_sub_mem) in Jacobian/Surface/Abel.lean lines 297–321, Abel's theorem in two-point form, proved in this repository. It argues by contradiction. Suppose Q₁ ≠ Q₂ and the two [period vectors](#/node/Periods.periodVector) differ by a period. Write the period as the integral over a closed formal chain Γ, and form the combination `C = chain to Q₂ − chain to Q₁ − Γ`. By construction C has boundary Q₂ − Q₁ and integrates to zero against every basis 1-form, hence (by linearity, [integral_eq_zero_of_basis](#/node/Surface.FChain.integral_eq_zero_of_basis), Jacobian/Surface/Abel.lean lines 289–293) against every holomorphic 1-form. A chain with those two properties feeds [homeomorph_of_null_chain](#/node/Surface.FChain.homeomorph_of_null_chain) (Jacobian/Surface/Abel.lean lines 241–255), whose output is a homeomorphism X ≃ₜ ℂ̂ built the same way as in [the genus-zero classification](#/node/genus_eq_zero_iff_homeo): the vanishing integrals make a ∂̄ problem solvable, producing a function with a single simple pole. Compose with ℂ̂ ≃ₜ S², conclude via [holomorphicOneForm_eq_zero_of_homeomorph_sphere](#/node/Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere) that every holomorphic 1-form on X vanishes, so `genus X = 0`, contradicting `0 < genus X` by `omega`.

So the two headline theorems of the project share an engine. Both go through "a surface with enough vanishing turns out to be a sphere".

Nothing in this chain is admitted. `ref/axiom-audit.md` reports three remaining `sorry`s in the tree, all in `Jacobian/Periods/Hurewicz.lean` and unreachable from the public API, with every public declaration printing the axioms `propext`, `Classical.choice`, `Quot.sound`, and a strict comparator run on 2026-10-28. That is the repository's record; this page does not re-verify it.

## What it does not say

- Not "injective **iff** the genus is positive". Only the forward direction exists in Lean; the challenge's own docstring (Jacobian/Challenge.lean line 25) is looser than its lemma.
- Not an embedding, immersion, or closed immersion. Injectivity alone.
- Not the Abel–Jacobi theorem in divisor form. There is no divisor group, no degree-zero divisor class group, no surjectivity (Jacobi inversion), and no criterion for a divisor to be principal.
- Nothing about the Jacobian being an abelian variety or projective. What is proved about it is: compact Hausdorff complex torus, abelian Lie group, complex dimension `genus X`.
- No compatibility between `ofCurve` and [pushforward](#/node/Jacobian.pushforward) or [pullback](#/node/Jacobian.pullback). No lemma of the shape `pushforward f (ofCurve P Q) = ofCurve (f P) (f Q)` exists.
