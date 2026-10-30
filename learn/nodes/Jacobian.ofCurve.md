---
id: Jacobian.ofCurve
title: Abel–Jacobi, the public version
summary: 'The declaration the challenge asks for is just a universe relabelling of the analytic Abel–Jacobi map, and its injectivity for positive genus is what rules out a fake one-point Jacobian.'
review: draft
authors:
- claude
caveats:
- 'The body is `ULift.up` applied to `analyticOfCurveU`, so all the mathematics is in that definition. `ULift.up` is a bijection, which is why injectivity transfers by `ULift.up_injective` (Jacobian/Solution.lean lines 117–120).'
- 'The base point P is an argument. The map is not canonical, and no theorem relates the maps for two different base points.'
- '`ofCurve` is not a group homomorphism and is not stated to be one. X is not a group.'
- 'The injectivity theorem assumes `0 < genus X`. For genus 0 it is false: the Jacobian is a one-point group, so the map is constant.'
- 'Nothing here claims surjectivity, the divisor form of Abel theorem, Jacobi inversion, or that the Jacobian is an abelian variety. The project proves none of those.'
quiz:
- q: 'What is the body of `Jacobian.ofCurve P`?'
  type: choice
  choices:
  - '`fun Q => ULift.up (analyticOfCurveU X P Q)`'
  - 'A fresh definition independent of the analytic layer'
  - 'The zero map'
  answer: 0
  explain: 'Jacobian/Solution.lean lines 103–105 give exactly that body, where `analyticOfCurveU` is the analytic Abel–Jacobi map.'
- q: 'Which public theorem is the anti-hack check on the Jacobian, and what does it need?'
  type: choice
  choices:
  - '`ofCurve_self`, needing nothing'
  - '`ofCurve_inj`, needing `0 < genus X`'
  - '`ofCurve_contMDiff`, needing compactness'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 117–120 prove injectivity under `0 < genus X`. An injective map from a positive-genus surface forces the Jacobian to be big, which a definition like `Jacobian X := PUnit` could not satisfy.'
- q: 'What does `ofCurve_self` say?'
  type: choice
  choices:
  - 'That the base point maps to the zero element of the Jacobian'
  - 'That `ofCurve` is injective at the base point'
  - 'That the integral from P to P is literally the zero vector of ℂ^g'
  answer: 0
  explain: 'Jacobian/Solution.lean lines 113–115 prove `ofCurve P P = 0`, by rewriting with `analyticOfCurve_selfU`. The underlying vector is only a period, not necessarily zero.'
- q: 'What smoothness is proved for `ofCurve`?'
  type: choice
  choices:
  - 'Continuity only'
  - 'Holomorphy, as a map of complex manifolds into ℂ^g/Λ'
  - 'Real smoothness but not holomorphy'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 107–111 give `ContMDiff` at level ω, which is the analytic level in `WithTop ℕ∞`, between X and the Jacobian modelled on `Fin (genus X) → ℂ`.'
- q: 'Why is `ULift` involved at all?'
  type: choice
  choices:
  - 'To get a group structure on the Jacobian'
  - 'Because the spec demands `Jacobian (X : Type u) : Type u` while ℂ^g/Λ lives in `Type 0`'
  - 'To make the quotient compact'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 74–77 define `Jacobian X` as `ULift.{u}` of the quotient, and the manifold structure is transported along the lift in Jacobian/ComplexTorus/ULiftTransport.lean.'
---
## Plain English

This is the declaration the challenge specification asks for: given a compact Riemann surface X and a base point P, a map from X to [its Jacobian](#/node/Jacobian). The body is one line (`Jacobian/Solution.lean` lines 103–105): take the [analytic Abel–Jacobi map](#/node/AbelJacobi.analyticOfCurveU) and apply `ULift.up`.

The `ULift` is pure bookkeeping. The analytic Jacobian carrier ℂ^g/Λ lives in the smallest type universe, while the specification requires `Jacobian X` to live in the same universe as X, so the quotient gets relabelled (Jacobian/Solution.lean lines 74–77). Because `ULift.up` is a bijection, every property passes back and forth unchanged.

Three public theorems accompany it:

- `ofCurve_contMDiff` (Jacobian/Solution.lean lines 107–111): the map is holomorphic.
- `ofCurve_self` (Jacobian/Solution.lean lines 113–115): the base point maps to 0. Note it is the class that vanishes; the underlying integral around the chosen closed chain is a period, not necessarily zero.
- `ofCurve_inj` (Jacobian/Solution.lean lines 117–120): if the genus is positive, the map is injective.

## What the injectivity theorem is for

`ofCurve_inj` is one of the challenge's four anti-hack checks. Without it, somebody could set `Jacobian X := PUnit`, give it the obvious group, topology and manifold structure, and satisfy every other requirement. An injective map from a positive-genus surface makes that impossible, because the target has to be at least as big as X.

Here it is proved for real. The route is the two-point form of Abel theorem (`Jacobian/AbelJacobi/AnalyticOfCurveInjectiveU.lean` lines 31–48): if the integrals to Q₁ and Q₂ differ by a period, then there is a chain between them with zero integrals against every holomorphic form; Hodge theory turns that into a meromorphic function with a single simple pole; such a function is a degree-one map to the Riemann sphere, so X would be a sphere and have genus 0, contradicting the hypothesis.

Which also explains the hypothesis. For genus 0 the Jacobian is a single point and `ofCurve` is constant, so injectivity is simply false there, and the challenge does not ask for it.
