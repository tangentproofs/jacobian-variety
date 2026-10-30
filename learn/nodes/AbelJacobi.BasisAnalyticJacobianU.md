---
id: AbelJacobi.BasisAnalyticJacobianU
title: The Jacobian, before the universe wrapper
summary: 'The Jacobian carrier is literally the quotient group ℂ^g/Λ, and it lands in the smallest universe, which is exactly why the public Jacobian X needs a ULift.'
review: draft
authors:
- claude
caveats:
- 'This is an `abbrev`, so it is not a new type: it unfolds to `ComplexTorus.quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)`, which in turn unfolds to the Mathlib quotient `V ⧸ Λ.subgroup`.'
- 'Its type is `Type`, not `Type u`, because `Fin g → ℂ` lives in `Type 0` no matter which universe X lives in. The public `Jacobian X` has to be in the same universe as X, hence the `ULift` in Jacobian/Solution.lean lines 74–77.'
- 'The group, topology, Hausdorff and compactness structure all come from the lattice bundle rather than from X. Nothing here depends on X beyond the number g and the subgroup Λ.'
- 'For genus 0 this is the quotient of the zero vector space, that is, a one-point group. The project never claims Abel–Jacobi is injective in that case.'
quiz:
- q: 'What is `BasisAnalyticJacobianU X`?'
  type: choice
  choices:
  - 'The quotient of ℂ^g by the period lattice Λ'
  - 'The space of holomorphic 1-forms on X'
  - 'The quotient of X by an equivalence relation'
  answer: 0
  explain: 'The body at Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 45–46 is `quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)`, and `ComplexTorus.quotient` is `V ⧸ Λ.subgroup` (Jacobian/ComplexTorus/Defs.lean lines 73–74).'
- q: 'Why does the public `Jacobian X` apply `ULift` to this?'
  type: choice
  choices:
  - 'To make it a group'
  - 'To move it into the same universe as X, since this carrier is in `Type 0`'
  - 'To make the quotient Hausdorff'
  answer: 1
  explain: 'The declared type at Jacobian/AbelJacobi/AnalyticOfCurveU.lean lines 45–46 is `Type`. Jacobian/Solution.lean lines 74–77 wrap it in `ULift.{u}` so that `Jacobian (X : Type u) : Type u`.'
- q: 'Where do Hausdorffness and compactness of this quotient come from?'
  type: choice
  choices:
  - 'From compactness of X, transported along Abel–Jacobi'
  - 'From the `isClosed` and compact-covering fields of the lattice bundle'
  - 'They are assumed'
  answer: 1
  explain: 'The instances at Jacobian/ComplexTorus/Defs.lean lines 82–121 derive `T2Space` from `isClosed` and `CompactSpace` from the compact covering set of the lattice.'
- q: 'If the genus of X is 0, what is this type?'
  type: choice
  choices:
  - 'A one-point group'
  - 'ℂ'
  - 'Empty'
  answer: 0
  explain: '`Fin 0 → ℂ` is the zero vector space, so the quotient has exactly one element. This is consistent with `ofCurve_inj` in Jacobian/Solution.lean lines 117–120 requiring `0 < genus X`.'
---
## Plain English

This is the Jacobian itself, in the form the analytic work uses. It is the quotient of ℂ^g by the [period lattice](#/node/Periods.periodFullComplexLatticeU), where g is the genus (`Jacobian/AbelJacobi/AnalyticOfCurveU.lean` lines 40–46). Nothing is dressed up: [ComplexTorus.quotient](#/node/ComplexTorus.quotient) is Mathlib's quotient of an additive group by a subgroup, with the quotient topology.

All the structure you want on a Jacobian is already available on this type, and all of it comes from the lattice rather than from X. The quotient is an abelian group and a topological group for free. It is Hausdorff because Λ is closed, and compact because Λ has a compact set whose translates cover ℂ^g (`Jacobian/ComplexTorus/Defs.lean` lines 82–121). The charts, the complex-manifold structure and the Lie-group structure are built in the `Jacobian/ComplexTorus/` layer from the small balls on which the projection ℂ^g → ℂ^g/Λ is injective, which is where discreteness of Λ is needed.

## Why there are two Jacobians in the code

The letter U in the name means "universe-polymorphic in X", but the carrier itself is not. `Fin g → ℂ` lives in `Type 0` whatever universe X lives in, so this quotient is a `Type 0` as well. The challenge specification demands `Jacobian (X : Type u) : Type u`. The fix is a `ULift`: the public `Jacobian X` of `Jacobian/Solution.lean` lines 72–77 is this type lifted into X's universe, and the manifold structure is transported along the obvious bijection in `Jacobian/ComplexTorus/ULiftTransport.lean`.

So when reading the public theorems, treat `Jacobian X` and this type as the same object with a relabelling applied. The map [ofCurve](#/node/Jacobian.ofCurve) is [analyticOfCurveU](#/node/AbelJacobi.analyticOfCurveU) followed by that relabelling.
