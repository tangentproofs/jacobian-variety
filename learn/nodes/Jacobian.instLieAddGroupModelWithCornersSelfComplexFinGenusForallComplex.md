---
id: Jacobian.instLieAddGroupModelWithCornersSelfComplexFinGenusForallComplex
title: Adding on the Jacobian is holomorphic
summary: Addition and negation on the Jacobian are analytic, not merely smooth, because upstairs on ℂ^g they are analytic and the projection to the quotient is too.
review: draft
authors:
- claude
caveats:
- 'The instance is anonymous in the source — Jacobian/Solution.lean lines 100–101. The id used on this site is the name Lean is expected to generate, not a name written in the file.'
- 'This instance is not listed in `comparator/jacobian.json` and does not occur in any checked statement, so the harness that compares the solution with the frozen spec does not certify it. The proof is real; it is just checked by reading.'
- '`LieAddGroup` in Mathlib extends `ContMDiffAdd`, so the instance body only supplies `contMDiff_neg`; smoothness of addition is registered by the preceding `ContMDiffAdd` instance (Jacobian/ComplexTorus/LieAddGroup.lean lines 17–20, and Jacobian/ComplexTorus/ULiftTransport.lean lines 328–333 for the lifted version).'
- 'The regularity is `ω`, written `(⊤ : WithTop ℕ∞)` in the torus layer: addition and negation are analytic, not merely smooth.'
- 'The classical statement behind this requirement is that a *connected* compact complex Lie group of dimension g is ℂ^g modulo a full lattice. That is background explaining why the specification asks for the instance. It is not proved in this repository, and neither is connectedness of `Jacobian X`: there is no `ConnectedSpace` instance on the quotient anywhere in `Jacobian/`.'
quiz:
- q: Why is addition on the torus analytic?
  type: choice
  choices:
  - In product charts it factors as chart maps, then addition on ℂ^g, then the projection, all three analytic
  - Because the torus is compact
  - Because the lattice is discrete
  answer: 0
  explain: The strategy docstring at Jacobian/ComplexTorus/AddSmooth.lean lines 11–23 lists exactly those three factors and names `contMDiff_mk` for the last.
- q: What does the `LieAddGroup` instance body actually provide?
  type: choice
  choices:
  - Only `contMDiff_neg`, since smoothness of addition comes from the `ContMDiffAdd` instance it extends
  - Both `contMDiff_add` and `contMDiff_neg`
  - The group axioms
  answer: 0
  explain: 'Jacobian/ComplexTorus/LieAddGroup.lean lines 26–29 supply `contMDiff_neg := contMDiff_quotient_neg Λ`, and Jacobian/ComplexTorus/LieAddGroup.lean lines 17–20 register `ContMDiffAdd` separately.'
- q: Which anti-hack role does this instance play in the challenge?
  type: choice
  choices:
  - Together with compactness and the ℂ^g charts it forces torus-like analytic structure on the Jacobian
  - It forces the genus to be positive
  - It forces the Abel–Jacobi map to be injective
  answer: 0
  explain: Jacobian/Challenge.lean line 87 asks for `LieAddGroup … ω (Jacobian X)`, alongside `CompactSpace` at Jacobian/Challenge.lean line 76 and `ChartedSpace (Fin (genus X) → ℂ)` at Jacobian/Challenge.lean line 81.
- q: How is the lifted version obtained?
  type: choice
  choices:
  - Negation on `ULift` factors as up, negate, down, each analytic, so the transported instance follows
  - By reproving everything in the higher universe
  - By an axiom
  answer: 0
  explain: '`complexTorusULift_contMDiff_neg` at Jacobian/ComplexTorus/ULiftTransport.lean lines 344–357 rewrites `fun a => -a` as that three-fold composition and composes the three smoothness facts; the instance at Jacobian/ComplexTorus/ULiftTransport.lean lines 365–370 then supplies `contMDiff_neg`.'
---
## Plain English

A Lie group is a group that is also a manifold, with the group operations smooth. The Jacobian is asked to be one, with analytic operations, modelled on ℂ^g (Jacobian/Challenge.lean lines 86–87).

On a torus this is true for a simple reason: the group law upstairs, on ℂ^g, is addition of vectors, which is as analytic as a map can be, and the projection to the torus is analytic too. So the group law downstairs is analytic wherever it is defined, which is everywhere.

The Lean follows that outline. To check smoothness of addition at a pair of torus points, work in the product of the two charts at those points. There, addition reads as: apply the two chart maps to get vectors in ℂ^g, add them, project back. Three analytic maps composed (Jacobian/ComplexTorus/AddSmooth.lean lines 11–23). Negation is the same argument with one factor.

Mathlib's `LieAddGroup` extends `ContMDiffAdd`, so the project registers smooth addition first and then the Lie group instance carries only negation (Jacobian/ComplexTorus/LieAddGroup.lean lines 17–29). For `Jacobian X` the whole structure is transported across the `ULift` wrapper, where negation factors as unwrap, negate, rewrap (Jacobian/ComplexTorus/ULiftTransport.lean lines 344–370).

## Why the specification insists on it

This instance, with compactness and the ℂ^g charts, is one of the challenge's anti-hack requirements. Consider what a lazy answer would try: define `Jacobian X := PUnit`, or `Jacobian X := ℂ^g`, or some finite group. Each fails one of the demands. `PUnit` fails the injectivity of Abel–Jacobi for positive genus. ℂ^g fails compactness. A finite group fails the charts to ℂ^g once the genus is positive. What is left, once you require a compact complex manifold of dimension `g` with analytic group operations, is torus-like: classically, a connected compact complex Lie group of dimension `g` is ℂ^g modulo a full lattice.

That classification is background, not something proved here — and connectedness of `Jacobian X` is not proved here either. What is proved here is that the object built from honest periods satisfies all of the requirements, which is the direction the challenge needs.
