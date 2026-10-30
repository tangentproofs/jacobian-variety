---
id: genus_eq_zero_iff_homeo
title: Genus zero exactly for the sphere
summary: 'A compact Riemann surface has no nonzero holomorphic 1-form precisely when it is homeomorphic to the round 2-sphere, and both directions are proved here from scratch.'
review: draft
authors:
- claude
caveats:
- 'The conclusion is `Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`: a homeomorphism to the unit sphere in ℝ³. It is **not** a biholomorphism, and not an identification with ℙ¹ as a complex manifold. No uniformization theorem is proved in this repository.'
- '`genus X` is the *analytic* genus `Module.finrank ℂ (HolomorphicOneForm ℂ X)` (Jacobian/Solution.lean lines 45–47). A `topologicalGenus` is defined separately, as half the ℤ-rank of singular H₁ (Jacobian/Periods/TopologicalGenus.lean lines 113–116), but no theorem relates the two. This lemma is the only bridge between the analytic genus and topology, and only at the value 0.'
- 'The lemma is a biconditional about whatever X you hand it. It does not exhibit a surface of positive genus: the only concrete compact Riemann surface built in the repository is the one-point compactification ℂ̂ (Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean line 166), whose genus is proved to be 0 (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 638–642), and `0 < genus X` occurs only as a hypothesis. So the lemma blocks `genus X := 0` only given that non-spherical compact Riemann surfaces exist, which is classical but not formalized here.'
- 'The ℂℙ¹-and-canonical-divisor route to `analyticGenus_eq_zero_of_homeomorphic_sphere` is *not* the proof used. Its docstring (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1418–1432) lists that uniformization argument among "two earlier routes to the same statement [that] are still available in this file but are not used here"; the proof at Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1433–1446 runs through simple connectivity of the punctured sphere, and its own comment says "No uniformization needed".'
quiz:
- q: What exactly is on the right-hand side of the biconditional?
  type: choice
  choices:
  - 'A biholomorphism `X ≅ ℙ¹` of complex manifolds'
  - 'A homeomorphism `X ≃ₜ` the unit sphere in `EuclideanSpace ℝ (Fin 3)`'
  - 'An isomorphism of the homology group `H₁(X, ℤ)` with 0'
  answer: 1
  explain: 'Jacobian/Solution.lean lines 70–72 state `Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))`, which is a topological equivalence only.'
- q: 'Which meaning of "genus" does this lemma constrain?'
  type: choice
  choices:
  - 'The number of handles, defined topologically'
  - 'The complex dimension of the space of holomorphic 1-forms'
  - 'Half the rank of the first homology group'
  answer: 1
  explain: '`genus X` unfolds to `Module.finrank ℂ (HolomorphicOneForm ℂ X)` at Jacobian/Solution.lean lines 45–47. The repo proves no link to a topological definition apart from this lemma at genus 0.'
- q: How is the direction "genus 0 ⇒ sphere" obtained?
  type: choice
  choices:
  - 'By quoting the uniformization theorem from Mathlib'
  - 'By solving a ∂̄ equation to get a function with one simple pole, which is a degree-one map to ℂ̂, then composing with a homeomorphism ℂ̂ ≃ₜ S²'
  - 'By counting handles in a triangulation of X'
  answer: 1
  explain: '`Surface.homeomorph_onePoint_of_forall_eq_zero` (Jacobian/Surface/GenusZero.lean lines 432–438) builds the simple-pole function, and `onePointCx_homeomorph_sphere` (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 44–46) supplies ℂ̂ ≃ₜ S².'
- q: How is the direction "sphere ⇒ genus 0" obtained?
  type: choice
  choices:
  - 'Every holomorphic 1-form on such a surface vanishes, because the punctured sphere is simply connected so the form has a primitive and its chain integrals depend only on endpoints'
  - 'By computing the degree of the canonical bundle of ℙ¹'
  - 'It is assumed as a hypothesis'
  answer: 0
  explain: '`Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere` (Jacobian/Periods/PrimitiveCovering.lean lines 472–486) runs exactly that argument, with simple connectivity from stereographic projection at Jacobian/Periods/PrimitiveCovering.lean lines 458–469.'
- q: Does the lemma, on its own, prove that some compact Riemann surface has positive genus?
  type: choice
  choices:
  - 'Yes, it constructs a torus'
  - 'No. It is a biconditional about whatever X you hand it; no positive-genus surface is built anywhere in the repository'
  - 'Yes, because the sphere is the only compact surface'
  answer: 1
  explain: 'The statement at Jacobian/Solution.lean lines 70–72 quantifies over X. The only concrete compact Riemann surface in the repository is ℂ̂ (Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean line 166), of genus 0. The force against the hack answer `genus X := 0` comes from non-spherical surfaces existing, which is classical and not formalized here.'
---
## Plain English

Fix a compact, connected, Hausdorff space X with holomorphic charts to ℂ: a compact Riemann surface. Its [genus](#/node/genus) is defined to be the complex dimension of the space of [holomorphic 1-forms](#/node/HolomorphicForms.HolomorphicOneForm) on it (Jacobian/Solution.lean lines 45–47). This theorem says:

> that dimension is 0 if and only if X is homeomorphic to the round unit sphere in ℝ³.

Both directions are proved. The hypotheses are exactly the ambient ones: `TopologicalSpace`, `T2Space`, `CompactSpace`, `ConnectedSpace`, `ChartedSpace ℂ X`, `IsManifold 𝓘(ℂ) ω X` (Jacobian/Solution.lean lines 67–68). Nothing else is assumed. The right-hand side is a *homeomorphism*, which is weaker than the classical statement "genus 0 implies biholomorphic to ℙ¹".

The public lemma (Jacobian/Solution.lean lines 70–72) is a one-line delegation to [analyticGenus_eq_zero_iff_homeomorphic_sphere](#/node/HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere) (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1888–1896).

## Why it matters

The specification marks this one explicitly: "this proof avoids the hack answer `∀ X, genus X = 0`" (Jacobian/Challenge.lean lines 51–54). Without it, somebody could define `genus X := 0`, define the Jacobian as a one-point group, and satisfy most of the rest of the challenge trivially. Tying `genus X = 0` to a topological property of X forces the definition to see the surface.

The force is conditional in one respect. The lemma says what genus 0 means, not that any surface fails to be a sphere. A non-spherical compact Riemann surface (a complex torus, say) is not constructed anywhere in this repository, so the refutation of `genus X := 0` is completed outside the formalization.

## How the proof goes

**Genus 0 ⇒ sphere.** This half is [homeomorphic_sphere_of_analyticGenus_eq_zero](#/node/HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero) (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1873–1881), which chains [genus_zero_homeomorph_onePointCx](#/node/HolomorphicForms.genus_zero_homeomorph_onePointCx) (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1856–1868) with a homeomorphism ℂ̂ ≃ₜ S². Genus 0 means the space of holomorphic 1-forms has `finrank` zero, hence (being finite-dimensional) is a single point, so every holomorphic 1-form on X is zero. That vanishing is exactly what makes the ∂̄ equation solvable on X. [homeomorph_onePoint_of_forall_eq_zero](#/node/Surface.homeomorph_onePoint_of_forall_eq_zero) (Jacobian/Surface/GenusZero.lean lines 432–438) picks a point P, takes a bump function around it, solves ∂̄u = ∂̄(χ/(w − z₀)), and assembles a meromorphic function on X with exactly one simple pole. A function with one simple pole is a degree-one map to the one-point compactification ℂ̂, and a degree-one holomorphic map is a homeomorphism. Finally [onePointCx_homeomorph_sphere](#/node/HolomorphicForms.onePointCx_homeomorph_sphere) (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 44–46) transports ℂ̂ to S² using Mathlib's `onePointEquivSphereOfFinrankEq` and the fact that ℂ has real dimension 2.

**Sphere ⇒ genus 0.** [analyticGenus_eq_zero_of_homeomorphic_sphere](#/node/HolomorphicForms.analyticGenus_eq_zero_of_homeomorphic_sphere) (Jacobian/HolomorphicForms/GenusZeroClassification.lean lines 1433–1446) shows every holomorphic 1-form is zero, via [holomorphicOneForm_eq_zero_of_homeomorph_sphere](#/node/Periods.holomorphicOneForm_eq_zero_of_homeomorph_sphere) (Jacobian/Periods/PrimitiveCovering.lean lines 472–486). The argument: delete a point not met by the chains in question; the punctured sphere is [simply connected by stereographic projection](#/node/Periods.simplyConnectedSpace_compl_of_homeomorph_sphere) (Jacobian/Periods/PrimitiveCovering.lean lines 458–469); so the form has a global primitive there; so its [chain integrals](#/node/Periods.chainIntegral) depend only on the endpoints; and a form whose chain integrals have the same real part along any two chains with the same endpoints is 0 ([eq_zero_of_re_chainIntegral_eq](#/node/Periods.eq_zero_of_re_chainIntegral_eq)). No Hodge theory and no uniformization needed on this side.

Neither half is admitted. `ref/axiom-audit.md` reports that no public declaration depends on a `sorry` and that every public declaration prints the axioms `propext`, `Classical.choice`, `Quot.sound`, with a strict comparator run on 2026-10-28; that is the repository's own record, not something this page re-checks.

The finite-dimensionality that makes `finrank` meaningful is itself proved, not assumed: [finiteDimensional_holomorphicOneForm](#/node/HolomorphicForms.finiteDimensional_holomorphicOneForm) is a Montel–Riesz argument over a finite chart cover (Jacobian/HolomorphicForms/Finiteness.lean line 323), registered as an instance at Jacobian/HolomorphicForms/Finiteness.lean line 372. This matters, because Mathlib's `finrank` of an infinite-dimensional space is 0 by convention, so without finiteness the left-hand side could be 0 for an empty reason.

## What it does not say

- Not "biholomorphic to ℙ¹" or "to the Riemann sphere as a complex manifold". A degree-one holomorphic map to ℂ̂ is built along the way, but no biholomorphism is constructed and no uniformization theorem is proved.
- Not "genus is the number of holes". `genus` here is the dimension of the 1-form space. No theorem equates it with `topologicalGenus` at any value; this lemma is the only link to topology, and only at 0, and even there it is phrased as a homeomorphism rather than as an equality of two genera.
- Nothing about `2g = rank H₁(X, ℤ)`, the de Rham theorem, or Riemann–Hurwitz.
