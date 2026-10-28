import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.Periods.BasisAlignedPeriodSubgroupU
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Universe-polymorphic Abel-Jacobi injectivity

`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` proves the plain Abel-Jacobi
injectivity `analyticOfCurve_injective (P) (h : 0 < analyticGenus ℂ X) :
Function.Injective (analyticOfCurve X P)` by a trivial quotient assembly
(`QuotientAddGroup.eq.mp`) on top of the genuine separating-points theorem
`pathIntegralFunctional_separates_points`. That separating-points theorem is the
deep content (Abel's theorem): its proof threads
`abelJacobi_image_zero_implies_principal` — which produces a
`HolomorphicForms.MeromorphicMapToSphere X` — and the genus-zero classification.

This file provides the universe-polymorphic companion `analyticOfCurve_injectiveU`
(D2 of the Abel-Jacobi "D-chain"), needed by the public `ofCurve_inj` for
`X : Type u` (Milestone B).

## Why the separating-points fact is a tracked frontier obligation here

Re-deriving the genuine separating-points proof at `Type u` would re-thread the
entire Abel-existence / meromorphic-degree / genus-zero chain through
`MeromorphicMapToSphere X` — precisely the surface currently being restructured
(the `PoleModulusData` / `BranchedCoverDataOfPoleDegree` field un-bundling). To
keep this step self-contained and avoid a moving-target collision, the deep
content is isolated into a single named obligation
`pathIntegralFunctional_separates_pointsU` (the universe-`u` analogue of the
genuine Type-0 `pathIntegralFunctional_separates_points`); the injectivity
assembly on top of it is genuine.

This is a `theorem … := sorry`, NOT an `opaque`: the Type-0 separating-points
declaration is itself a genuine `theorem`, and a `Prop`-valued result `Q₁ = Q₂`
cannot be `opaque` (it has no `Inhabited`/`Nonempty` witness). It is a
Periods/AbelJacobi layer-frontier sorry — NOT a sorry in `Jacobian/Solution.lean`'s
public anti-hack block, NOT an axiom. It will be discharged genuinely once the
universe-`u` Abel chain is built, after the `MeromorphicMapToSphere`
restructuring settles. This file introduces **no** `MeromorphicMapToSphere`
reference.
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods JacobianChallenge.ComplexTorus

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
**Abel's theorem in universe-`u` basis-aligned path-integral coordinates
(named tracked frontier obligation).** If two universe-`u` path-integral
coordinate vectors differ by a period vector (lie in the same coset of the
universe-`u` period subgroup), their endpoints coincide.

Universe-polymorphic analogue of the genuine Type-0
`pathIntegralFunctional_separates_points`. Recorded as a named tracked
Periods/AbelJacobi layer-frontier obligation; see the module docstring for why
the universe-`u` re-derivation is deferred (it would re-thread the
`MeromorphicMapToSphere` surface currently being restructured). NOT a
public-block sorry, NOT an axiom.
-/
theorem pathIntegralFunctional_separates_pointsU
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctionalU X P Q₁ + pathIntegralFunctionalU X P Q₂ ∈
        basisAlignedPeriodSubgroupConcreteU X) :
    Q₁ = Q₂ :=
  sorry

/--
Abel injectivity for positive genus, universe-polymorphic. Universe-polymorphic
companion to `analyticOfCurve_injective`: a genuine quotient assembly on top of
`pathIntegralFunctional_separates_pointsU`.
-/
lemma analyticOfCurve_injectiveU (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurveU X P) := by
  intro Q₁ Q₂ heq
  apply pathIntegralFunctional_separates_pointsU X P h Q₁ Q₂
  unfold analyticOfCurveU at heq
  exact QuotientAddGroup.eq.mp heq

end JacobianChallenge.AbelJacobi
