import Jacobian.AbelJacobi.AnalyticOfCurveU
import Mathlib.GroupTheory.QuotientGroup.Basic
import Jacobian.Surface.Abel

/-!
# Universe-polymorphic Abel-Jacobi injectivity

`analyticOfCurve_injectiveU (P) (h : 0 < analyticGenus ℂ X)` — injectivity of the
analytic Abel–Jacobi map in positive genus, needed by the public `ofCurve_inj`. The
assembly (`QuotientAddGroup.eq.mp`) is proved here; the deep content, Abel's theorem in
two-point form, is `pathIntegralFunctional_separates_pointsU` (proved in
`Jacobian/Surface/Abel.lean`).

Note on the Type-0 `analyticOfCurve_injective` in `AnalyticOfCurveBasis.lean`: it is not
on the public path, and the chain feeding it is placeholder scaffolding (`Unit`/`True`
fields; see `ref/rkirov-gap-comparison.md`, gap 2), not a proof of Abel's theorem.
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
**Abel's theorem, two-point form (point separation).** If the Abel–Jacobi integrals from `P`
to `Q₁` and to `Q₂` differ by a period, and the genus is positive, then `Q₁ = Q₂`.

Proof (`JacobianChallenge.Surface.FChain.eq_of_periodVector_sub_mem`): otherwise there is a
formal chain from `Q₁` to `Q₂` with zero integrals against every holomorphic form; the
`(0,1)`-form it defines is then `∂̄`-exact (Hodge decomposition), which produces a meromorphic
function with a single simple pole; such a function is a degree-one map to the Riemann sphere,
so `X` is a sphere and has genus `0` — a contradiction.
-/
theorem pathIntegralFunctional_separates_pointsU
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctionalU X P Q₁ + pathIntegralFunctionalU X P Q₂ ∈
        genuinePeriodSubgroup X) :
    Q₁ = Q₂ :=
  JacobianChallenge.Surface.FChain.eq_of_periodVector_sub_mem h (chosenChain_isChain X P Q₁)
    (chosenChain_isChain X P Q₂) hperiod

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
