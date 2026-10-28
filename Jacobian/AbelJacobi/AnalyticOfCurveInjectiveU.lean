import Jacobian.AbelJacobi.AnalyticOfCurveU
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Universe-polymorphic Abel-Jacobi injectivity

`analyticOfCurve_injectiveU (P) (h : 0 < analyticGenus ℂ X)` — injectivity of the
analytic Abel–Jacobi map in positive genus, needed by the public `ofCurve_inj`. The
assembly (`QuotientAddGroup.eq.mp`) is proved here; the deep content is the single named
classical input `pathIntegralFunctional_separates_pointsU` (Abel's theorem, two-point
form).

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
**CLASSICAL INPUT — Abel's theorem, two-point form (point separation).** If the
Abel–Jacobi integrals from `P` to `Q₁` and to `Q₂` differ by a period, and the genus is
positive, then `Q₁ = Q₂`.

Classical proof: by Abel's theorem the divisor `Q₂ - Q₁` is then principal, i.e. there is
a meromorphic function with a single simple pole; such a function is a degree-one map to
the Riemann sphere, hence a biholomorphism, so `X` has genus `0` — a contradiction.
References: O. Forster, *Lectures on Riemann Surfaces*, Thm. 20.7 (Abel) and §21;
Griffiths–Harris, Ch. 2 §2.

Named classical input (`sorry`); see `ref/axiom-audit.md`, "Classical inputs".
The statement is now about the **genuine** path integral and the **genuine** period
lattice (`genuinePeriodSubgroup`). Previously it was stated about an `opaque` functional
whose specification the zero functional satisfied, against a period subgroup equal to
`⊥`, under the refuted `StableChartAt` binder.
-/
theorem pathIntegralFunctional_separates_pointsU
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctionalU X P Q₁ + pathIntegralFunctionalU X P Q₂ ∈
        genuinePeriodSubgroup X) :
    Q₁ = Q₂ := by
  -- CLASSICAL INPUT: Abel's theorem + degree-one maps; see docstring.
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
