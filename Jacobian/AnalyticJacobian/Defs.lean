import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.PeriodFunctional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The analytic Jacobian as an abstract group quotient

```text
AnalyticJacobianGroup E X :=
    (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸ periodSubgroup E X
```

This is the **group-theoretic** shape of the analytic Jacobian — the
linear dual of holomorphic 1-forms quotiented by the period subgroup.
`AddCommGroup` structure comes for free from `QuotientAddGroup`.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods


noncomputable abbrev AnalyticJacobianGroup
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸ periodSubgroup E X

/--
Sanity check: the additive group structure on `AnalyticJacobianGroup`
comes for free from `QuotientAddGroup`.
-/
noncomputable example
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (AnalyticJacobianGroup E X) :=
  inferInstance

end JacobianChallenge.AnalyticJacobian
