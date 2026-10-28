import Jacobian.AnalyticJacobian.Defs
import Jacobian.Periods.PeriodSubgroupApi
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Quotient projection API for `AnalyticJacobianGroup`

`AnalyticJacobianGroup E X` is `(HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸
periodSubgroup E X` — the standard `QuotientAddGroup`. This file
exposes the quotient projection and a handful of named wrappers
around the inherited `QuotientAddGroup` API.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
Quotient projection from a linear functional to its analytic
Jacobian class.
-/
noncomputable abbrev mk (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) : AnalyticJacobianGroup E X :=
  QuotientAddGroup.mk φ

@[simp] theorem mk_zero :
    mk E X 0 = 0 := by
  rfl

theorem mk_add (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (φ + ψ) = mk E X φ + mk E X ψ := by
  rfl

/--
A class is zero iff the underlying functional lies in the
period subgroup.
-/
theorem mk_eq_zero_iff (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = 0 ↔ φ ∈ periodSubgroup E X :=
  QuotientAddGroup.eq_zero_iff φ

end JacobianChallenge.AnalyticJacobian
