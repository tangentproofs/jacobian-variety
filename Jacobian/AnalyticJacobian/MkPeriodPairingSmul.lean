import Jacobian.AnalyticJacobian.MkPeriodPairing
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `mk` is invariant under integer-scaled `periodPairing` adjustments

Continues `MkPeriodPairing` with scaled variants. Since `periodPairing`
values lie in `periodSubgroup` (an `AddSubgroup`), integer multiples
of them do too.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk` of a natural-scaled `periodPairing` value is `0`. -/
@[simp] theorem mk_nsmul_periodPairing
    (n : ℕ) (σ : IntegralOneCycle X) :
    mk E X (n • periodPairing E X σ) = 0 := by
  rw [mk_nsmul, mk_periodPairing_eq_zero, smul_zero]

/-- `mk` of an integer-scaled `periodPairing` value is `0`. -/
@[simp] theorem mk_zsmul_periodPairing
    (n : ℤ) (σ : IntegralOneCycle X) :
    mk E X (n • periodPairing E X σ) = 0 := by
  rw [mk_zsmul, mk_periodPairing_eq_zero, smul_zero]

/-- Adding a natural-scaled `periodPairing` doesn't change `mk`. -/
@[simp] theorem mk_add_nsmul_periodPairing
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (n : ℕ) (σ : IntegralOneCycle X) :
    mk E X (φ + n • periodPairing E X σ) = mk E X φ := by
  rw [mk_add, mk_nsmul_periodPairing, add_zero]

/-- Adding an integer-scaled `periodPairing` doesn't change `mk`. -/
@[simp] theorem mk_add_zsmul_periodPairing
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (n : ℤ) (σ : IntegralOneCycle X) :
    mk E X (φ + n • periodPairing E X σ) = mk E X φ := by
  rw [mk_add, mk_zsmul_periodPairing, add_zero]

end JacobianChallenge.AnalyticJacobian
