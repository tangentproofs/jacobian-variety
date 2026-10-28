import Jacobian.AnalyticJacobian.MkArith
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Interactions between `mk` and `periodPairing`

`mk_periodPairing_eq_zero` (from `MkMembership`) says `mk` kills the
range of `periodPairing`. Here we expose corollaries: adding a
`periodPairing` value to a functional doesn't change its `mk` class.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- Adding a `periodPairing` value to `φ` doesn't change `mk φ`. -/
@[simp] theorem mk_add_periodPairing
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (σ : IntegralOneCycle X) :
    mk E X (φ + periodPairing E X σ) = mk E X φ := by
  rw [mk_add, mk_periodPairing_eq_zero, add_zero]

/-- `mk` ignores `periodPairing` on the left as well. -/
@[simp] theorem mk_periodPairing_add
    (σ : IntegralOneCycle X) (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (periodPairing E X σ + φ) = mk E X φ := by
  rw [mk_add, mk_periodPairing_eq_zero, zero_add]

/-- Subtracting a `periodPairing` value also leaves `mk` unchanged. -/
@[simp] theorem mk_sub_periodPairing
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (σ : IntegralOneCycle X) :
    mk E X (φ - periodPairing E X σ) = mk E X φ := by
  rw [mk_sub, mk_periodPairing_eq_zero, sub_zero]

/-- `mk` of the negation of a `periodPairing` is `0`. -/
@[simp] theorem mk_neg_periodPairing
    (σ : IntegralOneCycle X) :
    mk E X (-periodPairing E X σ) = 0 := by
  rw [mk_neg, mk_periodPairing_eq_zero, neg_zero]

end JacobianChallenge.AnalyticJacobian
