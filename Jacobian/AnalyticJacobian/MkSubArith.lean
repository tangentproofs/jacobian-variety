import Jacobian.AnalyticJacobian.MkArith
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Combined sub/add/neg arithmetic identities for `mk`

Extends `MkArith` with mixed sub/neg combinations, derived directly
from the LinearMap-quotient `mk_add` / `mk_neg` / `mk_sub` identities.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk (φ - -ψ) = mk φ + mk ψ`. -/
theorem mk_sub_neg
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (φ - -ψ) = mk E X φ + mk E X ψ := by
  rw [sub_neg_eq_add, mk_add]

/-- `mk (-φ + ψ) = -mk φ + mk ψ`. -/
theorem mk_neg_add
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (-φ + ψ) = -mk E X φ + mk E X ψ := by
  rw [mk_add, mk_neg]

/-- `mk (φ + -ψ) = mk φ - mk ψ`. -/
theorem mk_add_neg
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (φ + -ψ) = mk E X φ - mk E X ψ := by
  rw [mk_add, mk_neg, ← sub_eq_add_neg]

/-- `mk (-(φ + ψ)) = -mk φ - mk ψ`. -/
theorem mk_neg_add_distrib
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (-(φ + ψ)) = -mk E X φ - mk E X ψ := by
  rw [mk_neg, mk_add, neg_add, ← sub_eq_add_neg]

end JacobianChallenge.AnalyticJacobian
