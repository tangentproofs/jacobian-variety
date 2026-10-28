import Jacobian.AnalyticJacobian.Mk
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Group operation lemmas for `AnalyticJacobianGroup.mk`

Continues `AnalyticJacobian.Mk` with neg/sub/nsmul/zsmul facade
lemmas around the inherited `QuotientAddGroup.mk` morphism.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

theorem mk_neg (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (-φ) = - mk E X φ := by
  rfl

theorem mk_sub (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (φ - ψ) = mk E X φ - mk E X ψ := by
  rfl

theorem mk_nsmul (n : ℕ) (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (n • φ) = n • mk E X φ := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, mk_add, ih]

theorem mk_zsmul (n : ℤ) (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (n • φ) = n • mk E X φ :=
  (QuotientAddGroup.mk' (periodSubgroup E X)).map_zsmul n φ

end JacobianChallenge.AnalyticJacobian
