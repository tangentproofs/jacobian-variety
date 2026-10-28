import Jacobian.AnalyticJacobian.EvalJacobianClassOps
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Integer-scaling on the vec slot of `evalJacobianClass` -/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

theorem evalLinearMap_vec_nsmul [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x : X) (n : ℕ) (v : E) :
    evalLinearMap (X := X) x (n • v) = n • evalLinearMap (X := X) x v := by
  ext η
  exact evalLinearMap_nsmul_vec x n v η

theorem evalLinearMap_vec_zsmul [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x : X) (n : ℤ) (v : E) :
    evalLinearMap (X := X) x (n • v) = n • evalLinearMap (X := X) x v := by
  ext η
  exact evalLinearMap_zsmul_vec x n v η

variable [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

theorem evalJacobianClass_nsmul_vec (x : X) (n : ℕ) (v : E) :
    evalJacobianClass (E := E) (X := X) x (n • v) =
      n • evalJacobianClass (E := E) (X := X) x v := by
  rw [evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_nsmul, mk_nsmul]

theorem evalJacobianClass_zsmul_vec (x : X) (n : ℤ) (v : E) :
    evalJacobianClass (E := E) (X := X) x (n • v) =
      n • evalJacobianClass (E := E) (X := X) x v := by
  rw [evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_zsmul, mk_zsmul]

end JacobianChallenge.AnalyticJacobian
