import Jacobian.AnalyticJacobian.EvalJacobianClass
import Jacobian.HolomorphicForms.EvalLinearMapVecExtra
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vec-slot group operations on `evalJacobianClass`

Closes the vec-slot group-operation matrix on the witness lift
`evalJacobianClass`: subtraction, negation, and `ℕ`/`ℤ` scaling.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

theorem evalLinearMap_vec_neg [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x : X) (v : E) :
    evalLinearMap (X := X) x (-v) = -evalLinearMap (X := X) x v := by
  ext η
  exact evalLinearMap_neg_vec x v η

theorem evalLinearMap_vec_sub [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x : X) (v w : E) :
    evalLinearMap (X := X) x (v - w) =
      evalLinearMap (X := X) x v - evalLinearMap (X := X) x w := by
  ext η
  exact evalLinearMap_sub_vec x v w η

variable [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

theorem evalJacobianClass_neg_vec (x : X) (v : E) :
    evalJacobianClass (E := E) (X := X) x (-v) =
      -evalJacobianClass (E := E) (X := X) x v := by
  rw [evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_neg, mk_neg]

theorem evalJacobianClass_sub_vec (x : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) x (v - w) =
      evalJacobianClass (E := E) (X := X) x v -
        evalJacobianClass (E := E) (X := X) x w := by
  rw [evalJacobianClass_def, evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_sub, mk_sub]

end JacobianChallenge.AnalyticJacobian
