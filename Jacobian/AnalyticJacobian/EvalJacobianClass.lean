import Jacobian.AnalyticJacobian.MkExt
import Jacobian.HolomorphicForms.EvalLinearMapVec
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vec-slot linearity for `evalJacobianClass`

`evalJacobianClass x v` is the analytic Jacobian class of the
ℂ-linear functional `η ↦ η.toFun x v`. As `v` varies, these
functionals (and hence their classes) are themselves additive in
`v` — this file exposes that as named lemmas.

Note: smul_vec is not yet exposed, since the analytic Jacobian
quotient does not (a priori) carry a ℂ-action; only the
`AddCommGroup` (over ℤ) is available at this stage.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/- `evalLinearMap x` is additive in the vector argument
(at the LinearMap level). -/
theorem evalLinearMap_vec_add (x : X) (v w : E) :
    evalLinearMap (X := X) x (v + w) =
      evalLinearMap (X := X) x v + evalLinearMap (X := X) x w := by
  ext η
  exact evalLinearMap_add_vec x v w η

/- `evalLinearMap x` sends `0` to the zero LinearMap. -/
theorem evalLinearMap_vec_zero (x : X) :
    evalLinearMap (X := X) x (0 : E) = 0 := by
  ext η
  exact evalLinearMap_zero_vec x η

variable [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

@[simp] theorem evalJacobianClass_zero_vec (x : X) :
    evalJacobianClass (E := E) (X := X) x 0 = 0 := by
  rw [evalJacobianClass_def, evalLinearMap_vec_zero, mk_zero]

theorem evalJacobianClass_add_vec (x : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) x (v + w) =
      evalJacobianClass (E := E) (X := X) x v +
        evalJacobianClass (E := E) (X := X) x w := by
  rw [evalJacobianClass_def, evalJacobianClass_def, evalJacobianClass_def,
      evalLinearMap_vec_add, mk_add]

end JacobianChallenge.AnalyticJacobian
