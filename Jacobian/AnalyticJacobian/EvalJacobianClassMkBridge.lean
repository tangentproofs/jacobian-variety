import Jacobian.AnalyticJacobian.EvalJacobianClass
import Jacobian.AnalyticJacobian.MkArith
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Explicit `mk`-bridge formulas for `evalJacobianClass` arithmetic

Each of `add`, `sub`, `neg`, `zero` for `evalJacobianClass`
expressed as a single `mk` of the corresponding `evalLinearMap`
arithmetic.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
`evalJacobianClass P v + evalJacobianClass Q v
    = mk (evalLinearMap P v + evalLinearMap Q v)`.
-/
theorem evalJacobianClass_add_eq_mk
    (P Q : X) (v : E) :
    evalJacobianClass (E := E) (X := X) P v +
        evalJacobianClass Q v =
      mk E X (evalLinearMap P v + evalLinearMap Q v) := by
  rw [evalJacobianClass_def, evalJacobianClass_def, mk_add]

/--
`evalJacobianClass P v - evalJacobianClass Q v
    = mk (evalLinearMap P v - evalLinearMap Q v)`.
-/
theorem evalJacobianClass_sub_eq_mk
    (P Q : X) (v : E) :
    evalJacobianClass (E := E) (X := X) P v -
        evalJacobianClass Q v =
      mk E X (evalLinearMap P v - evalLinearMap Q v) := by
  rw [evalJacobianClass_def, evalJacobianClass_def, mk_sub]

/-- `-evalJacobianClass P v = mk (-evalLinearMap P v)`. -/
theorem evalJacobianClass_neg_eq_mk
    (P : X) (v : E) :
    -evalJacobianClass (E := E) (X := X) P v =
      mk E X (-evalLinearMap P v) := by
  rw [evalJacobianClass_def, mk_neg]

/-- `(0 : AnalyticJacobianGroup E X) = mk E X 0`. -/
theorem zero_analyticJacobianGroup_eq_mk_zero :
    (0 : AnalyticJacobianGroup E X) =
      mk E X (0 : HolomorphicOneForm E X →ₗ[ℂ] ℂ) := by
  rw [mk_zero]

end JacobianChallenge.AnalyticJacobian
