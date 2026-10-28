import Jacobian.AnalyticJacobian.MkExt
import Jacobian.HolomorphicForms.EvalLinearMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Zero-class characterizations for `evalJacobianClass`

Combines `mk_eq_zero_iff` with the witness lift `evalJacobianClass`
to give convenience criteria for when a witness pair `(x, v)` lifts
to the zero class in the analytic Jacobian.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
A witness pair `(x, v)` lifts to the zero analytic Jacobian
class iff its `evalLinearMap` value lies in the period subgroup.
-/
theorem evalJacobianClass_eq_zero_iff (x : X) (v : E) :
    evalJacobianClass (E := E) (X := X) x v = 0 ↔
      evalLinearMap x v ∈ periodSubgroup E X := by
  rw [evalJacobianClass_def, mk_eq_zero_iff]

/-- If `evalLinearMap x v ∈ periodSubgroup`, the lift is zero. -/
theorem evalJacobianClass_zero_of_mem_periodSubgroup
    (x : X) (v : E)
    (h : evalLinearMap x v ∈ periodSubgroup E X) :
    evalJacobianClass (E := E) (X := X) x v = 0 :=
  (evalJacobianClass_eq_zero_iff x v).mpr h

/--
If `evalLinearMap x v = 0` then the lift is zero (since
0 ∈ any AddSubgroup).
-/
theorem evalJacobianClass_zero_of_evalLinearMap_eq_zero
    (x : X) (v : E) (h : evalLinearMap x v = (0 : HolomorphicOneForm E X →ₗ[ℂ] ℂ)) :
    evalJacobianClass (E := E) (X := X) x v = 0 := by
  apply evalJacobianClass_zero_of_mem_periodSubgroup
  rw [h]
  exact (periodSubgroup E X).zero_mem

/--
Two witnesses give the same Jacobian class iff their
`evalLinearMap` difference lies in the period subgroup.
-/
theorem evalJacobianClass_eq_iff (x : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) x v =
      evalJacobianClass (E := E) (X := X) x w ↔
      -evalLinearMap x v + evalLinearMap x w ∈ periodSubgroup E X := by
  rw [evalJacobianClass_def, evalJacobianClass_def, mk_eq_mk_iff]

end JacobianChallenge.AnalyticJacobian
