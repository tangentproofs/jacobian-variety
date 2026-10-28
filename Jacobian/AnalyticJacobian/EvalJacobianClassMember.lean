import Jacobian.AnalyticJacobian.MkMembership
import Jacobian.AnalyticJacobian.EvalJacobianClassZero
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `evalJacobianClass` ↔ `periodSubgroup` membership criteria

Composes `MkMembership` with `EvalJacobianClassZero` to give
`evalJacobianClass`-flavoured membership / kernel facts.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
An `evalLinearMap` value lying in `periodSubgroup` makes the
corresponding `evalJacobianClass` zero.
-/
theorem evalJacobianClass_eq_zero_of_evalLinearMap_mem_periodSubgroup
    (x : X) (v : E)
    (h : evalLinearMap x v ∈ periodSubgroup E X) :
    evalJacobianClass (E := E) (X := X) x v = 0 :=
  (evalJacobianClass_eq_zero_iff x v).mpr h

/--
An `evalLinearMap` value at the zero functional gives the zero
class.
-/
theorem evalJacobianClass_eq_zero_of_evalLinearMap_zero
    (x : X) (v : E)
    (h : evalLinearMap (E := E) (X := X) x v = 0) :
    evalJacobianClass (E := E) (X := X) x v = 0 := by
  apply evalJacobianClass_eq_zero_of_evalLinearMap_mem_periodSubgroup
  rw [h]
  exact (periodSubgroup E X).zero_mem

/--
Two `evalJacobianClass` values are equal iff their `evalLinearMap`
difference lies in `periodSubgroup`.
-/
theorem evalJacobianClass_eq_evalJacobianClass_iff_sub_mem
    (x y : X) (v : E) :
    evalJacobianClass (E := E) (X := X) x v =
      evalJacobianClass (E := E) (X := X) y v ↔
      evalLinearMap x v - evalLinearMap y v ∈ periodSubgroup E X := by
  rw [evalJacobianClass_def, evalJacobianClass_def, mk_eq_mk_iff_sub_mem]

/--
`mk` of `evalLinearMap` is `0` iff the value lies in
`periodSubgroup`.
-/
theorem mk_evalLinearMap_eq_zero_iff (x : X) (v : E) :
    mk E X (evalLinearMap x v) = 0 ↔
      evalLinearMap (E := E) (X := X) x v ∈ periodSubgroup E X :=
  mk_eq_zero_iff_mem_periodSubgroup (evalLinearMap x v)

end JacobianChallenge.AnalyticJacobian
