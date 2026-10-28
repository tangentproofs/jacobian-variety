import Jacobian.AnalyticJacobian.EvalJacobianClassEq
import Jacobian.AnalyticJacobian.MkMembership
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Sub-membership characterization of `evalJacobianClass` equality -/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
`evalJacobianClass P v = evalJacobianClass Q w` iff
`evalLinearMap P v - evalLinearMap Q w ∈ periodSubgroup`.
-/
theorem evalJacobianClass_eq_iff_sub_mem
    (P Q : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w ↔
      evalLinearMap P v - evalLinearMap Q w ∈ periodSubgroup E X := by
  unfold evalJacobianClass
  exact mk_eq_mk_iff_sub_mem _ _

/--
`evalJacobianClass P v - evalJacobianClass Q w = 0` iff
the two classes are equal.
-/
theorem evalJacobianClass_sub_eq_zero_iff_eq
    (P Q : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) P v -
        evalJacobianClass Q w = 0 ↔
      evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w :=
  sub_eq_zero

/--
`evalJacobianClass P v - evalJacobianClass Q w = 0` iff
`evalLinearMap P v - evalLinearMap Q w ∈ periodSubgroup`.
-/
theorem evalJacobianClass_sub_eq_zero_iff_sub_mem
    (P Q : X) (v w : E) :
    evalJacobianClass (E := E) (X := X) P v -
        evalJacobianClass Q w = 0 ↔
      evalLinearMap P v - evalLinearMap Q w ∈ periodSubgroup E X := by
  rw [evalJacobianClass_sub_eq_zero_iff_eq, evalJacobianClass_eq_iff_sub_mem]

/--
Sufficient condition (sub-form): `evalJacobianClass P v =
evalJacobianClass Q w` whenever the representative difference lies in
`periodSubgroup`.
-/
theorem evalJacobianClass_eq_of_sub_mem
    (P Q : X) (v w : E)
    (h : evalLinearMap P v - evalLinearMap Q w ∈ periodSubgroup E X) :
    evalJacobianClass (E := E) (X := X) P v =
        evalJacobianClass Q w :=
  (evalJacobianClass_eq_iff_sub_mem P Q v w).mpr h

end JacobianChallenge.AnalyticJacobian
