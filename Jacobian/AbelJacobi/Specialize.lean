import Jacobian.AbelJacobi.GenusWitness
import Jacobian.AnalyticJacobian.EvalJacobianClassMember
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Specializations of `witnessAbelJacobi` to common base-point cases

Combines the witness machinery with `EvalJacobianClassMember` to give
common compute-rule shortcuts.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
If `evalJacobianClass basePoint v = 0` then the witness equals the
endpoint class.
-/
theorem witnessAbelJacobi_eq_endpoint_of_basePoint_class_zero
    (basePoint P : X) (v : E)
    (h : evalJacobianClass (E := E) (X := X) basePoint v = 0) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      evalJacobianClass P v := by
  unfold witnessAbelJacobi
  rw [h, sub_zero]

/-- If both endpoints map to the zero class, the witness is zero. -/
theorem witnessAbelJacobi_eq_zero_of_both_classes_zero
    (basePoint P : X) (v : E)
    (h₁ : evalJacobianClass (E := E) (X := X) basePoint v = 0)
    (h₂ : evalJacobianClass (E := E) (X := X) P v = 0) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  unfold witnessAbelJacobi
  rw [h₁, h₂, sub_self]

/--
Witness vanishes when both `evalLinearMap` values lie in
`periodSubgroup`.
-/
theorem witnessAbelJacobi_eq_zero_of_both_evalLinearMap_mem
    (basePoint P : X) (v : E)
    (h₁ : evalLinearMap basePoint v ∈ periodSubgroup E X)
    (h₂ : evalLinearMap P v ∈ periodSubgroup E X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 :=
  witnessAbelJacobi_eq_zero_of_both_classes_zero basePoint P v
    (evalJacobianClass_eq_zero_of_evalLinearMap_mem_periodSubgroup _ _ h₁)
    (evalJacobianClass_eq_zero_of_evalLinearMap_mem_periodSubgroup _ _ h₂)

/--
Witness equals the endpoint class when both `evalLinearMap` values
are zero (a degenerate but useful corner case).
-/
theorem witnessAbelJacobi_eq_zero_of_both_evalLinearMap_zero
    (basePoint P : X) (v : E)
    (h₁ : evalLinearMap (E := E) (X := X) basePoint v = 0)
    (h₂ : evalLinearMap (E := E) (X := X) P v = 0) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 :=
  witnessAbelJacobi_eq_zero_of_both_classes_zero basePoint P v
    (evalJacobianClass_eq_zero_of_evalLinearMap_zero _ _ h₁)
    (evalJacobianClass_eq_zero_of_evalLinearMap_zero _ _ h₂)

end JacobianChallenge.AbelJacobi
