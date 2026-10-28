import Jacobian.AbelJacobi.Identities
import Jacobian.AnalyticJacobian.EvalJacobianClassZero
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Coset-flavoured wrappers for `witnessAbelJacobi`

Repackages the witness/class identities in the language of cosets
of `periodSubgroup` — useful when a downstream proof reasons in
terms of the underlying functionals rather than the Jacobian quotient.
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
`witnessAbelJacobi basePoint P v = 0` iff
`evalJacobianClass P v = evalJacobianClass basePoint v`.
-/
theorem witnessAbelJacobi_eq_zero_iff_class_eq
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      evalJacobianClass P v = evalJacobianClass basePoint v :=
  witnessAbelJacobi_eq_zero_iff basePoint P v

/-- Antisymmetric specialization: `witness B P v + witness P B v = 0`. -/
theorem witnessAbelJacobi_add_swap_eq_zero
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v +
      witnessAbelJacobi (E := E) (X := X) P basePoint v = 0 := by
  unfold witnessAbelJacobi
  abel

/--
Endpoint algebra: the witness from `B → P` minus the witness from
`B → Q` equals the witness from `Q → P`.
-/
theorem witnessAbelJacobi_endpoint_diff
    (basePoint P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v -
      witnessAbelJacobi (E := E) (X := X) basePoint Q v =
      witnessAbelJacobi (E := E) (X := X) Q P v := by
  unfold witnessAbelJacobi
  abel

/--
Two witnesses with the same endpoints but different base points
differ by a constant (the inter-base-point witness).
-/
theorem witnessAbelJacobi_base_change_eq
    (basePoint basePoint' P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      witnessAbelJacobi (E := E) (X := X) basePoint' P v +
        witnessAbelJacobi (E := E) (X := X) basePoint basePoint' v := by
  unfold witnessAbelJacobi
  abel

end JacobianChallenge.AbelJacobi
