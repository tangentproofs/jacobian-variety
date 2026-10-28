import Jacobian.AbelJacobi.Smul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Base-point change and three-point identities for `witnessAbelJacobi`

`witnessAbelJacobi` is base-point-relative; this file collects the
standard identities relating witnesses through different base points.
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
Changing the base point shifts the witness by a constant
(viz. the witness from new to old base point).
-/
theorem witnessAbelJacobi_base_change
    (basePoint basePoint' P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v -
      witnessAbelJacobi (E := E) (X := X) basePoint' P v =
      witnessAbelJacobi (E := E) (X := X) basePoint basePoint' v := by
  unfold witnessAbelJacobi
  abel

/-- Three-point identity: `(P→Q) + (Q→R) = (P→R)`. -/
theorem witnessAbelJacobi_chain_three
    (P Q R : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P Q v +
      witnessAbelJacobi (E := E) (X := X) Q R v =
      witnessAbelJacobi (E := E) (X := X) P R v := by
  unfold witnessAbelJacobi
  abel

/--
Two witnesses are equal iff their endpoint classes coincide
modulo the (common) base point.
-/
theorem witnessAbelJacobi_eq_iff_class_eq
    (basePoint P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      witnessAbelJacobi (E := E) (X := X) basePoint Q v ↔
      evalJacobianClass P v = evalJacobianClass Q v := by
  unfold witnessAbelJacobi
  exact sub_left_inj

/-- Endpoint swap turns `_eq_zero` into the symmetric form. -/
theorem witnessAbelJacobi_swap_eq_zero_iff
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      witnessAbelJacobi (E := E) (X := X) P basePoint v = 0 := by
  rw [witnessAbelJacobi_swap, neg_eq_zero]

end JacobianChallenge.AbelJacobi
