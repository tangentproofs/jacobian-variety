import Jacobian.AbelJacobi.BaseChange
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# More identities relating `witnessAbelJacobi` and `evalJacobianClass`

Continues `BaseChange` with explicit-form identities that downstream
proofs can use without unfolding `witnessAbelJacobi`.
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
Explicit form: `witness basePoint P v + evalJacobianClass basePoint v
= evalJacobianClass P v`.
-/
theorem witnessAbelJacobi_add_basePoint_class
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v +
      evalJacobianClass basePoint v =
      evalJacobianClass P v := by
  unfold witnessAbelJacobi
  abel

/--
Symmetric: `evalJacobianClass basePoint v + witness basePoint P v
= evalJacobianClass P v`.
-/
theorem basePoint_class_add_witness
    (basePoint P : X) (v : E) :
    evalJacobianClass basePoint v +
      witnessAbelJacobi (E := E) (X := X) basePoint P v =
      evalJacobianClass P v := by
  rw [add_comm]
  exact witnessAbelJacobi_add_basePoint_class basePoint P v

/--
Translation form: shifting endpoints by a different intermediate
point and reapplying.
-/
theorem witnessAbelJacobi_chain_shift
    (basePoint P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v +
      witnessAbelJacobi (E := E) (X := X) P Q v =
      witnessAbelJacobi (E := E) (X := X) basePoint Q v :=
  witnessAbelJacobi_chain_three basePoint P Q v

/-- Self-witness recovers `evalJacobianClass P v - evalJacobianClass P v = 0`. -/
@[simp] theorem witnessAbelJacobi_left_self_eq_zero
    (P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P P v = 0 :=
  witnessAbelJacobi_self P v

end JacobianChallenge.AbelJacobi
