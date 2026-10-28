import Jacobian.AbelJacobi.Defs
import Jacobian.AnalyticJacobian.EvalJacobianClassOps
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Composition / endpoint algebra for `witnessAbelJacobi`

- chain via an intermediate point: `(basePoint ⇒ Q) - (basePoint ⇒ P) = (P ⇒ Q)`
- vec-zero collapse
- vec-slot additivity in the path-symmetric form
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
Chain rule: passing through an intermediate point cancels:
`witness basePoint Q - witness basePoint P = witness P Q`.
-/
theorem witnessAbelJacobi_chain
    (basePoint P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint Q v -
      witnessAbelJacobi (E := E) (X := X) basePoint P v =
      witnessAbelJacobi (E := E) (X := X) P Q v := by
  unfold witnessAbelJacobi
  abel

/-- The witness vanishes on the zero tangent vector. -/
theorem witnessAbelJacobi_zero_vec
    (basePoint P : X) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (0 : E) = 0 := by
  unfold witnessAbelJacobi
  rw [show evalJacobianClass P (0 : E) = 0 from
        evalJacobianClass_zero_vec P]
  rw [show evalJacobianClass basePoint (0 : E) = 0 from
        evalJacobianClass_zero_vec basePoint]
  exact sub_self _

/-- The witness is additive in the tangent-vector slot. -/
theorem witnessAbelJacobi_add_vec
    (basePoint P : X) (v w : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (v + w) =
      witnessAbelJacobi (E := E) (X := X) basePoint P v +
        witnessAbelJacobi (E := E) (X := X) basePoint P w := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_add_vec, evalJacobianClass_add_vec]
  abel

/-- The witness negates over negation in the tangent-vector slot. -/
theorem witnessAbelJacobi_neg_vec
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (-v) =
      -witnessAbelJacobi (E := E) (X := X) basePoint P v := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_neg_vec, evalJacobianClass_neg_vec]
  abel

end JacobianChallenge.AbelJacobi
