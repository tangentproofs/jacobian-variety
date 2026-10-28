import Jacobian.AbelJacobi.Composition
import Jacobian.AnalyticJacobian.EvalJacobianClassSmul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vec-slot sub/nsmul/zsmul + zero-class characterization for `witnessAbelJacobi`

Closes the integer-action vec-slot algebra on the Abel-Jacobi
witness, plus a `_eq_zero_iff` characterization linking the witness
to coset equality of `evalJacobianClass`.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

theorem witnessAbelJacobi_sub_vec
    (basePoint P : X) (v w : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (v - w) =
      witnessAbelJacobi (E := E) (X := X) basePoint P v -
        witnessAbelJacobi (E := E) (X := X) basePoint P w := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_sub_vec, evalJacobianClass_sub_vec]
  abel

theorem witnessAbelJacobi_nsmul_vec
    (basePoint P : X) (n : ℕ) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (n • v) =
      n • witnessAbelJacobi (E := E) (X := X) basePoint P v := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_nsmul_vec, evalJacobianClass_nsmul_vec, smul_sub]

theorem witnessAbelJacobi_zsmul_vec
    (basePoint P : X) (n : ℤ) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (n • v) =
      n • witnessAbelJacobi (E := E) (X := X) basePoint P v := by
  unfold witnessAbelJacobi
  rw [evalJacobianClass_zsmul_vec, evalJacobianClass_zsmul_vec, smul_sub]

/-- The witness vanishes iff the two endpoint classes coincide. -/
theorem witnessAbelJacobi_eq_zero_iff
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      evalJacobianClass P v = evalJacobianClass basePoint v := by
  unfold witnessAbelJacobi
  exact sub_eq_zero

end JacobianChallenge.AbelJacobi
