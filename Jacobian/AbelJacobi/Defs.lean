import Jacobian.AnalyticJacobian.NontrivialWitness
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Abel-Jacobi map

```text
witnessAbelJacobi (basePoint : X) (P : X) (v : E) : AnalyticJacobianGroup E X
  := evalJacobianClass P v - evalJacobianClass basePoint v
```
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]


noncomputable def witnessAbelJacobi
    (basePoint P : X) (v : E) : AnalyticJacobianGroup E X :=
  evalJacobianClass P v - evalJacobianClass basePoint v

/-- The witness map vanishes at the base point. -/
@[simp] theorem witnessAbelJacobi_self
    (basePoint : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint basePoint v = 0 := by
  unfold witnessAbelJacobi
  exact sub_self _

/-- The witness map is antisymmetric in the two endpoints. -/
theorem witnessAbelJacobi_swap
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v =
      -witnessAbelJacobi (E := E) (X := X) P basePoint v := by
  unfold witnessAbelJacobi
  rw [neg_sub]

/-- The witness map of a point with itself collapses. -/
theorem witnessAbelJacobi_diag (basePoint : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint basePoint v = 0 :=
  witnessAbelJacobi_self basePoint v

end JacobianChallenge.AbelJacobi
