import Jacobian.AnalyticJacobian.MkPeriodPairingSmul
import Jacobian.AnalyticJacobian.EvalJacobianClass
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `evalJacobianClass` invariance under `periodPairing` adjustments

If `evalLinearMap x v = φ + periodPairing E X σ`, then
`evalJacobianClass x v = mk E X φ`. These four lemmas package the
common forms of that invariance.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
If `evalLinearMap x v` differs from `φ` by a `periodPairing` value,
the corresponding Jacobian class equals `mk φ`.
-/
theorem evalJacobianClass_eq_mk_of_evalLinearMap_eq_add_periodPairing
    (x : X) (v : E) (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ)
    (σ : IntegralOneCycle X)
    (h : evalLinearMap x v = φ + periodPairing E X σ) :
    evalJacobianClass (E := E) (X := X) x v = mk E X φ := by
  rw [evalJacobianClass_def, h, mk_add_periodPairing]

/-- Same with subtraction. -/
theorem evalJacobianClass_eq_mk_of_evalLinearMap_eq_sub_periodPairing
    (x : X) (v : E) (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ)
    (σ : IntegralOneCycle X)
    (h : evalLinearMap x v = φ - periodPairing E X σ) :
    evalJacobianClass (E := E) (X := X) x v = mk E X φ := by
  rw [evalJacobianClass_def, h, mk_sub_periodPairing]

/--
If `evalLinearMap x v` is a `periodPairing` value, the Jacobian
class is `0`.
-/
theorem evalJacobianClass_eq_zero_of_evalLinearMap_eq_periodPairing
    (x : X) (v : E) (σ : IntegralOneCycle X)
    (h : evalLinearMap x v = periodPairing E X σ) :
    evalJacobianClass (E := E) (X := X) x v = 0 := by
  rw [evalJacobianClass_def, h, mk_periodPairing_eq_zero]

/--
If `evalLinearMap x v` is `n • periodPairing E X σ`, the Jacobian
class is `0`.
-/
theorem evalJacobianClass_eq_zero_of_evalLinearMap_eq_zsmul_periodPairing
    (x : X) (v : E) (n : ℤ) (σ : IntegralOneCycle X)
    (h : evalLinearMap x v = n • periodPairing E X σ) :
    evalJacobianClass (E := E) (X := X) x v = 0 := by
  rw [evalJacobianClass_def, h, mk_zsmul_periodPairing]

end JacobianChallenge.AnalyticJacobian
