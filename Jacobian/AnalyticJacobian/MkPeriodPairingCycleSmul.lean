import Jacobian.AnalyticJacobian.MkPeriodPairingCycle
import Jacobian.Periods.PeriodFunctionalIntSmul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `mk` ∘ `periodPairing` on integer-scaled cycles

Continues `MkPeriodPairingCycle` with cycle-side `ℕ`/`ℤ`-scaling.
All four lemmas reduce via `mk_periodPairing_eq_zero` (or via the
new `periodPairing_{n,z}smul` bridge plus `mk_{n,z}smul_periodPairing`).
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk` of `periodPairing (n • σ)` for `n : ℕ` is `0`. -/
@[simp] theorem mk_periodPairing_nsmul_cycle
    (n : ℕ) (σ : IntegralOneCycle X) :
    mk E X (periodPairing E X (n • σ)) = 0 :=
  mk_periodPairing_eq_zero (n • σ)

/-- `mk` of `periodPairing (n • σ)` for `n : ℤ` is `0`. -/
@[simp] theorem mk_periodPairing_zsmul_cycle
    (n : ℤ) (σ : IntegralOneCycle X) :
    mk E X (periodPairing E X (n • σ)) = 0 :=
  mk_periodPairing_eq_zero (n • σ)

/-- Adding `periodPairing (n • σ)` for `n : ℕ` doesn't change `mk`. -/
@[simp] theorem mk_add_periodPairing_nsmul_cycle
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (n : ℕ) (σ : IntegralOneCycle X) :
    mk E X (φ + periodPairing E X (n • σ)) = mk E X φ := by
  rw [mk_add, mk_periodPairing_nsmul_cycle, add_zero]

/-- Adding `periodPairing (n • σ)` for `n : ℤ` doesn't change `mk`. -/
@[simp] theorem mk_add_periodPairing_zsmul_cycle
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) (n : ℤ) (σ : IntegralOneCycle X) :
    mk E X (φ + periodPairing E X (n • σ)) = mk E X φ := by
  rw [mk_add, mk_periodPairing_zsmul_cycle, add_zero]

end JacobianChallenge.AnalyticJacobian
