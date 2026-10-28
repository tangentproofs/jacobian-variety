import Jacobian.AnalyticJacobian.MkExt
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Membership / kernel lemmas for `mk`

Continues `MkExt` with criteria for `mk` to vanish on functionals
that lie in `periodSubgroup` (the kernel of the quotient projection).
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- A functional in `periodSubgroup` projects to `0`. -/
theorem mk_eq_zero_of_mem_periodSubgroup
    {φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (h : φ ∈ periodSubgroup E X) : mk E X φ = 0 :=
  (mk_eq_zero_iff φ).mpr h

/-- The kernel of `mk` is exactly `periodSubgroup`. -/
theorem mk_eq_zero_iff_mem_periodSubgroup
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = 0 ↔ φ ∈ periodSubgroup E X :=
  mk_eq_zero_iff φ

/-- `mk` of a `periodPairing` value is `0`. -/
@[simp] theorem mk_periodPairing_eq_zero
    (σ : IntegralOneCycle X) :
    mk E X (periodPairing E X σ) = 0 :=
  mk_eq_zero_of_mem_periodSubgroup (periodPairing_mem_periodSubgroup σ)

/--
Two functionals project to the same class iff their difference
lies in the period subgroup (alternative form of `mk_eq_mk_iff`
via `sub_mem`).
-/
theorem mk_eq_mk_iff_sub_mem
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = mk E X ψ ↔ φ - ψ ∈ periodSubgroup E X := by
  rw [show φ - ψ = -(- φ + ψ) by abel, neg_mem_iff]
  rw [mk_eq_mk_iff]

end JacobianChallenge.AnalyticJacobian
