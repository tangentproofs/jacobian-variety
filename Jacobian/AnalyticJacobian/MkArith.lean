import Jacobian.AnalyticJacobian.MkMembership
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Arithmetic identities for `mk`

A few additional convenience lemmas around `mk_eq_mk_iff` /
`mk_eq_zero_iff` covering negation/addition combinations.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `mk φ = -mk ψ` iff `φ + ψ ∈ periodSubgroup`. -/
theorem mk_eq_neg_iff_add_mem
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = -mk E X ψ ↔ φ + ψ ∈ periodSubgroup E X := by
  rw [show (-mk E X ψ : AnalyticJacobianGroup E X) = mk E X (-ψ) from
    (mk_neg ψ).symm]
  rw [mk_eq_mk_iff_sub_mem]
  constructor
  · intro h
    have : φ - -ψ = φ + ψ := by abel
    rwa [this] at h
  · intro h
    have : φ - -ψ = φ + ψ := by abel
    rw [this]; exact h

/-- `-mk φ = mk ψ` iff `φ + ψ ∈ periodSubgroup`. -/
theorem neg_mk_eq_iff_add_mem
    (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    -mk E X φ = mk E X ψ ↔ φ + ψ ∈ periodSubgroup E X := by
  rw [eq_comm, mk_eq_neg_iff_add_mem, add_comm]

/-- `mk` of `φ + ψ` decomposes as the sum of `mk` projections. -/
theorem mk_add_eq (φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X (φ + ψ) = mk E X φ + mk E X ψ :=
  mk_add φ ψ

/-- The zero class can always be written as `mk 0`. -/
theorem zero_eq_mk_zero :
    (0 : AnalyticJacobianGroup E X) =
      mk E X (0 : HolomorphicOneForm E X →ₗ[ℂ] ℂ) := by
  rw [mk_zero]

end JacobianChallenge.AnalyticJacobian
