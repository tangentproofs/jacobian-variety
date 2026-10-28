import Jacobian.Periods.PeriodSubgroupClosure
import Jacobian.Periods.PeriodFunctionalIntSmul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `periodSubgroup` negation iff and explicit `periodPairing`-combination membership

Iff form of negation closure plus explicit `periodPairing` closure
witnesses (sums, differences, integer scalings combined).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `-φ ∈ periodSubgroup` iff `φ ∈ periodSubgroup`. -/
theorem neg_mem_periodSubgroup_iff
    {φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ} :
    -φ ∈ periodSubgroup E X ↔ φ ∈ periodSubgroup E X :=
  (periodSubgroup E X).neg_mem_iff

/-- `-periodPairing σ ∈ periodSubgroup`. -/
theorem neg_periodPairing_mem_periodSubgroup
    (σ : IntegralOneCycle X) :
    -periodPairing E X σ ∈ periodSubgroup E X :=
  neg_mem_periodSubgroup (periodPairing_mem_periodSubgroup σ)

/-- `periodPairing σ + periodPairing τ ∈ periodSubgroup`. -/
theorem periodPairing_add_periodPairing_mem_periodSubgroup
    (σ τ : IntegralOneCycle X) :
    periodPairing E X σ + periodPairing E X τ ∈ periodSubgroup E X :=
  add_mem_periodSubgroup
    (periodPairing_mem_periodSubgroup σ)
    (periodPairing_mem_periodSubgroup τ)

/-- `periodPairing σ - periodPairing τ ∈ periodSubgroup`. -/
theorem periodPairing_sub_periodPairing_mem_periodSubgroup
    (σ τ : IntegralOneCycle X) :
    periodPairing E X σ - periodPairing E X τ ∈ periodSubgroup E X :=
  sub_mem_periodSubgroup
    (periodPairing_mem_periodSubgroup σ)
    (periodPairing_mem_periodSubgroup τ)

end JacobianChallenge.Periods
