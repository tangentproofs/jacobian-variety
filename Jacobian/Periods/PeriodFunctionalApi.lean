import Jacobian.Periods.PeriodFunctional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Small named API around the opaque `periodPairing` -/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The period pairing sends the 0-cycle to the zero functional. -/
@[simp] theorem periodPairing_zero :
    periodPairing E X 0 = 0 :=
  (periodPairing E X).map_zero

/-- The period pairing distributes over addition of cycles. -/
theorem periodPairing_add (σ τ : IntegralOneCycle X) :
    periodPairing E X (σ + τ) =
      periodPairing E X σ + periodPairing E X τ :=
  (periodPairing E X).map_add σ τ

/-- The period pairing negates negation of cycles. -/
@[simp] theorem periodPairing_neg (σ : IntegralOneCycle X) :
    periodPairing E X (-σ) = -periodPairing E X σ :=
  (periodPairing E X).map_neg σ

/-- 0 lies in the period subgroup (immediate from `AddSubgroup`). -/
@[simp] theorem zero_mem_periodSubgroup :
    (0 : HolomorphicOneForm E X →ₗ[ℂ] ℂ) ∈ periodSubgroup E X :=
  (periodSubgroup E X).zero_mem

end JacobianChallenge.Periods
