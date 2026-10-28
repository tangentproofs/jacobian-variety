import Jacobian.Periods.PeriodSubgroupClosure
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Integer-scalar API for the opaque `periodPairing`

`periodPairing` is an `AddMonoidHom`, so it commutes with `ℕ`/`ℤ`
scalar multiplication of the cycle. This file exposes those
named wrappers, plus the matching `… ∈ periodSubgroup` corollaries.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The period pairing commutes with `ℕ`-scalar multiplication of cycles. -/
theorem periodPairing_nsmul (n : ℕ) (σ : IntegralOneCycle X) :
    periodPairing E X (n • σ) = n • periodPairing E X σ :=
  (periodPairing E X).map_nsmul n σ

/-- The period pairing commutes with `ℤ`-scalar multiplication of cycles. -/
theorem periodPairing_zsmul (n : ℤ) (σ : IntegralOneCycle X) :
    periodPairing E X (n • σ) = n • periodPairing E X σ :=
  (periodPairing E X).map_zsmul n σ

/-- `n • periodPairing _ σ ∈ periodSubgroup` for `n : ℕ`. -/
theorem periodPairing_nsmul_mem_periodSubgroup
    (n : ℕ) (σ : IntegralOneCycle X) :
    n • periodPairing E X σ ∈ periodSubgroup E X :=
  nsmul_mem_periodSubgroup (periodPairing_mem_periodSubgroup σ) n

/-- `n • periodPairing _ σ ∈ periodSubgroup` for `n : ℤ`. -/
theorem periodPairing_zsmul_mem_periodSubgroup
    (n : ℤ) (σ : IntegralOneCycle X) :
    n • periodPairing E X σ ∈ periodSubgroup E X :=
  zsmul_mem_periodSubgroup (periodPairing_mem_periodSubgroup σ) n

end JacobianChallenge.Periods
