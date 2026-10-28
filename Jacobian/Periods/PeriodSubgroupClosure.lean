import Jacobian.Periods.PeriodSubgroupApi
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Closure of `periodSubgroup` under group operations

`periodSubgroup` is an `AddSubgroup`, so it is closed under
addition, subtraction, and integer scalar multiplication. These
named wrappers expose those facts directly.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `periodSubgroup` is closed under addition. -/
theorem add_mem_periodSubgroup
    {φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (hφ : φ ∈ periodSubgroup E X) (hψ : ψ ∈ periodSubgroup E X) :
    φ + ψ ∈ periodSubgroup E X :=
  (periodSubgroup E X).add_mem hφ hψ

/-- `periodSubgroup` is closed under subtraction. -/
theorem sub_mem_periodSubgroup
    {φ ψ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (hφ : φ ∈ periodSubgroup E X) (hψ : ψ ∈ periodSubgroup E X) :
    φ - ψ ∈ periodSubgroup E X :=
  (periodSubgroup E X).sub_mem hφ hψ

/-- `periodSubgroup` is closed under natural-number scaling. -/
theorem nsmul_mem_periodSubgroup
    {φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (h : φ ∈ periodSubgroup E X) (n : ℕ) :
    n • φ ∈ periodSubgroup E X :=
  AddSubgroup.nsmul_mem _ h n

/-- `periodSubgroup` is closed under integer scaling. -/
theorem zsmul_mem_periodSubgroup
    {φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (h : φ ∈ periodSubgroup E X) (n : ℤ) :
    n • φ ∈ periodSubgroup E X :=
  AddSubgroup.zsmul_mem _ h n

end JacobianChallenge.Periods
