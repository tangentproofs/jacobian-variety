import Jacobian.Periods.PeriodFunctionalApi
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# More named API around `periodSubgroup`

Continues `PeriodFunctionalApi` with sub/membership/image lemmas.
All trivial corollaries of the `AddSubgroup`/`AddMonoidHom.range`
interface, exposed as named lemmas.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The period pairing distributes over subtraction of cycles. -/
theorem periodPairing_sub (σ τ : IntegralOneCycle X) :
    periodPairing E X (σ - τ) =
      periodPairing E X σ - periodPairing E X τ :=
  (periodPairing E X).map_sub σ τ

/--
An element lies in the period subgroup iff it is in the range
of `periodPairing`.
-/
theorem mem_periodSubgroup_iff (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    φ ∈ periodSubgroup E X ↔ ∃ σ : IntegralOneCycle X, periodPairing E X σ = φ :=
  Iff.rfl

/-- The image of `periodPairing` lies in `periodSubgroup`. -/
theorem periodPairing_mem_periodSubgroup (σ : IntegralOneCycle X) :
    periodPairing E X σ ∈ periodSubgroup E X :=
  ⟨σ, rfl⟩

/--
The period subgroup is closed under negation (immediate from
`AddSubgroup`).
-/
theorem neg_mem_periodSubgroup
    {φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ}
    (h : φ ∈ periodSubgroup E X) : -φ ∈ periodSubgroup E X :=
  (periodSubgroup E X).neg_mem h

end JacobianChallenge.Periods
