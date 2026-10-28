import Jacobian.Periods.PeriodSubgroupClosure
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Extensional facts about `periodSubgroup`

A small collection of carrier-set / image / range facts for
`periodSubgroup`, all immediate from the underlying
`AddSubgroup`/`AddMonoidHom.range` interface.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `periodSubgroup` as a Set equals the range of `periodPairing`. -/
theorem periodSubgroup_carrier_eq_range :
    (periodSubgroup E X : Set _) = Set.range (periodPairing E X) := by
  ext φ
  exact mem_periodSubgroup_iff φ

/-- `periodPairing` ranges into `periodSubgroup`. -/
theorem range_periodPairing_subset_periodSubgroup :
    Set.range (periodPairing E X) ⊆ (periodSubgroup E X : Set _) := by
  intro φ hφ
  rcases hφ with ⟨σ, rfl⟩
  exact periodPairing_mem_periodSubgroup σ

/--
The image of any `periodPairing` value under negation lies in
`periodSubgroup`.
-/
theorem neg_periodPairing_mem_periodSubgroup (σ : IntegralOneCycle X) :
    -periodPairing E X σ ∈ periodSubgroup E X :=
  neg_mem_periodSubgroup (periodPairing_mem_periodSubgroup σ)

/-- The sum of two `periodPairing` values lies in `periodSubgroup`. -/
theorem periodPairing_add_mem_periodSubgroup
    (σ τ : IntegralOneCycle X) :
    periodPairing E X σ + periodPairing E X τ ∈ periodSubgroup E X :=
  add_mem_periodSubgroup
    (periodPairing_mem_periodSubgroup σ)
    (periodPairing_mem_periodSubgroup τ)

end JacobianChallenge.Periods
