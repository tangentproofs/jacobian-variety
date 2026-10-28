import Jacobian.Periods.PeriodFundamentalDomainU
import Jacobian.Periods.BasisAlignedPeriodSubgroupU
import Jacobian.Periods.PeriodSubgroupZLatticeU
import Jacobian.ComplexTorus.Defs

/-!
# Universe-polymorphic period `FullComplexLattice`

`Jacobian/Periods/PeriodLattice.lean` bundles the Type-0 period subgroup, its
discreteness/closedness, and a compact fundamental domain into
`periodFullComplexLattice (X : Type) : ComplexTorus.FullComplexLattice
(Fin (analyticGenus ℂ X) → ℂ)`.

This file provides the universe-polymorphic capstone
`periodFullComplexLatticeU (X : Type u)` (C3 of the authorized full `Type u`
generalization, Option C containment), assembling the six universe-`u`
`FullComplexLattice` fields built across C2a–C2c-iii:

* `subgroup` — `basisAlignedPeriodSubgroupConcreteU` (C2a)
* `isClosed` — `basisAlignedPeriodSubgroupConcreteU_isClosed` (C2b)
* `isDiscrete` — `periodSubgroup_isZLatticeU` (C2b)
* `fundamentalDomain` / `_isCompact` / `_covers` — from
  `exists_compact_periodFundamentalDomainU` (C2c-iii)

With this in hand, the public `Jacobian (X : Type u)` def in
`Jacobian/Solution.lean` can be wired as
`ULift.{u} (ComplexTorus.quotient (Fin (genus X) → ℂ) (periodFullComplexLatticeU X))`
— the universe-polymorphic "Route 1" that was the original goal of this project,
which previously failed to type-check because `periodFullComplexLattice` demanded
`X : Type 0`. No new sorry is introduced here; the assembly consumes the inherited
Periods layer-frontier obligations only transitively, exactly as the Type-0
`periodFullComplexLattice` does.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/-- A compact fundamental domain for the universe-`u` period subgroup, in the
basis-aligned model. Universe-polymorphic companion to `periodFundamentalDomain`. -/
noncomputable def periodFundamentalDomainU : Set (Fin (analyticGenus ℂ X) → ℂ) :=
  (exists_compact_periodFundamentalDomainU X).choose

/-- The universe-`u` fundamental domain is compact. -/
theorem periodFundamentalDomainU_isCompact : IsCompact (periodFundamentalDomainU X) :=
  (exists_compact_periodFundamentalDomainU X).choose_spec.1

/-- The universe-`u` fundamental-domain translates cover the model space. -/
theorem periodFundamentalDomainU_covers :
    ∀ v : Fin (analyticGenus ℂ X) → ℂ,
      ∃ g ∈ basisAlignedPeriodSubgroupConcreteU X, v - g ∈ periodFundamentalDomainU X :=
  (exists_compact_periodFundamentalDomainU X).choose_spec.2

/--
The period lattice of a compact Riemann surface `X : Type u`, bundled as a
`FullComplexLattice` in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.
Universe-polymorphic capstone companion to `periodFullComplexLattice`.
-/
noncomputable def periodFullComplexLatticeU :
    JacobianChallenge.ComplexTorus.FullComplexLattice
      (Fin (analyticGenus ℂ X) → ℂ) where
  subgroup := basisAlignedPeriodSubgroupConcreteU X
  isClosed := basisAlignedPeriodSubgroupConcreteU_isClosed X
  isDiscrete := periodSubgroup_isZLatticeU X
  fundamentalDomain := periodFundamentalDomainU X
  fundamentalDomain_isCompact := periodFundamentalDomainU_isCompact X
  fundamentalDomain_covers := periodFundamentalDomainU_covers X

end JacobianChallenge.Periods
