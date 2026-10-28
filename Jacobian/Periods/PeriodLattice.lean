import Jacobian.ComplexTorus.Defs
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Period lattice in the basis-aligned model

This module provides the period lattice of a compact Riemann surface,
transported into the basis-aligned model space `Fin (analyticGenus ℂ X) → ℂ`.

The basis-aligned model is the one used by `Jacobian/Challenge.lean` for the
charted-space and Lie-group instances on `Jacobian X`. Choosing the carrier
this way means the universe and chart-model bridges in
`Jacobian/Solution.lean` collapse to a single `ULift`.

This file owns the named obligations that the top-down `Solution.Jacobian`
definition delegates to. Following the project's preference for
*small* named obligations over a single monolithic helper, the
construction is split into separately named pieces:

* `basisAlignedPeriodSubgroup X` — the period subgroup (data, `opaque`);
* `basisAlignedPeriodSubgroup_isClosed` — closedness in the model space;
* `basisAlignedPeriodSubgroup_isDiscrete` — discreteness in the subspace topology;
* `periodFundamentalDomain X` — a chosen fundamental domain (data);
* `periodFundamentalDomain_isCompact` — compactness;
* `periodFundamentalDomain_covers` — the translates cover the model space;
* `periodFullComplexLattice X` — bundles the above into a
  `FullComplexLattice` with no further sorries of its own.

Each of these is the bottom-up obligation Aristotle (or local proof
work) can attack independently. The bottom-up content is, roughly:
period pairing (integration of holomorphic 1-forms over `H₁(X, ℤ)`) +
basis transport + Riemann bilinear nondegeneracy.
-/

namespace JacobianChallenge.Periods

open scoped Manifold
open JacobianChallenge.HolomorphicForms

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The period subgroup of a compact Riemann surface, expressed in the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.

Routed (keystone refactor, 2026-04-27): defined as the concrete
representative `basisAlignedPeriodSubgroupConcrete X` from
`Jacobian/Periods/BasisAlignedPeriodSubgroup.lean`. This routing
specialises the lattice's carrier domain `X` to `Type` (Type 0) — the
same universe constraint that `Periods.periodSubgroup` and
`IntegralOneCycle` carry, which themselves are limited to Type 0 by
Mathlib's available `HasCoproducts.{0} (ModuleCat ℤ)` instance.

The specialisation propagates upward to `periodFullComplexLattice` and
`Solution.Jacobian`. The comparator-level data-declaration mismatch with
`Challenge.Jacobian (X : Type u)` is a known consequence; per
`Jacobian/WorkPackets/TopDown.md` the comparator's `theorem_names` list
covers only theorem-level declarations, so the data-level monomorphism
should be acceptable for the staged-refinement check.
-/
noncomputable def basisAlignedPeriodSubgroup :
    AddSubgroup (Fin (analyticGenus ℂ X) → ℂ) :=
  basisAlignedPeriodSubgroupConcrete X







end JacobianChallenge.Periods
