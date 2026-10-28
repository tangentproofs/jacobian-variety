import Jacobian.Periods.IntegralOneCycleU
import Jacobian.HolomorphicForms.CompactRiemannSurface

/-!
# Universe-polymorphic H₁ ℤ-basis (tracked surface-classification obligation)

`Jacobian/Periods/PeriodFunctional.lean` proves, genuinely, that the Type-0
integral first homology of a compact connected Riemann surface admits a ℤ-basis
indexed by `Fin (2 * analyticGenus ℂ X)`
(`h1_basis_of_compact_riemann_surface`). That proof runs the full surface-
classification chain — `singularH1_iso_freeZ_of_compactOrientableSurface` →
`compactOrientableSurface_homeomorph_polygon4g` + `polygon4g_singularH1_iso_freeZ`
— built on the Type-0 singular-homology functor `singularH1 M = IntegralOneCycle M`.

This file provides the universe-polymorphic companion
`h1_basis_of_compact_riemann_surfaceU` for the universe-`u` homology
`IntegralOneCycleU X` (`Jacobian/Periods/IntegralOneCycleU.lean`), which is step
C2c-i of the authorized full `Type u` generalization of the period lattice
(Option C containment). It is the foundational prerequisite for the universe-`u`
period subgroup's full-rank `IsZLattice` content and hence for the universe-`u`
compact fundamental domain (`exists_compact_periodFundamentalDomainU`, C2c-ii) —
which the public `Jacobian (X : Type u)` charted-space/manifold/Lie transports
ultimately consume.

## Status: named tracked frontier obligation

`IntegralOneCycleU X` is built from the singular-homology functor instantiated at
universe `u` with `ULift.{u} ℤ` coefficients — a genuinely *different* object from
the Type-0 `IntegralOneCycle X` (which uses `ℤ` coefficients), with no cheap
isomorphism bridge. Reproducing the rank-`2g` freeness for `IntegralOneCycleU X`
requires re-running the surface-classification + cellular-homology argument on the
universe-`u` functor — substantial deferred infrastructure, well beyond a single
commit.

Accordingly, the remaining direct providers in this file are narrower Stage-A
and Stage-B universe-`u` obligations: the `IntegralOneCycleU` singular/cellular
H₁ bridge giving a topological-genus-indexed basis, and the analytic/topological
genus comparison for that universe-`u` homology object. The public
`h1_basis_of_compact_riemann_surfaceU` theorem is only the sorry-free reindexing
assembly, exactly mirroring the Type-0 side.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

/--
Universe-`u` topological genus measured from the universe-`u` singular homology
object `IntegralOneCycleU X`.
-/
noncomputable def topologicalGenusU
    (X : Type u) [TopologicalSpace X] : ℕ :=
  Module.finrank ℤ (IntegralOneCycleU X) / 2

/--
**Universe-`u` Stage-A surface classification + cellular H₁ provider.**
A compact connected Riemann surface `X : Type u` admits a topological-genus
indexed ℤ-basis of the universe-`u` integral 1-cycles.

This is the genuinely missing bridge: re-running the surface-classification,
cellular-homology, and singular-vs-cellular comparison for Mathlib's
`singularHomologyFunctor.{u}` with `ULift.{u} ℤ` coefficients.
-/
theorem stageA_surface_CW_basisU
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenusU X)) ℤ
      (IntegralOneCycleU X)) := by
  sorry

/--
**Universe-`u` Stage-B Hodge bridge.** The analytic genus agrees with the
topological genus measured by `IntegralOneCycleU`.

This is the universe-`u` companion of the Type-0 analytic/topological genus
comparison, with the homology side now using `ULift.{u} ℤ` coefficients.
-/
theorem stageB_analytic_eq_topologicalGenusU
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = topologicalGenusU X := by
  sorry

/--
**Universe-`u` H₁ ℤ-basis (tracked surface-classification obligation).**
A compact connected Riemann surface `X : Type u` has integral first homology
`IntegralOneCycleU X` admitting a ℤ-basis indexed by `Fin (2 * analyticGenus ℂ X)`.

Universe-polymorphic companion to the genuinely-proved Type-0
`h1_basis_of_compact_riemann_surface`. Its remaining frontier is the narrower
topological-genus basis provider `stageA_surface_CW_basisU` plus the
universe-`u` Stage-B genus comparison `stageB_analytic_eq_topologicalGenusU`;
this theorem itself only reindexes that basis.
-/
theorem h1_basis_of_compact_riemann_surfaceU
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ (IntegralOneCycleU X)) := by
  obtain ⟨b⟩ := stageA_surface_CW_basisU X
  exact ⟨b.reindex (Fin.castOrderIso (by rw [stageB_analytic_eq_topologicalGenusU])).toEquiv⟩

end JacobianChallenge.Periods
