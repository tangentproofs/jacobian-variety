/-!
# RETIRED — not built, not imported (was `Jacobian/Periods/PeriodSubgroupZLatticeU.lean`)

Part of the universe-`u` period chain built on the **zero** period pairing
(`periodPairingComplexU`, whose chain-level integration map was the placeholder `0`). On
that pairing the period subgroup is `⊥` (`basisAlignedPeriodSubgroupConcreteU_eq_bot`), so
the "Jacobian" was all of `ℂ^g`, and the full-rank statement `h1_basis_riemannClassicalPeriodBasisU`
(gap 15) was false for `g ≥ 1`. The public `Jacobian` now uses the genuine lattice
`Jacobian/Periods/GenuinePeriodLattice.lean` (integration of holomorphic 1-forms over closed
`C¹` curves), and nothing imports this chain any more. Retired on branch `independent-repair`
(goal (b)); the sorries it carried (gaps 3, 4, 15) left the build with it.
-/

import Jacobian.Periods.BasisAlignedPeriodSubgroupU
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Universe-polymorphic period-subgroup discreteness and closedness

`Jacobian/Periods/PeriodFunctional.lean` proves discreteness of the Type-0
basis-aligned period subgroup (`periodSubgroup_isZLattice`) by exhibiting it as
the ℤ-span of `2g` ℝ-linearly independent period vectors and invoking the ZSpan
discreteness machinery. That route currently rests on a tracked Riemann-bilinear
frontier obligation (`period_functionals_ℝ_linearIndependent`), because while the
integration map of the period pairing is the placeholder `0`, the period pairing
is the zero homomorphism and the "2g independent period vectors" claim is
vacuously unavailable.

This file provides the universe-polymorphic companions for the discreteness and
closedness `FullComplexLattice` fields (C2b of the authorized full `Type u`
generalization, Option C containment). Crucially, it proves them **sorry-free**,
by a route that the Type-0 file does not take: with the integration map at its
current `0` placeholder, the universe-`u` period pairing `periodPairingComplexU`
is the zero homomorphism (`periodPairingComplexU_eq_zero`), so the universe-`u`
basis-aligned period subgroup is the trivial subgroup `⊥`
(`basisAlignedPeriodSubgroupConcreteU_eq_bot`), whose discreteness and closedness
are immediate.

This is the same vacuous content as the Type-0 side (both subgroups are currently
`{0}`), proved directly rather than through the sorry-backed full-rank route — so
it is strictly more honest, and introduces no new sorry. When the nonzero
integration frontier eventually lands (the project-wide
`singularChain_integration_from_simplex` obligation), the genuine full-rank
discreteness will replace this `⊥`-based proof on both the Type-0 and universe-`u`
sides; until then the period lattice is genuinely the trivial lattice on both.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms CategoryTheory

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/--
The universe-`u` complex-model period pairing is the zero homomorphism, since its
chain-level integration map is the placeholder `0`. Universe-polymorphic
companion to `periodPairing_eq_zero_placeholder` (PullbackNaturality.lean), with
the same descent-of-zero proof.
-/
theorem periodPairingComplexU_eq_zero (γ : IntegralOneCycleU X) :
    periodPairingComplexU X γ = 0 := by
  ext
  simp [periodPairingComplexU]
  erw [show (HomologicalComplex.sc
      (JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X) 1).descHomology _ _ = 0
      from _] ; aesop
  convert CategoryTheory.Limits.zero_of_epi_comp _ _
  exact (HomologicalComplex.cycles
    (JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X) 1)
  exact (HomologicalComplex.sc
    (JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X) 1).homologyπ
  · exact CategoryTheory.ShortComplex.instEpiHomologyπ
      (HomologicalComplex.sc (JacobianChallenge.Blueprint.Sec03.singularChainComplexZU X) 1)
  · erw [CategoryTheory.ShortComplex.π_descHomology]
    exact CategoryTheory.Limits.comp_zero

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- The range of the universe-`u` complex-model period pairing is trivial. -/
theorem periodPairingComplexU_range_eq_bot : (periodPairingComplexU X).range = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨γ, rfl⟩ := hφ
  rw [periodPairingComplexU_eq_zero]
  exact AddSubgroup.zero_mem _

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The universe-`u` basis-aligned period subgroup is trivial (current placeholder). -/
theorem basisAlignedPeriodSubgroupConcreteU_eq_bot :
    basisAlignedPeriodSubgroupConcreteU X = ⊥ := by
  unfold basisAlignedPeriodSubgroupConcreteU
  rw [periodPairingComplexU_range_eq_bot, AddSubgroup.map_bot]

/--
The universe-`u` basis-aligned period subgroup is discrete. Universe-polymorphic
companion to `basisAlignedPeriodSubgroup_isDiscrete` / `periodSubgroup_isZLattice`.
Proved sorry-free via the trivial-subgroup route (see module docstring).
-/
instance periodSubgroup_isZLatticeU :
    DiscreteTopology (basisAlignedPeriodSubgroupConcreteU X) := by
  rw [basisAlignedPeriodSubgroupConcreteU_eq_bot]
  infer_instance

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The universe-`u` basis-aligned period subgroup is closed. Universe-polymorphic
companion to `basisAlignedPeriodSubgroup_isClosed`; follows from discreteness.
-/
theorem basisAlignedPeriodSubgroupConcreteU_isClosed :
    IsClosed (basisAlignedPeriodSubgroupConcreteU X :
      Set (Fin (analyticGenus ℂ X) → ℂ)) :=
  AddSubgroup.isClosed_of_discrete

end JacobianChallenge.Periods
