/-!
# RETIRED — not built, not imported (was `Jacobian/Periods/PeriodVectorsLIU.lean`)

Part of the universe-`u` period chain built on the **zero** period pairing
(`periodPairingComplexU`, whose chain-level integration map was the placeholder `0`). On
that pairing the period subgroup is `⊥` (`basisAlignedPeriodSubgroupConcreteU_eq_bot`), so
the "Jacobian" was all of `ℂ^g`, and the full-rank statement `h1_basis_riemannClassicalPeriodBasisU`
(gap 15) was false for `g ≥ 1`. The public `Jacobian` now uses the genuine lattice
`Jacobian/Periods/GenuinePeriodLattice.lean` (integration of holomorphic 1-forms over closed
`C¹` curves), and nothing imports this chain any more. Retired on branch `independent-repair`
(goal (b)); the sorries it carried (gaps 3, 4, 15) left the build with it.
-/

import Jacobian.Periods.H1BasisU
import Jacobian.Periods.BasisAlignedPeriodSubgroupU
import Jacobian.Periods.PeriodFunctionalU
import Jacobian.Periods.PeriodSpanHelpers
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv

/-!
# Universe-polymorphic period-vector independence and spanning

`Jacobian/Periods/PeriodFunctional.lean` builds the full-rank content of the
Type-0 period lattice through the chain
`riemann_classical_real_LI_input` → `period_functionals_ℝ_linearIndependent`
→ `period_vectors_linearIndependent_of_symplectic` →
`periodVectors_linearIndependent` → `periodSubgroup_spans_real`.

This file mirrors that chain at `Type u` for the universe-`u` period subgroup
(C2c-ii of the authorized full `Type u` generalization, Option C containment),
ending at the universe-`u` spanning fact `periodSubgroup_spans_realU`. With this
in hand, the universe-`u` `IsZLattice ℝ` and compact fundamental domain (C2c-iii)
can be assembled, completing the `FullComplexLattice` fields for the public
`Jacobian (X : Type u)`.

## Frontier obligation

The remaining frontier is the universe-`u` companion to the accepted Type-0
period-basis provider: an H₁ basis supplied by
`h1_basis_of_compact_riemann_surfaceU` must be the classical symplectic period
basis for which Riemann bilinear nondegeneracy / Hodge positivity and Stokes on
the fundamental polygon give basis-aligned period-coordinate independence.

That missing classical/geometric proof is recorded as the narrow provider
`h1_basis_riemannClassicalPeriodBasisU`, not as a broad arbitrary-injective
period-independence assertion.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
**Universe-`u` classical period-basis predicate.** A family of lifted integral
cycles carries the canonical/symplectic period-basis input needed by the
Riemann-bilinear/Hodge-positivity argument.
-/
structure RiemannClassicalPeriodBasisU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X) : Prop where
  periodCoordinate_linearIndependent :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairingComplexU X) (σ i)))

/--
**Universe-`u` classical period-basis provider for an H₁ basis.** This is the
narrow remaining Riemann-bilinear frontier: a concrete H₁ basis is the
classical/symplectic period basis with nondegenerate basis-aligned coordinates.
-/
theorem h1_basis_riemannClassicalPeriodBasisU
    (B : Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ
      (IntegralOneCycleU X)) :
    RiemannClassicalPeriodBasisU X (fun i => B i) := by
  sorry

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
**Riemann-bilinear ℝ-linear-independence input (universe-`u`).** The period
functionals `periodPairingComplexU X ∘ σ` are ℝ-linearly independent once `σ`
is known to be a classical/symplectic period basis.
-/
theorem riemann_classical_real_LI_inputU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (_hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasisU X σ) :
    LinearIndependent ℝ
      (fun i => (periodPairingComplexU X) (σ i)) := by
  let e := (holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ
  have hcoords :
      LinearIndependent ℝ (e.symm.toLinearMap ∘
        fun i => (holomorphicOneFormDualEquiv ℂ X)
          ((periodPairingComplexU X) (σ i))) :=
    hσ_classical.periodCoordinate_linearIndependent.map'
      e.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hfun :
      (e.symm.toLinearMap ∘ fun i => (holomorphicOneFormDualEquiv ℂ X)
          ((periodPairingComplexU X) (σ i)))
        = fun i => (periodPairingComplexU X) (σ i) := by
    funext i
    change e.symm (e ((periodPairingComplexU X) (σ i))) =
      (periodPairingComplexU X) (σ i)
    exact e.symm_apply_apply ((periodPairingComplexU X) (σ i))
  rw [hfun] at hcoords
  exact hcoords

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The period functionals `periodPairingComplexU X ∘ σ` are ℝ-linearly independent
in the ℂ-linear dual `HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ`. Universe-`u` companion to
`period_functionals_ℝ_linearIndependent`.
-/
theorem period_functionals_ℝ_linearIndependentU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasisU X σ) :
    LinearIndependent ℝ
      (fun i => (periodPairingComplexU X) (σ i)) :=
  riemann_classical_real_LI_inputU X σ hσ hσ_classical

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The period vectors `dualEquiv ∘ periodPairingComplexU X ∘ σ` are ℝ-linearly
independent in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.
Universe-`u` companion to `period_vectors_linearIndependent_of_symplectic`;
transports `period_functionals_ℝ_linearIndependentU` through the dual equivalence.
-/
theorem period_vectors_linearIndependent_of_symplecticU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X)
    (hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasisU X σ) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairingComplexU X) (σ i))) :=
  (period_functionals_ℝ_linearIndependentU X σ hσ hσ_classical).map'
    ((holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

/--
A compact connected Riemann surface `X : Type u` has `2g` integral 1-cycles in
`IntegralOneCycleU X` forming an injective family. Universe-`u` companion to
`symplectic_basis_of_cycles`; extracted from the universe-`u` H₁ basis (C2c-i).
-/
theorem symplectic_basis_of_cyclesU :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X),
      Function.Injective σ := by
  obtain ⟨b⟩ := h1_basis_of_compact_riemann_surfaceU X
  exact ⟨b, b.linearIndependent.injective⟩

/--
The selected universe-`u` H₁ basis also carries the classical period-basis
predicate needed for the Riemann-bilinear rank assembly.
-/
theorem symplectic_basis_of_cycles_riemannClassicalPeriodBasisU :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X),
      Function.Injective σ ∧ RiemannClassicalPeriodBasisU X σ := by
  obtain ⟨B⟩ := h1_basis_of_compact_riemann_surfaceU X
  exact ⟨fun i => B i, B.linearIndependent.injective,
    h1_basis_riemannClassicalPeriodBasisU X B⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Each period vector lies in the universe-`u` basis-aligned period subgroup.
Universe-`u` companion to `period_vectors_mem_subgroup`.
-/
theorem period_vectors_mem_subgroupU
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycleU X) :
    ∀ i, (holomorphicOneFormDualEquiv ℂ X) ((periodPairingComplexU X) (σ i))
      ∈ (basisAlignedPeriodSubgroupConcreteU X :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := fun i =>
  AddSubgroup.mem_map_of_mem _ (AddMonoidHom.mem_range.mpr ⟨σ i, rfl⟩)

/--
There exist `2g` ℝ-linearly independent vectors lying in the universe-`u`
basis-aligned period subgroup. Universe-`u` companion to
`periodVectors_linearIndependent`.
-/
theorem periodVectors_linearIndependentU :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      ∀ i, b i ∈ (basisAlignedPeriodSubgroupConcreteU X :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  obtain ⟨σ, hσ, hσ_classical⟩ := symplectic_basis_of_cycles_riemannClassicalPeriodBasisU X
  exact ⟨fun i => (holomorphicOneFormDualEquiv ℂ X) ((periodPairingComplexU X) (σ i)),
         period_vectors_linearIndependent_of_symplecticU X σ hσ hσ_classical,
         period_vectors_mem_subgroupU X σ⟩

/--
The universe-`u` basis-aligned period subgroup spans the full ℝ-vector space
`Fin (analyticGenus ℂ X) → ℂ`. Universe-`u` companion to `periodSubgroup_spans_real`;
the second half of the `IsZLattice ℝ` content. Uses the pure helper
`span_real_eq_top_of_subset_linearIndependent` as-is.
-/
theorem periodSubgroup_spans_realU :
    Submodule.span ℝ
      ((basisAlignedPeriodSubgroupConcreteU X :
        AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
        Set (Fin (analyticGenus ℂ X) → ℂ))
      = ⊤ := by
  obtain ⟨b, hli, hmem⟩ := periodVectors_linearIndependentU X
  exact span_real_eq_top_of_subset_linearIndependent
    (analyticGenus ℂ X)
    ((basisAlignedPeriodSubgroupConcreteU X :
      AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
      Set (Fin (analyticGenus ℂ X) → ℂ))
    b hli (Set.range_subset_iff.mpr hmem)

end JacobianChallenge.Periods
