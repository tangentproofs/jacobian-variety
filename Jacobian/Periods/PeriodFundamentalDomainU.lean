import Jacobian.Periods.PeriodVectorsLIU
import Jacobian.Periods.PeriodSubgroupZLatticeU
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Universe-polymorphic period `IsZLattice` and compact fundamental domain

`Jacobian/Periods/PeriodFunctional.lean` (lines 989–1140) promotes the Type-0
basis-aligned period subgroup to a `Submodule ℤ`, equips it with the
`DiscreteTopology` and `IsZLattice ℝ` instances, and derives the existence of a
compact fundamental domain whose subgroup-translates cover the model space.

This file mirrors that block at `Type u` (C2c-iii of the authorized full `Type u`
generalization, Option C containment), supplying the last three
`FullComplexLattice` fields needed by `periodFullComplexLatticeU` (C3):
`fundamentalDomain`, `fundamentalDomain_isCompact`, `fundamentalDomain_covers`.
Together with the discreteness/closedness from C2b
(`Jacobian/Periods/PeriodSubgroupZLatticeU.lean`), this completes all six lattice
fields at `Type u`.

Every declaration here is a verbatim mirror of its Type-0 original. No new sorry
is introduced: the `IsZLattice` `span_top` field consumes the universe-`u`
`periodSubgroup_spans_realU` (C2c-ii), which transitively rests on the inherited
Riemann-bilinear and H₁-basis Periods layer-frontier obligations
(`riemann_classical_real_LI_inputU`, `h1_basis_of_compact_riemann_surfaceU`) —
exactly as the Type-0 `basisAlignedPeriodSubmoduleℤ_isZLattice` rests on the
Type-0 `periodSubgroup_spans_real`. These are NOT public-block sorries and NOT
axioms.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The universe-`u` basis-aligned period subgroup promoted to a `Submodule ℤ`.
Universe-polymorphic companion to `basisAlignedPeriodSubmoduleℤ`.
-/
noncomputable def basisAlignedPeriodSubmoduleℤU :
    Submodule ℤ (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.toIntSubmodule (basisAlignedPeriodSubgroupConcreteU X)

/--
`DiscreteTopology` for the `Submodule ℤ`-promoted universe-`u` period subgroup,
transported from `periodSubgroup_isZLatticeU` (C2b). Universe-polymorphic
companion to `basisAlignedPeriodSubmoduleℤ_discreteTopology`.
-/
noncomputable instance basisAlignedPeriodSubmoduleℤU_discreteTopology :
    DiscreteTopology (basisAlignedPeriodSubmoduleℤU X) := by
  exact @DiscreteTopology.of_continuous_injective _ _ _ _
    (periodSubgroup_isZLatticeU X) _
    (continuous_induced_rng.mpr continuous_subtype_val)
    (fun _ _ h => Subtype.ext (congr_arg Subtype.val h))

/--
`IsZLattice ℝ` for the `Submodule ℤ`-promoted universe-`u` period subgroup.
The `span_top` field reduces to `periodSubgroup_spans_realU` (C2c-ii) after
identifying carriers via `AddSubgroup.coe_toIntSubmodule`. Universe-polymorphic
companion to `basisAlignedPeriodSubmoduleℤ_isZLattice`.
-/
noncomputable instance basisAlignedPeriodSubmoduleℤU_isZLattice :
    IsZLattice ℝ (basisAlignedPeriodSubmoduleℤU X) where
  span_top := by
    exact periodSubgroup_spans_realU X

/--
Existence of a compact fundamental domain for the universe-`u` basis-aligned
period subgroup. Universe-polymorphic companion to
`exists_compact_periodFundamentalDomain`: the closure of the `ZSpan` fundamental
domain against the real basis lifted from a ℤ-basis of the lattice is compact
(bounded in a finite-dim space) and covers via the `ZSpan.floor`/`fract`
decomposition.
-/
theorem exists_compact_periodFundamentalDomainU :
    ∃ D : Set (Fin (analyticGenus ℂ X) → ℂ),
      IsCompact D ∧
      ∀ v : Fin (analyticGenus ℂ X) → ℂ,
        ∃ g ∈ (basisAlignedPeriodSubgroupConcreteU X :
          AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)),
          v - g ∈ D := by
  haveI : DiscreteTopology (basisAlignedPeriodSubmoduleℤU X) :=
    basisAlignedPeriodSubmoduleℤU_discreteTopology X
  haveI : IsZLattice ℝ (basisAlignedPeriodSubmoduleℤU X) :=
    basisAlignedPeriodSubmoduleℤU_isZLattice X
  haveI := ZLattice.module_free ℝ (basisAlignedPeriodSubmoduleℤU X)
  haveI := ZLattice.module_finite ℝ (basisAlignedPeriodSubmoduleℤU X)
  let bℤ : Module.Basis _ ℤ (basisAlignedPeriodSubmoduleℤU X) :=
    Module.Free.chooseBasis ℤ _
  let bR : Module.Basis _ ℝ (Fin (analyticGenus ℂ X) → ℂ) :=
    bℤ.ofZLatticeBasis ℝ _
  refine ⟨closure (ZSpan.fundamentalDomain bR), ?_, ?_⟩
  · exact (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  · intro v
    refine ⟨(ZSpan.floor bR v : Fin _ → ℂ), ?_, ?_⟩
    · have hmem_span : (ZSpan.floor bR v : Fin _ → ℂ) ∈
          (Submodule.span ℤ (Set.range bR) : Submodule ℤ _) :=
        (ZSpan.floor bR v).property
      have hSub : (basisAlignedPeriodSubmoduleℤU X)
            = Submodule.span ℤ (Set.range bR) :=
        (Module.Basis.ofZLatticeBasis_span (K := ℝ) (b := bℤ)).symm
      have hSubgroup :
          (basisAlignedPeriodSubmoduleℤU X).toAddSubgroup =
          (Submodule.span ℤ (Set.range bR)).toAddSubgroup :=
        congrArg Submodule.toAddSubgroup hSub
      rw [show (basisAlignedPeriodSubgroupConcreteU X) =
          (basisAlignedPeriodSubmoduleℤU X).toAddSubgroup
        from (AddSubgroup.toIntSubmodule_toAddSubgroup _).symm, hSubgroup]
      exact hmem_span
    · have hfract : v - (ZSpan.floor bR v : Fin _ → ℂ) = ZSpan.fract bR v := by
        rw [ZSpan.fract_apply]
      rw [hfract]
      exact subset_closure (ZSpan.fract_mem_fundamentalDomain bR v)

end JacobianChallenge.Periods
