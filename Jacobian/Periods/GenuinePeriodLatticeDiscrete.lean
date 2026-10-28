import Jacobian.Periods.GenuinePeriodLattice
import Jacobian.Surface.PeriodDiscrete

/-!
# The period lattice is a full lattice

Discreteness of the period subgroup (`periodLattice_discrete`, proved in
`Jacobian/Surface/PeriodDiscrete.lean`), and the bundled lattice `genuinePeriodLattice`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X] [T2Space X] [CompactSpace X] [ConnectedSpace X]

/--
**The period lattice is discrete.** For a compact connected Riemann surface the period
subgroup `Λ ⊆ ℂ^g` is discrete (`JacobianChallenge.Surface.FChain.periodLattice_discrete'`):
for closed chains `γ, δ`, `Im ∫_δ ν_γ ∈ π ℤ`, where `ν_γ` is the holomorphic form with
`∫ ν̄_γ ∧ ω = π ∫_γ ω`; this real bilinear form is non-degenerate, and `Λ` spans `ℂ^g`.
-/
theorem periodLattice_discrete : DiscreteTopology (genuinePeriodSubgroup X) :=
  JacobianChallenge.Surface.FChain.periodLattice_discrete'

/-- The period subgroup is a full lattice: discrete (`periodLattice_discrete`) and spanning
(`periodLattice_span`). -/
theorem periodLattice_discrete_and_span :
    DiscreteTopology (genuinePeriodSubgroup X) ∧
      Submodule.span ℝ (genuinePeriodSubgroup X : Set (Fin (analyticGenus ℂ X) → ℂ)) = ⊤ :=
  ⟨periodLattice_discrete X, periodLattice_span X⟩

/-- The period subgroup as a `ℤ`-submodule. -/
noncomputable def genuinePeriodSubmodule : Submodule ℤ (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.toIntSubmodule (genuinePeriodSubgroup X)

instance genuinePeriodSubgroup_discrete : DiscreteTopology (genuinePeriodSubgroup X) :=
  (periodLattice_discrete_and_span X).1

instance genuinePeriodSubmodule_discrete : DiscreteTopology (genuinePeriodSubmodule X) :=
  (periodLattice_discrete_and_span X).1

instance genuinePeriodSubmodule_isZLattice : IsZLattice ℝ (genuinePeriodSubmodule X) where
  span_top := (periodLattice_discrete_and_span X).2

/--
A compact fundamental domain for the period lattice: the closure of the parallelepiped
spanned by a `ℤ`-basis of `Λ` (which exists because `Λ` is a full lattice).
-/
theorem exists_compact_genuinePeriodFundamentalDomain :
    ∃ D : Set (Fin (analyticGenus ℂ X) → ℂ),
      IsCompact D ∧
      ∀ v : Fin (analyticGenus ℂ X) → ℂ, ∃ g ∈ genuinePeriodSubgroup X, v - g ∈ D := by
  haveI := ZLattice.module_free ℝ (genuinePeriodSubmodule X)
  haveI := ZLattice.module_finite ℝ (genuinePeriodSubmodule X)
  let bℤ : Module.Basis _ ℤ (genuinePeriodSubmodule X) := Module.Free.chooseBasis ℤ _
  let bR : Module.Basis _ ℝ (Fin (analyticGenus ℂ X) → ℂ) := bℤ.ofZLatticeBasis ℝ _
  refine ⟨closure (ZSpan.fundamentalDomain bR),
    (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure, fun v => ?_⟩
  refine ⟨(ZSpan.floor bR v : Fin _ → ℂ), ?_, ?_⟩
  · have hmem : (ZSpan.floor bR v : Fin _ → ℂ) ∈ Submodule.span ℤ (Set.range bR) :=
      (ZSpan.floor bR v).property
    have hSub : genuinePeriodSubmodule X = Submodule.span ℤ (Set.range bR) :=
      (Module.Basis.ofZLatticeBasis_span (K := ℝ) (b := bℤ)).symm
    exact (SetLike.ext_iff.mp hSub _).mpr hmem
  · rw [show v - (ZSpan.floor bR v : Fin _ → ℂ) = ZSpan.fract bR v from
      (ZSpan.fract_apply bR v).symm]
    exact subset_closure (ZSpan.fract_mem_fundamentalDomain bR v)

/--
**The period lattice of a compact Riemann surface**, bundled as a
`ComplexTorus.FullComplexLattice` in the basis-aligned model `ℂ^g`. Its carrier is the
genuine `genuinePeriodSubgroup X`; discreteness and cocompactness come from
`periodLattice_discrete_and_span`.
-/
noncomputable def genuinePeriodLattice :
    JacobianChallenge.ComplexTorus.FullComplexLattice (Fin (analyticGenus ℂ X) → ℂ) where
  subgroup := genuinePeriodSubgroup X
  isClosed := AddSubgroup.isClosed_of_discrete
  isDiscrete := genuinePeriodSubgroup_discrete X
  fundamentalDomain := (exists_compact_genuinePeriodFundamentalDomain X).choose
  fundamentalDomain_isCompact := (exists_compact_genuinePeriodFundamentalDomain X).choose_spec.1
  fundamentalDomain_covers := (exists_compact_genuinePeriodFundamentalDomain X).choose_spec.2

@[simp] theorem genuinePeriodLattice_subgroup :
    (genuinePeriodLattice X).subgroup = genuinePeriodSubgroup X := rfl

end JacobianChallenge.Periods
