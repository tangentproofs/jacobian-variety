import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.Periods.PeriodFunctional
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Basis-aligned period subgroup (concrete representative)

Top-down obligation upgrade. The `Jacobian.Periods.PeriodLattice` module
declares an `opaque periodSubgroup : AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)`
for which all five sorries (`_isClosed`, `_isDiscrete`,
`_fundamentalDomain_isCompact`, `_fundamentalDomain_covers`, etc.) are
*literally unprovable* — there is no body to unfold.

This file provides the concrete representative
`basisAlignedPeriodSubgroupConcrete X`, defined as the image of the
existing functional-space `Periods.periodSubgroup ℂ X`
(= `(periodPairing ℂ X).range`) under the basis-aligned dual equivalence
`HolomorphicForms.holomorphicOneFormDualEquiv`. Once a future tick
renames the opaque (e.g. to `JacobianChallenge.Periods.basisAlignedPeriodSubgroup`)
and points `periodFullComplexLattice` at this file's definition, the five
PeriodLattice obligations become substantive but bounded targets:
- `_isClosed`: closed image under a continuous LinearEquiv on a finite-dim space;
- `_isDiscrete`: image of a discrete subgroup under a homeomorphism;
- `_fundamentalDomain_isCompact` & `_covers`: standard
  `ZSpan.fundamentalDomain` machinery against a chosen basis.

Note: this file deliberately uses a distinctive name
(`basisAlignedPeriodSubgroupConcrete`) to avoid colliding with the
`opaque periodSubgroup` declared in `PeriodLattice.lean` (Lean 4 does
not allow two declarations with the same fully-qualified name to
coexist in a single elaboration context, and `PeriodLattice.lean`'s
opaque is in the same namespace `JacobianChallenge.Periods`). Hence we
do NOT import `PeriodLattice` here.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The basis-aligned period subgroup, defined concretely as the image of
the functional-space `periodSubgroup ℂ X` under the basis-aligned dual
equivalence. The `[FiniteDimensionalHolomorphicOneForms ℂ X]` assumption
keeps the basis machinery's finite-dimensionality requirement visible.
-/
noncomputable def basisAlignedPeriodSubgroupConcrete :
    AddSubgroup (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.map
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
    (periodSubgroup ℂ X)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
An element of `basisAlignedPeriodSubgroupConcrete X` is exactly the
image of some functional-space period under the dual equivalence.
-/
theorem mem_basisAlignedPeriodSubgroupConcrete_iff
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    v ∈ basisAlignedPeriodSubgroupConcrete X ↔
      ∃ φ ∈ periodSubgroup ℂ X,
        holomorphicOneFormDualEquiv ℂ X φ = v := by
  unfold basisAlignedPeriodSubgroupConcrete
  exact AddSubgroup.mem_map

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The `0` of the basis-aligned space lies in the concrete period
subgroup (since `0 ∈ periodSubgroup` always, and the dual equiv preserves
zero). Sanity check; redundant with `AddSubgroup.zero_mem` but recorded
explicitly.
-/
theorem zero_mem_basisAlignedPeriodSubgroupConcrete :
    (0 : Fin (analyticGenus ℂ X) → ℂ) ∈
      basisAlignedPeriodSubgroupConcrete X :=
  (basisAlignedPeriodSubgroupConcrete X).zero_mem

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Inverse-direction transport: pulling back an element of the
basis-aligned period subgroup through the inverse dual equivalence
lands in the functional-space `periodSubgroup ℂ X`.
-/
theorem holomorphicOneFormDualEquiv_symm_mem_periodSubgroup
    {v : Fin (analyticGenus ℂ X) → ℂ}
    (hv : v ∈ basisAlignedPeriodSubgroupConcrete X) :
    (holomorphicOneFormDualEquiv ℂ X).symm v ∈ periodSubgroup ℂ X := by
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv
  rw [← hφ_eq, LinearEquiv.symm_apply_apply]
  exact hφ_mem

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Forward-direction transport: pushing an element of the functional-space
`periodSubgroup ℂ X` through the dual equivalence lands in the
basis-aligned period subgroup. The trivial `mp` direction; recorded
explicitly for use as a lemma at call sites.
-/
theorem holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete
    {φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ}
    (hφ : φ ∈ periodSubgroup ℂ X) :
    holomorphicOneFormDualEquiv ℂ X φ ∈ basisAlignedPeriodSubgroupConcrete X :=
  (mem_basisAlignedPeriodSubgroupConcrete_iff X _).mpr ⟨φ, hφ, rfl⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The dual equivalence restricts to a bijection between the
functional-space and basis-aligned period subgroups (as sets). Combines
the forward-direction membership transport, injectivity of the
equivalence, and the surjective image characterization.
-/
theorem holomorphicOneFormDualEquiv_bijOn_periodSubgroup :
    Set.BijOn (holomorphicOneFormDualEquiv ℂ X)
      (periodSubgroup ℂ X : Set _)
      (basisAlignedPeriodSubgroupConcrete X : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · -- maps into
    intro φ hφ
    exact holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete X hφ
  · -- injective on the source set
    intro φ _ ψ _ heq
    exact (holomorphicOneFormDualEquiv ℂ X).injective heq
  · -- surjective onto the target set
    intro v hv
    rw [SetLike.mem_coe, mem_basisAlignedPeriodSubgroupConcrete_iff] at hv
    obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv
    exact ⟨φ, hφ_mem, hφ_eq⟩

/--
The dual equivalence restricts to an additive isomorphism between
the functional-space `periodSubgroup ℂ X` and the basis-aligned
`basisAlignedPeriodSubgroupConcrete X`. Built from Mathlib's
`AddSubgroup.equivMapOfInjective` against the injective dual
equivalence.
-/
noncomputable def holomorphicOneFormDualPeriodSubgroupEquiv :
    periodSubgroup ℂ X ≃+ basisAlignedPeriodSubgroupConcrete X :=
  (periodSubgroup ℂ X).equivMapOfInjective
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
    (holomorphicOneFormDualEquiv ℂ X).injective

end JacobianChallenge.Periods
