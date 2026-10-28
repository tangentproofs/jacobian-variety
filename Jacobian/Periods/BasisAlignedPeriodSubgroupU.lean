import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.Periods.PeriodFunctionalU
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Basis-aligned period subgroup, universe-polymorphic companion

`Jacobian/Periods/BasisAlignedPeriodSubgroup.lean` defines the concrete
basis-aligned period subgroup `basisAlignedPeriodSubgroupConcrete (X : Type)` at
universe 0, as the image of the Type-0 functional-space `periodSubgroup ℂ X`
(`= (periodPairing ℂ X).range`) under the dual equivalence
`HolomorphicForms.holomorphicOneFormDualEquiv`.

This file provides the universe-polymorphic companion
`basisAlignedPeriodSubgroupConcreteU (X : Type u)`, built identically but on the
universe-`u` complex-model period subgroup `(periodPairingComplexU X).range`
(C1b, `Jacobian/Periods/PeriodFunctionalU.lean`). This is step C2a of the
authorized full `Type u` generalization of the period lattice (Option C
containment): with this transport layer in place, the universe-`u` discreteness /
spanning / fundamental-domain facts (C2b) and then `periodFullComplexLattice`
(C3) can be widened to `X : Type u`, so the public `Jacobian (X : Type u)`
type-checks — without disturbing the Type-0 period subsystem.

The carrier `Fin (analyticGenus ℂ X) → ℂ` is `Type 0` for any `X : Type u`, and
`holomorphicOneFormDualEquiv` is already universe-polymorphic
(`BasisAlignedDualEquiv.lean`), so every lemma here is a verbatim mirror of its
Type-0 original with `periodSubgroup ℂ X` replaced by `(periodPairingComplexU X).range`.

Note: we use the complex-model pairing `periodPairingComplexU` (which hardcodes
`E := ℂ`) rather than the general `periodPairingU ℂ X`, because the latter's
`(E : Type u)` binder would force `E`'s universe to equal `X`'s, pinning `u = 0`
when `E := ℂ : Type 0`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The universe-`u` basis-aligned period subgroup, defined concretely as the image
of the universe-`u` complex-model period subgroup `(periodPairingComplexU X).range`
under the basis-aligned dual equivalence. Companion to
`basisAlignedPeriodSubgroupConcrete`.
-/
noncomputable def basisAlignedPeriodSubgroupConcreteU :
    AddSubgroup (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.map
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
    (periodPairingComplexU X).range

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
An element of `basisAlignedPeriodSubgroupConcreteU X` is exactly the image of
some functional-space period under the dual equivalence.
-/
theorem mem_basisAlignedPeriodSubgroupConcreteU_iff
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    v ∈ basisAlignedPeriodSubgroupConcreteU X ↔
      ∃ φ ∈ (periodPairingComplexU X).range,
        holomorphicOneFormDualEquiv ℂ X φ = v := by
  unfold basisAlignedPeriodSubgroupConcreteU
  exact AddSubgroup.mem_map

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The `0` of the basis-aligned space lies in the concrete period subgroup.
-/
theorem zero_mem_basisAlignedPeriodSubgroupConcreteU :
    (0 : Fin (analyticGenus ℂ X) → ℂ) ∈
      basisAlignedPeriodSubgroupConcreteU X :=
  (basisAlignedPeriodSubgroupConcreteU X).zero_mem

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Inverse-direction transport: pulling back an element of the basis-aligned period
subgroup through the inverse dual equivalence lands in the functional-space
`(periodPairingComplexU X).range`.
-/
theorem holomorphicOneFormDualEquiv_symm_mem_periodSubgroupU
    {v : Fin (analyticGenus ℂ X) → ℂ}
    (hv : v ∈ basisAlignedPeriodSubgroupConcreteU X) :
    (holomorphicOneFormDualEquiv ℂ X).symm v ∈ (periodPairingComplexU X).range := by
  rw [mem_basisAlignedPeriodSubgroupConcreteU_iff] at hv
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv
  rw [← hφ_eq, LinearEquiv.symm_apply_apply]
  exact hφ_mem

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Forward-direction transport: pushing an element of the functional-space
`(periodPairingComplexU X).range` through the dual equivalence lands in the
basis-aligned period subgroup.
-/
theorem holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcreteU
    {φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ}
    (hφ : φ ∈ (periodPairingComplexU X).range) :
    holomorphicOneFormDualEquiv ℂ X φ ∈ basisAlignedPeriodSubgroupConcreteU X :=
  (mem_basisAlignedPeriodSubgroupConcreteU_iff X _).mpr ⟨φ, hφ, rfl⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The dual equivalence restricts to a bijection between the functional-space and
basis-aligned period subgroups (as sets).
-/
theorem holomorphicOneFormDualEquiv_bijOn_periodSubgroupU :
    Set.BijOn (holomorphicOneFormDualEquiv ℂ X)
      ((periodPairingComplexU X).range : Set _)
      (basisAlignedPeriodSubgroupConcreteU X : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · -- maps into
    intro φ hφ
    exact holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcreteU X hφ
  · -- injective on the source set
    intro φ _ ψ _ heq
    exact (holomorphicOneFormDualEquiv ℂ X).injective heq
  · -- surjective onto the target set
    intro v hv
    rw [SetLike.mem_coe, mem_basisAlignedPeriodSubgroupConcreteU_iff] at hv
    obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv
    exact ⟨φ, hφ_mem, hφ_eq⟩

/--
The dual equivalence restricts to an additive isomorphism between the
functional-space `(periodPairingComplexU X).range` and the basis-aligned
`basisAlignedPeriodSubgroupConcreteU X`. Companion to
`holomorphicOneFormDualPeriodSubgroupEquiv`.
-/
noncomputable def holomorphicOneFormDualPeriodSubgroupEquivU :
    (periodPairingComplexU X).range ≃+ basisAlignedPeriodSubgroupConcreteU X :=
  ((periodPairingComplexU X).range).equivMapOfInjective
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
    (holomorphicOneFormDualEquiv ℂ X).injective

end JacobianChallenge.Periods
