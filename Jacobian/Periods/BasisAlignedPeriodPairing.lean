import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Basis-aligned period pairing

This file packages the composition of `periodPairing ℂ X` (functional-space)
with the basis-aligned dual equivalence as a single `AddMonoidHom`:

```text
basisAlignedPeriodPairing X
  : IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ)
  = (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom.comp
      (periodPairing ℂ X)
```

This is the natural arrow from cycles directly into the basis-aligned
model, skipping the intermediate functional-space stop. The
`basisAlignedPeriodSubgroupConcrete X` is exactly the range of this map.

Useful for two later goals:
1. Discharging `basisAlignedPeriodSubgroup_isDiscrete` once the opaque is
   unfrozen — the discreteness reduces to "image of `H₁(X, ℤ)` under the
   pairing has no accumulation in the basis-aligned model".
2. Discharging the eventual fundamental-domain construction — the
   `ZSpan.fundamentalDomain` machinery in Mathlib operates on a
   `Module.Basis (Fin n) ℤ` of an additive subgroup; this file provides
   the `Fin n → ℂ`-valued period pairing whose image we want to span.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The basis-aligned period pairing: integration of holomorphic 1-forms
over integer 1-cycles, postcomposed with the basis-aligned dual
equivalence.
-/
noncomputable def basisAlignedPeriodPairing :
    IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ) :=
  ((holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom).comp
    (periodPairing ℂ X)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Pointwise: the basis-aligned period pairing applies the dual equiv to
the functional-space period pairing.
-/
theorem basisAlignedPeriodPairing_apply (σ : IntegralOneCycle X) :
    basisAlignedPeriodPairing X σ =
      holomorphicOneFormDualEquiv ℂ X (periodPairing ℂ X σ) :=
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The basis-aligned period subgroup is exactly the range of the
basis-aligned period pairing.
-/
theorem basisAlignedPeriodSubgroupConcrete_eq_range :
    basisAlignedPeriodSubgroupConcrete X =
      (basisAlignedPeriodPairing X).range := by
  unfold basisAlignedPeriodSubgroupConcrete basisAlignedPeriodPairing
  ext v
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range,
             AddMonoidHom.coe_comp, Function.comp_apply,
             periodSubgroup, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨φ, ⟨σ, hσ⟩, hv⟩
    exact ⟨σ, hσ ▸ hv⟩
  · rintro ⟨σ, hv⟩
    exact ⟨periodPairing ℂ X σ, ⟨σ, rfl⟩, hv⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Period pairings of cycles always lie in the basis-aligned period
subgroup.
-/
theorem basisAlignedPeriodPairing_mem
    (σ : IntegralOneCycle X) :
    basisAlignedPeriodPairing X σ ∈
      basisAlignedPeriodSubgroupConcrete X := by
  rw [basisAlignedPeriodSubgroupConcrete_eq_range]
  exact ⟨σ, rfl⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Two basis-aligned period values are equal iff the underlying
functional-space periods are equal. Follows from injectivity of the
dual equivalence.
-/
theorem basisAlignedPeriodPairing_eq_iff (σ τ : IntegralOneCycle X) :
    basisAlignedPeriodPairing X σ = basisAlignedPeriodPairing X τ ↔
      periodPairing ℂ X σ = periodPairing ℂ X τ := by
  rw [basisAlignedPeriodPairing_apply, basisAlignedPeriodPairing_apply,
      EmbeddingLike.apply_eq_iff_eq]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
`basisAlignedPeriodPairing X σ = 0` iff
`periodPairing ℂ X σ = 0`. Special case of `_eq_iff` at `τ = 0`.
-/
theorem basisAlignedPeriodPairing_eq_zero_iff (σ : IntegralOneCycle X) :
    basisAlignedPeriodPairing X σ = 0 ↔ periodPairing ℂ X σ = 0 := by
  rw [show (0 : Fin (analyticGenus ℂ X) → ℂ) =
        basisAlignedPeriodPairing X 0 from
        ((basisAlignedPeriodPairing X).map_zero).symm,
      basisAlignedPeriodPairing_eq_iff, (periodPairing ℂ X).map_zero]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Pulling a basis-aligned period back through the inverse dual
equivalence recovers the functional-space `periodPairing`.
-/
theorem holomorphicOneFormDualEquiv_symm_basisAlignedPeriodPairing
    (σ : IntegralOneCycle X) :
    (holomorphicOneFormDualEquiv ℂ X).symm
        (basisAlignedPeriodPairing X σ) =
      periodPairing ℂ X σ := by
  rw [basisAlignedPeriodPairing_apply, LinearEquiv.symm_apply_apply]

end JacobianChallenge.Periods
