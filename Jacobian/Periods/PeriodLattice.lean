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

/--
The period subgroup is discrete in the subspace topology.

Top-down obligation. Bottom-up: the period pairing image of `H₁(X, ℤ)`
has no accumulation point near zero — a consequence of the integrality
of period values on integral cycles.

This proof now delegates to `periodSubgroup_isZLattice` in
`Jacobian/Periods/PeriodFunctional.lean`.

**Goal.** Show `DiscreteTopology (basisAlignedPeriodSubgroup X)` where
`basisAlignedPeriodSubgroup X = basisAlignedPeriodSubgroupConcrete X`
is defined as
```
AddSubgroup.map
  (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
  (periodSubgroup ℂ X)
```
in `Jacobian/Periods/BasisAlignedPeriodSubgroup.lean`.

The ambient space `Fin (analyticGenus ℂ X) → ℂ` carries the product
topology and is a finite-dimensional normed space over `ℂ` (and `ℝ`).
The subgroup topology on `↥(basisAlignedPeriodSubgroup X)` is the
subspace topology induced from that product.

#### Mathlib lemmas surveyed

| Lemma | Signature / Status |
|---|---|
| `ZSpan.instDiscreteTopology...` | `DiscreteTopology ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup` for a finite `ℝ`-basis `b`. Gives discreteness of ℤ-spans of ℝ-bases in normed spaces. Would apply if we could exhibit a finite `ℝ`-basis whose ℤ-span equals the period subgroup. |
| `ZLattice.comap_discreteTopology` | Transports discreteness backwards along a continuous injective linear map: `DiscreteTopology ↥L → DiscreteTopology ↥(ZLattice.comap K L e)`. Operates on `Submodule ℤ`, not `AddSubgroup`, and goes in the *comap* direction (preimage), not *map* (image). |
| `Homeomorph.discreteTopology_iff` | `DiscreteTopology X ↔ DiscreteTopology Y` for `X ≃ₜ Y`. Would transport discreteness if both sides carried compatible topologies. |
| `AddSubgroup.isClosed_of_discrete` | Already used downstream (`basisAlignedPeriodSubgroup_isClosed`). Requires `DiscreteTopology` as input. |
| `discreteTopology_of_isOpen_singleton_one` | For topological groups: `{1}` is open implies discrete. Could be used if we could show `{0}` is open in the subgroup topology. |
| `DiscreteTopology.of_subset` | `DiscreteTopology ↑s → t ⊆ s → DiscreteTopology ↑t`. Useful for sub-subgroups of a known-discrete group. |
| `AddSubgroup.map_discreteTopology` | **Does not exist** in Mathlib (v4.28.0). There is no general result transporting `DiscreteTopology` forward through `AddSubgroup.map`. |
| `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples` | `DiscreteTopology ↥(AddSubgroup.zmultiples a)` for `a : ℝ`. A one-dimensional special case. |

2. **The algebraic dual `HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` has no
   `TopologicalSpace` instance.** Lean/Mathlib does not automatically
   topologise the algebraic dual `V →ₗ[ℂ] ℂ` (as opposed to the
   continuous dual `V →L[ℂ] ℂ`). So `periodSubgroup ℂ X` does not
   even carry a topology in which "discrete" could be stated directly.
   Discreteness only becomes a meaningful question after transport to
   `Fin g → ℂ` via `holomorphicOneFormDualEquiv`.

3. **No integrality / finite-generation property is available.** The
   mathematical content — that the image of `H₁(X, ℤ)` under the period
   pairing is a free ℤ-module of rank `2g`, spanned by `2g` ℝ-linearly
   independent period vectors — is not encoded anywhere in the project.
   Without this, `ZSpan.instDiscreteTopology...` cannot fire.

#### Proposed 3-step resolution plan

**(a) Declare a discreteness / finite-generation property on
`periodPairing` or `periodSubgroup`.** The cleanest option is to add a
new `opaque` alongside `periodPairing` in
`Jacobian/Periods/PeriodFunctional.lean`:
```
opaque periodSubgroup_discreteTopology_basis_aligned
    (E : Type*) [...] (X : Type) [...] :
    DiscreteTopology (basisAlignedPeriodSubgroupConcrete X)
```
or, more structurally, declare that the image admits a ℤ-basis of
cardinality `2 * analyticGenus ℂ X` spanning a full-rank ℤ-lattice:
```
opaque periodSubgroup_isZLattice
    (E : Type*) [...] (X : Type) [...] :
    IsZLattice ℝ (periodSubgroupAsSubmodule ℂ X)
```
where `periodSubgroupAsSubmodule` lifts the `AddSubgroup` to a
`Submodule ℤ` and further witnesses that it spans `ℝ^(2g)`. The
`IsZLattice` approach is mathematically richer and also yields the
fundamental domain and covering properties needed downstream.

**(b) Derive `DiscreteTopology (periodSubgroup ℂ X)` from (a).**
If (a) declares `IsZLattice ℝ` on the ℤ-submodule spanned by
the period vectors in `Fin g → ℂ`, then Mathlib's
`ZSpan.instDiscreteTopology...` gives `DiscreteTopology` on the
corresponding `AddSubgroup` directly.

Alternatively, if (a) directly declares `DiscreteTopology` on the
basis-aligned subgroup, step (b) is trivial.

#### Downstream impact
-/
instance basisAlignedPeriodSubgroup_isDiscrete :
    DiscreteTopology (basisAlignedPeriodSubgroup X) :=
  periodSubgroup_isZLattice ℂ X

/-- The period subgroup is closed in the model space. -/
lemma basisAlignedPeriodSubgroup_isClosed :
    IsClosed (basisAlignedPeriodSubgroup X : Set (Fin (analyticGenus ℂ X) → ℂ)) :=
  AddSubgroup.isClosed_of_discrete

/-- A fundamental domain for the period subgroup, in the basis-aligned model. -/
noncomputable def periodFundamentalDomain : Set (Fin (analyticGenus ℂ X) → ℂ) :=
  (exists_compact_periodFundamentalDomain X).choose

/--
The fundamental domain is compact.

Top-down obligation. Bottom-up: bounded subset of a finite-dim
ℂ-vector space; bounded ⇒ compact in finite dimensions.

**Goal.** Show `IsCompact (periodFundamentalDomain X)` where
`periodFundamentalDomain X` is an `opaque` of type
`Set (Fin (analyticGenus ℂ X) → ℂ)`. Its mathematical intent is
"a fundamental domain for the action of the period subgroup on the
basis-aligned model — for example the closure of
`ZSpan.fundamentalDomain` against a chosen ℤ-basis of the subgroup".

The ambient space `Fin (analyticGenus ℂ X) → ℂ` is finite-dimensional
over `ℝ` (dimension `2 * analyticGenus ℂ X`), hence a `ProperSpace`,
so the Heine–Borel theorem applies.

#### Mathlib lemmas surveyed

| Lemma | Signature | Applicability |
|---|---|---|
| `ZSpan.fundamentalDomain_isBounded` | `Bornology.IsBounded (ZSpan.fundamentalDomain b)` for a finite basis `b` over a `NormedLinearOrderedField` with `FloorRing` and `HasSolidNorm`. | Gives boundedness of the open fundamental domain `{x | ∀ i, b.repr x i ∈ Set.Ico 0 1}`. Would fire if `periodFundamentalDomain` were defined as `ZSpan.fundamentalDomain b` for a known basis `b`. |
| `Bornology.IsBounded.isCompact_closure` | `IsBounded s → IsCompact (closure s)` in a `ProperSpace`. | Yields compactness of `closure (ZSpan.fundamentalDomain b)` once boundedness is established. This is the cleanest route for the "closure of a half-open parallelepiped" definition. |
| `Metric.isCompact_of_isClosed_isBounded` | `IsClosed s → IsBounded s → IsCompact s` in a `ProperSpace`. | Alternative to the above; requires separate `IsClosed` witness. |
| `Basis.parallelepiped` | `Basis ι ℝ E → TopologicalSpace.PositiveCompacts E` | The parallelepiped `{x | ∀ i, b.repr x i ∈ Set.Icc 0 1}` is a compact set with nonempty interior. Since `ZSpan.fundamentalDomain_subset_parallelepiped` shows `fundamentalDomain b ⊆ parallelepiped b`, the closure of the fundamental domain lies inside this compact set — hence is compact. |
| `ZSpan.fundamentalDomain_subset_parallelepiped` | `ZSpan.fundamentalDomain b ⊆ parallelepiped b` for `[Fintype ι]`. | Reduces boundedness/compactness of the fundamental domain to that of the parallelepiped. |
| `ZLattice.isAddFundamentalDomain` | `IsAddFundamentalDomain ↥L (ZSpan.fundamentalDomain (Basis.ofZLatticeBasis ℝ L b)) μ` for `[IsZLattice ℝ L]`, `[DiscreteTopology ↥L]`. | Confirms that `ZSpan.fundamentalDomain` against the real basis lifted from a ℤ-lattice basis is indeed a measure-theoretic fundamental domain. Needs `IsZLattice ℝ`. |

#### Two independent blockers

#### Proposed resolution paths

**(Option A — preferred) Replace the bare `opaque` with a concrete
`noncomputable def`:** Define `periodFundamentalDomain X` as
```
noncomputable def periodFundamentalDomain : Set (Fin (analyticGenus ℂ X) → ℂ) :=
  closure (ZSpan.fundamentalDomain (Basis.ofZLatticeBasis ℝ L (IsZLattice.basis L)))
```
where `L` is the period subgroup promoted to `Submodule ℤ`. Then
compactness follows in one line:
```
exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
```
This also provides `_covers` for free via
`ZLattice.isAddFundamentalDomain` (fundamental domains cover a.e.,
and the closure covers everywhere). Requires `IsZLattice ℝ L` +
`DiscreteTopology ↥L`.

**(Option B) Keep the `opaque` and add a companion axiom:** Declare a
new `opaque` in `Jacobian/Periods/PeriodFunctional.lean` (or alongside
`periodFundamentalDomain`):
```
opaque periodFundamentalDomain_isCompact_aux (X : Type) [...] :
    IsCompact (periodFundamentalDomain X)
```
This is mathematically less informative but unblocks the top-down
assembly immediately, deferring the bottom-up content to the same
future work package as `periodPairing`.

**(Option C) Add an `IsZLattice` opaque + a definitional equality
opaque:** Keep `periodFundamentalDomain` opaque but add:
```
opaque periodFundamentalDomain_eq (X : Type) [...] :
    periodFundamentalDomain X =
      closure (ZSpan.fundamentalDomain (...))
```
Then rewrite and apply `IsBounded.isCompact_closure`. This is
strictly worse than Option A unless there is a policy reason to keep
the `opaque` wrapper.

#### Recommended single-obligation prerequisite

If **Option A** is adopted (preferred), the sole new named obligation
needed — beyond the `IsZLattice ℝ` opaque already recommended by the
discreteness survey — is to **un-opaque `periodFundamentalDomain`**
and redefine it concretely. Once `IsZLattice ℝ` and the concrete
definition are in place, `_isCompact` becomes:
```
exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
```
and `_isDiscrete` is resolved by `ZSpan.instDiscreteTopology` or
equivalent.

#### Dependency graph
-/
lemma periodFundamentalDomain_isCompact :
    IsCompact (periodFundamentalDomain X) :=
  (exists_compact_periodFundamentalDomain X).choose_spec.1

/-- The fundamental-domain translates cover the model space. -/
lemma periodFundamentalDomain_covers :
    ∀ v : Fin (analyticGenus ℂ X) → ℂ,
      ∃ g ∈ basisAlignedPeriodSubgroup X, v - g ∈ periodFundamentalDomain X :=
  (exists_compact_periodFundamentalDomain X).choose_spec.2

/--
The period lattice of a compact Riemann surface, bundled as a
`FullComplexLattice` in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.
-/
noncomputable def periodFullComplexLattice :
    JacobianChallenge.ComplexTorus.FullComplexLattice
      (Fin (analyticGenus ℂ X) → ℂ) where
  subgroup := basisAlignedPeriodSubgroup X
  isClosed := basisAlignedPeriodSubgroup_isClosed X
  isDiscrete := basisAlignedPeriodSubgroup_isDiscrete X
  fundamentalDomain := periodFundamentalDomain X
  fundamentalDomain_isCompact := periodFundamentalDomain_isCompact X
  fundamentalDomain_covers := periodFundamentalDomain_covers X

end JacobianChallenge.Periods
