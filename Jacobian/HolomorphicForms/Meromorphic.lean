import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.FiniteDimensional
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.OnePointCxChartedSpace
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Meromorphic maps to the Riemann sphere

This file introduces the production-facing interface used by the genus-zero
classification proof.  It is intentionally narrow: the fields record the
global map together with the divisor data and analytic axioms needed
downstream.  Future bottom-up work can identify these axioms with the local
`MeromorphicAt`/order API.

### Why these fields are present
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- A meromorphic map from a compact Riemann surface to `OnePoint ℂ`. -/
structure MeromorphicMapToSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  locally_meromorphic : Prop
  zeroDivisor : Divisor X
  poleDivisor : Divisor X
  principalDivisor : Divisor X
  principalDivisor_eq : principalDivisor = zeroDivisor - poleDivisor
  /--
The pole divisor of a meromorphic function has nonneg coefficients
  pointwise.  This is the structural fact behind `Divisor.Effective f.poles`.
-/
  poleDivisor_nonneg : ∀ P : X, 0 ≤ poleDivisor P
  /--
A point cannot simultaneously be a zero and a pole of a meromorphic
  function.  This expresses the disjoint-support property of the
  zero/pole divisor decomposition.
-/
  zero_or_pole_eq_zero : ∀ Q : X, zeroDivisor Q = 0 ∨ poleDivisor Q = 0
  /--
Off the pole locus a meromorphic-map-to-sphere takes finite values
  in `OnePoint ℂ`.  Combined with continuity below, this captures that
  poles are exactly the preimage of `∞`.
-/
  toMap_ne_infty_of_poleDivisor_zero :
    ∀ x : X, poleDivisor x = 0 → toMap x ≠ (OnePoint.infty : OnePoint ℂ)
  /--
A meromorphic-map-to-sphere is continuous on the locus of finite
  values (i.e. the complement of its pole set).  This is the
  `OnePoint`-restricted form of the classical "holomorphic away from
  poles ⇒ continuous".
-/
  continuousOn_ne_infty :
    ContinuousOn toMap {x : X | toMap x ≠ (OnePoint.infty : OnePoint ℂ)}
  /--
Any global complex-valued lift of `toMap` through the canonical
  inclusion `ℂ → OnePoint ℂ` is `MDifferentiable`.  This implements
  "holomorphic ⇒ smooth" for the lifted map.
-/
  toFiniteFun_mdifferentiable :
    ∀ g : X → ℂ,
      toMap = (fun x => ((g x : ℂ) : OnePoint ℂ)) →
      MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g
  /--
At a (positive-order) pole of a meromorphic-map-to-sphere, the map
  evaluates to `∞ : OnePoint ℂ`.
-/
  toMap_eq_infty_of_poleDivisor_pos :
    ∀ P : X, 0 < poleDivisor P → toMap P = (OnePoint.infty : OnePoint ℂ)

namespace MeromorphicMapToSphere

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

instance : CoeFun (MeromorphicMapToSphere X) (fun _ => X → OnePoint ℂ) where
  coe f := f.toMap

/-- The zero divisor of a meromorphic map. -/
def zeros (f : MeromorphicMapToSphere X) : Divisor X :=
  f.zeroDivisor

/-- The pole divisor of a meromorphic map. -/
def poles (f : MeromorphicMapToSphere X) : Divisor X :=
  f.poleDivisor

/-- The principal divisor `(f)`, zeros minus poles. -/
def principal (f : MeromorphicMapToSphere X) : Divisor X :=
  f.principalDivisor

/-- A meromorphic map has one simple pole at `P` and no other poles. -/
def HasSimplePoleOnlyAt (f : MeromorphicMapToSphere X) (P : X) : Prop :=
  f.poles = Divisor.point P

/-- A meromorphic map is nonconstant. -/
def Nonconstant (f : MeromorphicMapToSphere X) : Prop :=
  ¬ ∃ c : OnePoint ℂ, ∀ x : X, f.toMap x = c

/--
Membership in the Riemann-Roch space `L(D)`: `(f) + D ≥ 0`.

This is the divisor-theoretic condition that `f` has poles bounded by `D`.
-/
def MemRiemannRochSpace (f : MeromorphicMapToSphere X) (D : Divisor X) : Prop :=
  Divisor.Effective (f.principal + D)

/--
A named predicate for continuity of the map to `OnePoint ℂ`.  This is
kept separate from meromorphicity because proving continuity of the extended
map is one of the degree/properness work packets.
-/
def ExtendsContinuously (f : MeromorphicMapToSphere X) : Prop :=
  Continuous f.toMap

/--
Additional analytic data for an honest meromorphic map: near a pole,
the map admits a finite lift on the non-pole locus whose modulus tends to
infinity.

**Un-bundling (2026-05-29):** This record is now the *sole carrier* of the
pole-modulus content. The corresponding inlined field on
`MeromorphicMapToSphere` was removed because mandatory analytic fields
forced scaffold constructors (`twoPointMeromorphicMap`, `constMeromorphicMap`,
`singleZeroSinglePoleMap`) to fill provably-impossible obligations with
`sorry`. Honest meromorphic-map constructors now build a `PoleModulusData`
value alongside the map; downstream consumers take it as an explicit
hypothesis.
-/
structure PoleModulusData (f : MeromorphicMapToSphere X) where
  exists_modulus_atTop_at_pole :
    ∀ P : X, 0 < f.poleDivisor P →
      ∃ g : X → ℂ,
        (∀ x : X, f.poleDivisor x = 0 →
          f.toMap x = ((g x : ℂ) : OnePoint ℂ)) ∧
        Filter.Tendsto (fun x => ‖g x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

/--
Additional analytic data for an honest nonconstant meromorphic map:
conditional on continuity, it has branched-cover data whose degree is the
degree of the pole divisor.

**Un-bundling (2026-05-29):** This record is now the *sole carrier* of the
branched-cover data. The corresponding inlined field on
`MeromorphicMapToSphere` was removed; see the note on `PoleModulusData`
for the rationale. Honest meromorphic-map constructors now build a
`BranchedCoverDataOfPoleDegree` value alongside the map; downstream
consumers take it as an explicit hypothesis.
-/
structure BranchedCoverDataOfPoleDegree (f : MeromorphicMapToSphere X) where
  hasBranchedCoverDataOfPoleDegree :
    Continuous f.toMap →
    ∃ (h : JacobianChallenge.HolomorphicForms.BranchedCoverData X (OnePoint ℂ) f.toMap),
      JacobianChallenge.HolomorphicForms.branchedDegree h = f.poleDivisor.degree.toNat

/--
**Honest analytic data for a `MeromorphicMapToSphere`.**

The abstract `MeromorphicMapToSphere` structure carries only set-level
data, divisor arithmetic, topological values at poles, continuity off
poles, and a *global* finite-lift differentiability axiom that is
vacuous whenever there are any poles. `PoleModulusData` adds a
modulus-divergence witness near poles but no analyticity.

This record bundles the **per-point analytic content** that an honest
meromorphic-map-to-sphere actually carries but the abstract interface
cannot derive:

* `continuous_toMap` — the global continuity statement
  (`MeromorphicMapToSphere.ExtendsContinuously`). Although the
  structure has a continuous extension on the non-pole locus, the
  global continuity at poles requires additional analytic input. We
  collect it here.
* `meromorphic_getD` — the *point-by-point* `MeromorphicAtX` predicate
  for the canonical finite lift `q ↦ (f.toMap q).getD 0`. This is the
  precise analytic content needed by the
  `MeromorphicFunctionType`/`liftToCp1` infrastructure of
  `MeromorphicToCp1.lean`.
* `simple_pole_order_one` — at a *simple* pole, the chart-local
  analytic order of `f.toMap` equals `1`. This is the analytic content
  "simple pole ⇒ ramification index one", read in the inversion chart
  on `OnePoint ℂ`.

Scaffold maps (e.g. `singlePoleMeromorphicMap`, `twoPointMeromorphicMap`)
generally cannot produce this data; production constructors (the
Riemann-Roch witness, dipole construction, an honest
`MeromorphicFunctionType` package) supply it by construction. The
data is intentionally *separate* from `MeromorphicMapToSphere` so that
the abstract interface can continue to be lock-stepped with scaffold
constructors that genuinely fail these analytic claims.

Production downstream theorems should consume `AnalyticData` (or the
record in which it is bundled) rather than the abstract interface
plus `PoleModulusData`.
-/
structure AnalyticData (f : MeromorphicMapToSphere X) where
  /-- Global continuity of the map to `OnePoint ℂ`. -/
  continuous_toMap : Continuous f.toMap
  /--
The canonical finite lift `(f.toMap ·).getD 0` is meromorphic at
  every point in the manifold sense.
-/
  meromorphic_getD :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        (fun q => (f.toMap q).getD 0) p
  /--
At a *simple* pole, the chart-local analytic order of `f.toMap`
  is exactly `1`. This is the analytic content
  "simple pole ⇒ ramification index one".
-/
  simple_pole_order_one :
    ∀ P : X,
      f.poles = Divisor.point P →
        JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1

@[simp] theorem principal_eq_zeroDivisor_sub_poleDivisor
    (f : MeromorphicMapToSphere X) :
    f.principal = f.zeroDivisor - f.poleDivisor :=
  f.principalDivisor_eq

end MeromorphicMapToSphere

/--
For a `MeromorphicMapToSphere X` with pole divisor `Divisor.point P`
that *also* carries explicit `PoleModulusData`, the norm of the
canonical finite lift `x ↦ (f.toMap x).getD 0` tends to `+∞` along
the punctured neighborhood of `P`.

This is the honest provider used by production downstream code. The
`PoleModulusData` hypothesis directly carries a global finite lift `g`
of `f.toMap` off the pole locus whose modulus diverges at `P`; the
proof glues together the off-pole agreement
`f.toMap x = ((g x : ℂ) : OnePoint ℂ)` (whose `getD 0` recovers `g x`)
with the modulus divergence of `g`, eventually in `nhdsWithin P {P}ᶜ`.
-/
theorem MeromorphicMapToSphere.modulus_tendsto_atTop_of_poleModulusData_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P)
    (hmod : f.PoleModulusData) :
    Filter.Tendsto
      (fun x => ‖(f.toMap x).getD 0‖)
      (nhdsWithin P {P}ᶜ)
      Filter.atTop := by
  classical
  have hposP : 0 < f.poleDivisor P := by
    have hh : f.poleDivisor P = (Divisor.point P : Divisor X) P := by
      change f.poles P = (Divisor.point P : Divisor X) P
      rw [hpole]
    rw [hh, Divisor.point_apply_self]; decide
  obtain ⟨g, hg_eq, hg_div⟩ := hmod.exists_modulus_atTop_at_pole P hposP
  refine (hg_div.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxP : x ≠ P := hx
  have hxpoleZero : f.poleDivisor x = 0 := by
    have hh : f.poleDivisor x = (Divisor.point P : Divisor X) x := by
      change f.poles x = (Divisor.point P : Divisor X) x
      rw [hpole]
    rw [hh, Divisor.point_apply_ne hxP]
  have hfx : f.toMap x = ((g x : ℂ) : OnePoint ℂ) := hg_eq x hxpoleZero
  show ‖g x‖ = ‖(f.toMap x).getD 0‖
  rw [hfx]; rfl

/--
For any `MeromorphicMapToSphere X` with pole divisor `Divisor.point P`
and an explicit `PoleModulusData`, the norm of the canonical finite lift
`x ↦ (f.toMap x).getD 0` tends to `+∞` along the punctured neighborhood
of `P`.

**Un-bundling (2026-05-29):** previously this lemma did not take an
explicit `hmod` hypothesis because `MeromorphicMapToSphere` carried the
pole-modulus content as an inlined field; with the field removed, the
hypothesis is supplied explicitly, matching the sibling lemma
`modulus_tendsto_atTop_of_poleModulusData_poleDivisor_point` it delegates
to.
-/
theorem MeromorphicMapToSphere.modulus_tendsto_atTop_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P)
    (hmod : f.PoleModulusData) :
    Filter.Tendsto
      (fun x => ‖(f.toMap x).getD 0‖)
      (nhdsWithin P {P}ᶜ)
      Filter.atTop :=
  MeromorphicMapToSphere.modulus_tendsto_atTop_of_poleModulusData_poleDivisor_point
    f P hpole hmod

end JacobianChallenge.HolomorphicForms
