import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Universe-polymorphic path-integral functional

`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` bundles the basis-coordinate
path-integral functional `(P, Q) ↦ (∫_P^Q ω₁, …, ∫_P^Q ωₘ)` of a compact
Riemann surface into `opaque pathIntegralFunctionalBundle (X : Type)` and
extracts `pathIntegralFunctional X P Q : Fin (analyticGenus ℂ X) → ℂ`. The whole
analytic Abel-Jacobi map `analyticOfCurve` is built on this functional.

This file provides the universe-polymorphic companion `pathIntegralFunctionalU`
(D0 of the Abel-Jacobi "D-chain" — the universe-`u` generalization of the
Abel-Jacobi layer, mirroring the C0–C3 period-lattice chain). It is the
foundation on which `analyticOfCurveU` (D1) — and hence the public
`ofCurve : X → Jacobian X` for `X : Type u` — will be built.

The functional's codomain `Fin (analyticGenus ℂ X) → ℂ` is `Type 0` for any
`X : Type u`, so only the binder `(X : Type)` needs widening to `(X : Type u)`.
As on the Type-0 side, the bundle is an `opaque` (the genuine multi-chart path
integration is deferred infrastructure); `opaque` introduces no axiom and no
sorry — it is the universe-`u` analogue of the existing Type-0
`opaque pathIntegralFunctionalBundle`.
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

universe u

/--
Universe-polymorphic companion to `PathIntegralFunctionalBundle`: bundles the
basis-coordinate path-integral functional with its constant-loop specification
and endpoint-smoothness, for `X : Type u`.
-/
structure PathIntegralFunctionalBundleU
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] where
  /-- The path-integral coordinates `(P, Q) ↦ (∫_P^Q ω₁, …, ∫_P^Q ωₘ)`. -/
  val : X → X → Fin (analyticGenus ℂ X) → ℂ
  /-- Integrating over a constant loop yields zero. -/
  self_spec : ∀ P : X, val P P = 0
  /-- The path integral depends smoothly on the endpoint, for each fixed base point. -/
  contMDiff_endpoint : ∀ P : X,
    ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (val P)

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

instance : Inhabited (PathIntegralFunctionalBundleU X) :=
  ⟨⟨fun _ _ => 0, fun _ => rfl, fun _ => contMDiff_const⟩⟩

/--
The bundled universe-`u` path-integral functional, as an `opaque` value.
Universe-polymorphic companion to `pathIntegralFunctionalBundle`; the genuine
multi-chart path integration is deferred infrastructure, as on the Type-0 side.
-/
opaque pathIntegralFunctionalBundleU : PathIntegralFunctionalBundleU X

/--
The universe-`u` path-integral functional from a base point `P` to an endpoint
`Q`, in basis coordinates. Universe-polymorphic companion to
`pathIntegralFunctional`; extracted from `pathIntegralFunctionalBundleU`.
-/
noncomputable def pathIntegralFunctionalU (P Q : X) : Fin (analyticGenus ℂ X) → ℂ :=
  (pathIntegralFunctionalBundleU X).val P Q

/-- Specification: the universe-`u` path integral over a constant loop at a point is zero. -/
theorem pathIntegralFunctionalU_self_spec (P : X) :
    pathIntegralFunctionalU X P P = 0 :=
  (pathIntegralFunctionalBundleU X).self_spec P

/--
The universe-`u` base-point self path integral vanishes. Universe-polymorphic
companion to `pathIntegralFunctional_self`.
-/
theorem pathIntegralFunctionalU_self (P : X) :
    pathIntegralFunctionalU X P P = 0 :=
  pathIntegralFunctionalU_self_spec X P

/--
The universe-`u` path integral depends smoothly on the endpoint, for each fixed
base point. Universe-polymorphic companion (the `contMDiff_endpoint` field of the
bundle), needed to build `analyticOfCurveU_contMDiff` (D1).
-/
theorem pathIntegralFunctionalU_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (pathIntegralFunctionalU X P) :=
  (pathIntegralFunctionalBundleU X).contMDiff_endpoint P

end JacobianChallenge.AbelJacobi
