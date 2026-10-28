import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Universe-polymorphic trace-lift maps

`Jacobian/TraceDegree/PushforwardBasis.lean` builds the analytic pushforward
`analyticPushforward f hf : BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y`
from the trace-coordinate map `holomorphicTraceCoord f hf` and its transpose
`pushforwardTraceLiftCLM` (a continuous ℂ-linear map between the basis-aligned
coordinate spaces `Fin g → ℂ`), all at universe 0 (`{X Y : Type}`).

This file provides the universe-polymorphic companions
`holomorphicTraceCoordU` / `pushforwardTraceLiftLinearMapU` /
`pushforwardTraceLiftCLMU` (E0 of the TraceDegree "E-chain" — the universe-`u`
generalization of the functorial layer, mirroring the Abel-Jacobi D-chain). They
are the foundation on which the universe-`u` `analyticPushforwardU` (E1) — and
hence the public `pushforward` for `X : Type u` (Milestone C) — will be built.

The maps' carriers `Fin (analyticGenus ℂ X) → ℂ` / `Fin (analyticGenus ℂ Y) → ℂ`
are `Type 0` for any `X Y : Type u`; only the binders `{X Y : Type}` need widening
to `{X Y : Type u}`. The underlying `pullbackFormsBundledLM` /
`holomorphicOneFormFinBasis` are already universe-polymorphic, so every
declaration here is a verbatim mirror of its Type-0 original. No sorry, no
frontier obligation, no `MeromorphicMapToSphere` reference — these are genuine
linear-algebra maps (chain-rule pullback of forms in basis coordinates,
transposed to the covariant direction).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

/--
The trace-coordinate map for `X Y : Type u`: the basis-coordinate form of the
chain-rule pullback `f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)` (contravariant direction).
Universe-polymorphic companion to `holomorphicTraceCoord`.
-/
noncomputable def holomorphicTraceCoordU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y] :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  (holomorphicOneFormFinBasis ℂ X).equivFun.toLinearMap ∘ₗ
    (pullbackFormsBundledLM X Y f hf) ∘ₗ
    (holomorphicOneFormFinBasis ℂ Y).equivFun.symm.toLinearMap

/--
The covariant trace-lift linear map for `X Y : Type u`: the matrix transpose of
`holomorphicTraceCoordU`. Universe-polymorphic companion to
`pushforwardTraceLiftLinearMap`.
-/
noncomputable def pushforwardTraceLiftLinearMapU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y] :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  Matrix.toLin' (holomorphicTraceCoordU f hf).toMatrix'.transpose

/--
The covariant trace-lift continuous ℂ-linear map for `X Y : Type u`.
Universe-polymorphic companion to `pushforwardTraceLiftCLM`.
-/
noncomputable def pushforwardTraceLiftCLMU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y] :
    (Fin (analyticGenus ℂ X) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  LinearMap.toContinuousLinearMap (pushforwardTraceLiftLinearMapU f hf)

end JacobianChallenge.TraceDegree
