import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Jacobian.HolomorphicForms.TraceSpec

/-!
# Universe-polymorphic pullback trace-lift maps

`PullbackBasis.lean` (retired; now `Attic/FalseGaps/PullbackBasis.lean`, not
built) built the analytic pullback
`analyticPullback f hf : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X`
from the trace-forms coordinate map `traceFormsCoord` and the dual-pullback
trace-lift `traceDualPullbackLift` (the transpose of `traceFormsCoord`), at
universe 0.

This file provides the universe-polymorphic companions `traceFormsCoordU` /
`traceDualPullbackLiftU` / `traceDualPullbackLiftLinearMapU` /
`traceDualPullbackLiftCLMU` (E2a of the TraceDegree "E-chain", pullback side —
the analogue of E0 on the pushforward side). They are the foundation on which the
universe-`u` `analyticPullbackU` (E2-core) — and hence the public `pullback` for
`X : Type u` (Milestone C) — will be built.

These maps are GENUINE (no sorry): the underlying `traceFormsBundledLM` has been
generalized to `Type*` in `Jacobian/HolomorphicForms/TraceSpec.lean` (a clean
binder-widen of its variable block, performed AFTER jc3's R-build merged, since
the deep dependencies `BranchedCoverData` /
`branchedCoverData_of_nonconstant_holomorphic` were already universe-polymorphic;
the widen was verified to leave jc3's R-leaves building unchanged). The matrix /
linear-map machinery (`holomorphicOneFormFinBasis.equivFun`, `Matrix.toLin'`,
transpose) is universe-polymorphic. Every declaration is a verbatim mirror of its
Type-0 original (`traceFormsCoord` / `traceDualPullbackLift*` in
`PullbackBasis.lean`).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [FiniteDimensionalHolomorphicOneForms ℂ Y]

/--
The trace-forms coordinate map for `X Y : Type u`: the basis-coordinate form of
the trace map on holomorphic 1-forms (the cycle-pushforward-dual direction).
Universe-polymorphic companion to `traceFormsCoord`.
-/
noncomputable def traceFormsCoordU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  (holomorphicOneFormFinBasis ℂ Y).equivFun.toLinearMap ∘ₗ
    (traceFormsBundledLM f hf) ∘ₗ
    (holomorphicOneFormFinBasis ℂ X).equivFun.symm.toLinearMap

/--
The dual-pullback trace-lift linear map for `X Y : Type u`: the matrix transpose
of `traceFormsCoordU`, the correct representative for Jacobian pullback.
Universe-polymorphic companion to `traceDualPullbackLift`.
-/
noncomputable def traceDualPullbackLiftU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  Matrix.toLin' (traceFormsCoordU f hf).toMatrix'.transpose

/--
The dual-pullback trace-lift linear map (alias for `traceDualPullbackLiftU`,
mirroring the Type-0 `traceDualPullbackLiftLinearMap`).
-/
noncomputable def traceDualPullbackLiftLinearMapU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  traceDualPullbackLiftU f hf

/--
The dual-pullback trace-lift as a continuous ℂ-linear map for `X Y : Type u`.
Universe-polymorphic companion to `traceDualPullbackLiftCLM`.
-/
noncomputable def traceDualPullbackLiftCLMU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  LinearMap.toContinuousLinearMap (traceDualPullbackLiftLinearMapU f hf)

end JacobianChallenge.TraceDegree
