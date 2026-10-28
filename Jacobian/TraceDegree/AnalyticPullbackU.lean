import Jacobian.TraceDegree.PullbackTraceLiftU
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.ComplexTorus.OfClm

/-!
# Universe-polymorphic analytic pullback

`Jacobian/TraceDegree/PullbackBasis.lean` defines the Type-0 analytic pullback
`analyticPullback f hf : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X`
(the contravariant `Y → X` direction) as the descent of the dual-pullback
trace-lift continuous linear map `traceDualPullbackLiftCLM` through the
period-lattice quotient, via `ComplexTorus.mapClm` and a lattice-preservation
obligation.

This file provides the universe-polymorphic companion `analyticPullbackU`
(E2-core of the TraceDegree "E-chain", pullback side), landing in the
universe-`u` quotient `BasisAnalyticJacobianU Y →ₜ+ BasisAnalyticJacobianU X`
(D1) — which, under `ULift.{u}`, underlies the public `pullback` for `X : Type u`
(Milestone C). It is built on the E2a dual-pullback trace-lift CLM
`traceDualPullbackLiftCLMU`.

## Lattice preservation

Descending the ambient map needs `traceDualPullbackLift_preserves_latticeU`: periods of
`Y` go to periods of `X` under the transpose of the trace. This used to be "proved" by a
`⊥` shortcut (old period subgroup `⊥`). With the genuine period lattice it is a real
statement, currently a labelled gap (lifting closed curves through the branched cover).

The continuous-smoothness lemma `analyticPullback_contMDiffU` and the
functoriality laws are deferred to E2b / E2c.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods JacobianChallenge.ComplexTorus
open JacobianChallenge.AbelJacobi (BasisAnalyticJacobianU)

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
**The pullback maps periods to periods.** The ambient pullback
`traceDualPullbackLiftCLMU f hf` — the transpose of the trace of forms in basis
coordinates — sends the period lattice of `Y` into that of `X` (contravariant).

GAP (`sorry`), true classically: for a closed curve `c` in `Y`, `∫_c tr(ω) = ∫_{f^*c} ω`
where `f^*c` is the lift of `c` through the branched cover `f` (a sum of closed curves in
`X` once `c` avoids the finitely many branch values, which it can after a homotopy).

History: previously proved by the "`⊥` shortcut" (old period subgroup `⊥`).
-/
theorem traceDualPullbackLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU Y).subgroup,
      traceDualPullbackLiftCLMU f hf v ∈ (periodFullComplexLatticeU X).subgroup := by
  -- GAP: see docstring.
  sorry

/--
The universe-`u` analytic pullback induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier (contravariant `Y → X`).
Universe-polymorphic companion to `analyticPullback`; the descent of
`traceDualPullbackLiftCLMU` through the universe-`u` period quotient via
`ComplexTorus.mapClm`.
-/
noncomputable def analyticPullbackU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobianU Y →ₜ+ BasisAnalyticJacobianU X where
  toFun := ComplexTorus.mapClm (traceDualPullbackLiftCLMU f hf)
    (traceDualPullbackLift_preserves_latticeU f hf)
  map_zero' := (ComplexTorus.mapClm _ _).map_zero
  map_add' := (ComplexTorus.mapClm _ _).map_add
  continuous_toFun :=
    ComplexTorus.mapClm_continuous (traceDualPullbackLiftCLMU f hf)
      (traceDualPullbackLift_preserves_latticeU f hf)

end JacobianChallenge.TraceDegree
