import Jacobian.TraceDegree.PullbackTraceLiftU
import Jacobian.TraceDegree.TracePeriods
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.ComplexTorus.OfClm

/-!
# Universe-polymorphic analytic pullback

`PullbackBasis.lean` (retired; now `Attic/FalseGaps/PullbackBasis.lean`, not
built) defined the Type-0 analytic pullback
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
statement, proved in `TraceDegree/TracePeriods.lean` without lifting curves.

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

Proof: for constant `f` the trace is `0` and so is the map. Otherwise
`traceDualPullbackLift_genuinePeriods`: for a chain `l` from `P` to `Q` in `Y`,
`(∫_l Tr ω_j)_j ≡ Φ(Q) − Φ(P)` modulo the periods of `X`, where `Φ` is the
multiplicity-weighted sum over the fibre of chosen integrals from a base point of `X`.

History: previously proved by the "`⊥` shortcut" (old period subgroup `⊥`), then a
labelled gap.
-/
theorem traceDualPullbackLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU Y).subgroup,
      traceDualPullbackLiftCLMU f hf v ∈ (periodFullComplexLatticeU X).subgroup := by
  classical
  intro v hv
  rw [periodFullComplexLatticeU_subgroup] at hv ⊢
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · have h0 : traceDualPullbackLiftCLMU f hf v = 0 := by
      funext j
      simp only [traceDualPullbackLiftCLMU, LinearMap.coe_toContinuousLinearMap',
        traceDualPullbackLiftLinearMapU, traceDualPullbackLiftU, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : traceFormsCoordU f hf (Pi.single j 1) = 0 := by
        show (holomorphicOneFormFinBasis ℂ Y).equivFun.toLinearMap
          (traceFormsBundled f hf _) = 0
        rw [traceFormsBundled_eq_zero_of_constant _ hconst, map_zero]
      rw [hz, Pi.zero_apply, zero_mul]
    rw [h0]
    exact zero_mem _
  · set hkfold := hasLocalKfoldRamification_of_contMDiff hf
    set hw := hasWeightedFiberConservation_of_contMDiff hf
    set hHol := isHolomorphic_of_contMDiff hf hkfold
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      hHol hw hconst
    exact traceDualPullbackLift_genuinePeriods hf hbc.finite_fiber hconst v hv

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
