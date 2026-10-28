import Jacobian.TraceDegree.PullbackTraceLiftU
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.Periods.PeriodSubgroupZLatticeU
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

## A sorry-free simplification (the `⊥` shortcut, as in E1-core)

The Type-0 lattice-preservation proof `traceDualPullbackLift_preserves_lattice_raw`
is deep. But the universe-`u` period subgroup is the trivial subgroup `⊥`
(`basisAlignedPeriodSubgroupConcreteU_eq_bot`, because the period pairing is
currently the `0` placeholder). Hence `traceDualPullbackLift_preserves_latticeU`
collapses to "`v ∈ ⊥ → CLMU v ∈ ⊥`", i.e. `v = 0 ⇒ map_zero` — proved in three
lines, no naturality chain. Same `⊥`-shortcut that made the pushforward E1-core
preserves-lattice sorry-free.

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
The universe-`u` dual-pullback trace lift preserves the period lattice.
Universe-polymorphic companion to `traceDualPullbackLift_preserves_lattice_raw`,
proved sorry-free via the `⊥` shortcut (the universe-`u` period subgroup is
trivial; see the module docstring): `v ∈ ⊥ ⇒ v = 0 ⇒ CLMU v = 0 ∈ ⊥`. Note the
contravariant `Y → X` direction.
-/
theorem traceDualPullbackLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU Y).subgroup,
      traceDualPullbackLiftCLMU f hf v ∈ (periodFullComplexLatticeU X).subgroup := by
  intro v hv
  have hvbot : v ∈ basisAlignedPeriodSubgroupConcreteU Y := hv
  rw [basisAlignedPeriodSubgroupConcreteU_eq_bot Y, AddSubgroup.mem_bot] at hvbot
  show traceDualPullbackLiftCLMU f hf v ∈ basisAlignedPeriodSubgroupConcreteU X
  rw [basisAlignedPeriodSubgroupConcreteU_eq_bot X, AddSubgroup.mem_bot, hvbot, map_zero]

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
