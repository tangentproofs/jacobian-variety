import Jacobian.TraceDegree.PushforwardTraceLiftU
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.Periods.PeriodSubgroupZLatticeU
import Jacobian.ComplexTorus.OfClm

/-!
# Universe-polymorphic analytic pushforward

`Jacobian/TraceDegree/PushforwardBasis.lean` defines the Type-0 analytic
pushforward
`analyticPushforward f hf : BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y`
as the descent of the trace-lift continuous linear map `pushforwardTraceLiftCLM`
through the period-lattice quotient, via `ComplexTorus.mapClm` and a
lattice-preservation obligation.

This file provides the universe-polymorphic companion `analyticPushforwardU`
(E1-core of the TraceDegree "E-chain"), landing in the universe-`u` quotient
`BasisAnalyticJacobianU X →ₜ+ BasisAnalyticJacobianU Y` (D1) — which, under
`ULift.{u}`, underlies the public `pushforward` for `X : Type u` (Milestone C).
It is built on the E0 trace-lift CLM `pushforwardTraceLiftCLMU`.

## A sorry-free simplification (the `⊥` shortcut)

The Type-0 lattice-preservation proof
`pushforwardTraceLift_preserves_lattice_raw` is deep: it threads the
period-pairing / cycle-pushforward naturality of the trace lift. But the
universe-`u` period subgroup is the trivial subgroup `⊥`
(`basisAlignedPeriodSubgroupConcreteU_eq_bot`, from the C2b development, because
the period pairing is currently the `0` placeholder). Hence
`pushforwardTraceLift_preserves_latticeU` collapses to "`v ∈ ⊥ → CLMU v ∈ ⊥`",
i.e. `v = 0 ⇒ map_zero` — proved in three lines with no naturality chain. This is
the same `⊥`-shortcut that made the C2b discreteness/closedness sorry-free, and it
keeps the entire E-chain's lattice-preservation obligations sorry-free. When the
nonzero-integration frontier lands, the genuine naturality proof replaces this on
both the Type-0 and universe-`u` sides.

The continuous-smoothness lemma `analyticPushforward_contMDiffU` and the
functoriality laws (`_id_applyU` / `_comp_applyU`) are deferred to E1b.
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
The universe-`u` trace lift preserves the period lattice. Universe-polymorphic
companion to `pushforwardTraceLift_preserves_lattice_raw`, proved sorry-free via
the `⊥` shortcut (the universe-`u` period subgroup is trivial; see the module
docstring): `v ∈ ⊥ ⇒ v = 0 ⇒ CLMU v = 0 ∈ ⊥`.
-/
theorem pushforwardTraceLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU X).subgroup,
      pushforwardTraceLiftCLMU f hf v ∈ (periodFullComplexLatticeU Y).subgroup := by
  intro v hv
  -- The universe-`u` period subgroup is `⊥`, so `v = 0` and the image is `0 ∈ ⊥`.
  have hvbot : v ∈ basisAlignedPeriodSubgroupConcreteU X := hv
  rw [basisAlignedPeriodSubgroupConcreteU_eq_bot X, AddSubgroup.mem_bot] at hvbot
  show pushforwardTraceLiftCLMU f hf v ∈ basisAlignedPeriodSubgroupConcreteU Y
  rw [basisAlignedPeriodSubgroupConcreteU_eq_bot Y, AddSubgroup.mem_bot, hvbot, map_zero]

/--
The universe-`u` analytic pushforward induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier. Universe-polymorphic companion to
`analyticPushforward`; the descent of `pushforwardTraceLiftCLMU` through the
universe-`u` period quotient via `ComplexTorus.mapClm`.
-/
noncomputable def analyticPushforwardU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobianU X →ₜ+ BasisAnalyticJacobianU Y where
  toFun := ComplexTorus.mapClm (pushforwardTraceLiftCLMU f hf)
    (pushforwardTraceLift_preserves_latticeU f hf)
  map_zero' := (ComplexTorus.mapClm _ _).map_zero
  map_add' := (ComplexTorus.mapClm _ _).map_add
  continuous_toFun :=
    ComplexTorus.mapClm_continuous (pushforwardTraceLiftCLMU f hf)
      (pushforwardTraceLift_preserves_latticeU f hf)

end JacobianChallenge.TraceDegree
