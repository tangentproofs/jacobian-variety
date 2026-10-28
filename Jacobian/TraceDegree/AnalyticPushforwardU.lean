import Jacobian.TraceDegree.PushforwardTraceLiftU
import Jacobian.AbelJacobi.AnalyticOfCurveU
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

## Lattice preservation

Descending the ambient map to the tori needs `pushforwardTraceLift_preserves_latticeU`:
periods of `X` go to periods of `Y`. This used to be "proved" by a `⊥` shortcut — the old
period subgroup was `⊥` because the period pairing was the zero placeholder. With the
genuine period lattice (`Periods/GenuinePeriodLattice.lean`) it is a real statement,
currently a labelled gap (change of variables `∫_{f∘γ} ω = ∫_γ f^*ω`).

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
**The pushforward maps periods to periods.** The ambient pushforward
`pushforwardTraceLiftCLMU f hf` — the transpose of the pullback of forms `f^*` in
basis coordinates — sends the period lattice of `X` into that of `Y`.

GAP (`sorry`), true: a generator of `Λ_X` is `periodVector γ₁ - periodVector γ₂` for
`C¹` paths with common endpoints; its image is `periodVector (f ∘ γ₁) - periodVector (f ∘ γ₂)`
because `∫_{f∘γ} ω = ∫_γ f^*ω` (chain rule in charts) and `∫_γ` is linear in the form;
and `f ∘ γᵢ` are `C¹` paths in `Y` with common endpoints. Needs: linearity of
`pathIntegralViaCover` in `ω` for `C¹` paths, and the change-of-variables lemma.

History: previously proved by the "`⊥` shortcut" — the old period subgroup was `⊥`
because the period pairing was the zero placeholder. With the genuine lattice that
shortcut is gone.
-/
theorem pushforwardTraceLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU X).subgroup,
      pushforwardTraceLiftCLMU f hf v ∈ (periodFullComplexLatticeU Y).subgroup := by
  -- GAP: see docstring.
  sorry

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
