import Jacobian.TraceDegree.PushforwardTraceLiftU
import Jacobian.Periods.ChainPushforward
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.ComplexTorus.OfClm

/-!
# Universe-polymorphic analytic pushforward

`PushforwardBasis.lean` (retired; now `Attic/FalseGaps/PushforwardBasis.lean`,
not built) defined the Type-0 analytic
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
and it is proved below from `Periods.exists_pushforward_chain` (the change of
variables `∫_{f∘γ} ω = ∫_γ f^*ω`).

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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] in
/-- The ambient pushforward (transpose of `f^*` in basis coordinates) sends the period vector
of a chain `l` to the period vector of any chain `l'` with `∫_{l'} η = ∫_l f^*η` for all `η`. -/
theorem pushforwardTraceLiftCLMU_periodVector
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (l : List (ChartSegment X)) (l' : List (ChartSegment Y))
    (hl : ∀ η : HolomorphicOneForm ℂ Y,
      chainIntegral η l' = chainIntegral (pullbackFormsBundled f hf η) l) :
    pushforwardTraceLiftCLMU f hf (periodVector X l) = periodVector Y l' := by
  funext j
  simp only [pushforwardTraceLiftCLMU, LinearMap.coe_toContinuousLinearMap',
    pushforwardTraceLiftLinearMapU, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  have hcoord : ∀ i, holomorphicTraceCoordU f hf (Pi.single j 1) i =
      (holomorphicOneFormFinBasis ℂ X).repr
        (pullbackFormsBundled f hf (holomorphicOneFormFinBasis ℂ Y j)) i := by
    intro i
    have h1 : (holomorphicOneFormFinBasis ℂ Y).equivFun.symm (Pi.single j 1) =
        holomorphicOneFormFinBasis ℂ Y j := by
      rw [Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply]
    show (holomorphicOneFormFinBasis ℂ X).equivFun
      (pullbackFormsBundledLM X Y f hf
        ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm (Pi.single j 1))) i = _
    rw [h1, Module.Basis.equivFun_apply]
    rfl
  simp_rw [hcoord]
  rw [show periodVector Y l' j = chainIntegral (holomorphicOneFormFinBasis ℂ Y j) l' from rfl,
    hl]
  conv_rhs => rw [← (holomorphicOneFormFinBasis ℂ X).sum_repr
    (pullbackFormsBundled f hf (holomorphicOneFormFinBasis ℂ Y j))]
  rw [← chainIntegralLM_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, chainIntegralLM_apply, smul_eq_mul]
  rfl

/--
**The pushforward maps periods to periods.** The ambient pushforward
`pushforwardTraceLiftCLMU f hf` — the transpose of the pullback of forms `f^*` in
basis coordinates — sends the period lattice of `X` into that of `Y`.

Proof: a generator of `Λ_X` is `periodVector l₁ - periodVector l₂` for chart chains with
common endpoints `P, Q`; pushing both chains forward (`Periods.exists_pushforward_chain`,
the change of variables `∫_{f∘γ} η = ∫_γ f^*η`) gives chains from `f P` to `f Q` whose
period vectors are the images, so the image is a generator of `Λ_Y`.

History: previously "proved" by a `⊥` shortcut (the old period subgroup was `⊥` because the
period pairing was the zero placeholder), then a labelled gap.
-/
theorem pushforwardTraceLift_preserves_latticeU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLatticeU X).subgroup,
      pushforwardTraceLiftCLMU f hf v ∈ (periodFullComplexLatticeU Y).subgroup := by
  intro v hv
  rw [periodFullComplexLatticeU_subgroup] at hv ⊢
  have hle : genuinePeriodSubgroup X ≤ (genuinePeriodSubgroup Y).comap
      (pushforwardTraceLiftCLMU f hf).toLinearMap.toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨P, Q, l₁, l₂, h₁, h₂, rfl⟩
    obtain ⟨l₁', hl₁', hint₁⟩ := exists_pushforward_chain hf h₁
    obtain ⟨l₂', hl₂', hint₂⟩ := exists_pushforward_chain hf h₂
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show pushforwardTraceLiftCLMU f hf (periodVector X l₁ - periodVector X l₂) ∈
      genuinePeriodSubgroup Y
    rw [map_sub, pushforwardTraceLiftCLMU_periodVector f hf l₁ l₁' hint₁,
      pushforwardTraceLiftCLMU_periodVector f hf l₂ l₂' hint₂]
    exact periodVector_sub_mem hl₁' hl₂'
  exact hle hv

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
