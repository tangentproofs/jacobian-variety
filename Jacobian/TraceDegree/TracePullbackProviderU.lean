import Jacobian.TraceDegree.AnalyticDegreeU
import Jacobian.TraceDegree.PullbackBasis

/-!
# Universe-polymorphic trace-of-pullback = degree identity (route-β, E3b)

This file genuinely discharges the universe-`u` trace-of-pullback identity
`(traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
(analyticDegreeU f hf : ℂ) • LinearMap.id`
(`traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU`) — the E3b route-β
obligation
`JacobianChallenge.TraceDegree.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU`
(declared as a tracked frontier `sorry` in `AnalyticPushPullU.lean`, companion of
the Type-0 `traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul` in
`AnalyticDegree.lean:236`).

The proof ports the Type-0 `trace_pullback_provider` (`AnalyticDegree.lean:191`)
to independent universes `{X : Type u} {Y : Type v}`: case on whether `f` is
constant (both sides vanish) or nonconstant (identity principle on the dense
regular locus, via `trace_pullback_at_regular_value`). Nearly the entire chain is
already universe-polymorphic (`regularLocus_dense`, `trace_pullback_at_regular_value`
in `TraceDefinition`; `branchedCoverData_of_nonconstant_holomorphic`(+`_compatible`)
in `Blueprint/Sec02`; the `HolomorphicMap` providers; `branchedDegree_eq_weightedFiberCard`;
`TraceFormsRegularSpec` in `TraceSpec`). The only Type-0-bound pieces are the two
providers in `AnalyticDegree` (`traceFormsRegularSpec_provider`,
`hasWeightedFiberConservation_provider`), restated here verbatim (their bodies use
only `Type*` primitives), plus the degree well-definedness lemmas already ported
in E3a (`analyticDegree_constantU` / `analyticDegree_eq_canonical_branchedDegreeU`
from `AnalyticDegreeU`).

Genuine — no sorry.
-/

namespace JacobianChallenge.TraceDegree.TracePullbackProviderU

open scoped Manifold ContDiff Topology
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

/-- The regular-value trace provider at `Type u`. Restatement of the Type-0
`traceFormsRegularSpec_provider` (`AnalyticDegree.lean:166`); its body uses only
the already-`Type*` `traceFormsConstructionData_provider`. -/
noncomputable def traceFormsRegularSpec_providerU (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    TraceFormsRegularSpec f hf where
  map_zero := by
    change (traceFormsConstructionData_provider f hf 0).traceForm = 0
    exact (traceFormsConstructionData_provider f hf 0).map_zero_spec rfl
  apply_fun_regular := by
    intro hbc hcompat η y hy
    change (traceFormsConstructionData_provider f hf η).traceForm.toFun y = _
    exact (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [FiniteDimensionalHolomorphicOneForms ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] [FiniteDimensionalHolomorphicOneForms ℂ Y] in
/-- Weighted-fibre conservation at `Type u`. Restatement of the Type-0
`hasWeightedFiberConservation_provider` (`AnalyticDegree.lean:157`). -/
theorem hasWeightedFiberConservation_providerU (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HasWeightedFiberConservation f :=
  hasWeightedFiberConservation_of_contMDiff hf

omit [FiniteDimensionalHolomorphicOneForms ℂ X] [FiniteDimensionalHolomorphicOneForms ℂ Y] in
/-- **Trace-of-pullback = degree on holomorphic 1-forms** at `Type u`. Universe-`u`
companion of the deep Type-0 `trace_pullback_provider` (`AnalyticDegree.lean:191`):
`traceFormsBundled (pullbackFormsBundled η) = analyticDegreeU • η`. Case split on
`f` constant (both 0) / nonconstant (regular-locus identity principle). Reuses
E3a's `analyticDegreeU` well-definedness. -/
theorem trace_pullback_providerU (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (analyticDegreeU f hf : ℂ) • η := by
  classical
  set htrace : TraceFormsRegularSpec f hf := traceFormsRegularSpec_providerU f hf with htrace_def
  set hkfold : HasLocalKfoldRamification f := hasLocalKfoldRamification_of_contMDiff hf
    with hkfold_def
  set hw : HasWeightedFiberConservation f := hasWeightedFiberConservation_providerU f hf
    with hw_def
  have hHol : IsHolomorphic f := isHolomorphic_of_contMDiff hf hkfold
  by_cases hconst : ∃ y₀, ∀ x, f x = y₀
  · -- Constant case: both sides are zero.
    have hpb_zero : pullbackFormsBundled f hf η = 0 := by
      apply ContMDiffSection.coe_inj
      funext x
      obtain ⟨y₀, hf_const⟩ := hconst
      have hf_eq : f = fun _ : X => y₀ := funext hf_const
      subst f
      simp [pullbackFormsBundled, pullbackFormsFunFiber, mfderiv_const]
    rw [hpb_zero, htrace.map_zero, analyticDegree_constantU f hf hconst]
    apply ContMDiffSection.ext
    intro y
    simp
  · -- Nonconstant case: descend through the regular locus by the identity principle.
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      hHol hw hconst with hbc_def
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        hHol hw hconst
    have hdeg : analyticDegreeU f hf = branchedDegree hbc :=
      analyticDegree_eq_canonical_branchedDegreeU f hf hHol hbc hcompat hconst
    rw [hdeg]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y,
        htrace.apply_fun_regular hbc hcompat (pullbackFormsBundled f hf η) y hy]
    exact trace_pullback_at_regular_value hbc hcompat hf hHol η y hy

omit [FiniteDimensionalHolomorphicOneForms ℂ X] [FiniteDimensionalHolomorphicOneForms ℂ Y] in
/-- **The genuine trace-of-pullback = degree identity** (linear-map level) at
`Type u`: `(traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
(analyticDegreeU f hf : ℂ) • LinearMap.id`. This is the genuine discharge of the
E3b route-β obligation
`JacobianChallenge.TraceDegree.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU`. -/
theorem traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
      (analyticDegreeU f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro η
  show traceFormsBundledLM f hf (pullbackFormsBundledLM X Y f hf η) =
    (analyticDegreeU f hf : ℂ) • η
  show traceFormsBundled f hf (pullbackFormsBundled f hf η) = _
  exact trace_pullback_providerU f hf η

end JacobianChallenge.TraceDegree.TracePullbackProviderU
