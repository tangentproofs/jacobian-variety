import Jacobian.TraceDegree.AnalyticDegreeU
import Jacobian.TraceDegree.PushforwardTraceLiftU
import Jacobian.TraceDegree.AnalyticPushforwardContMDiffU
import Jacobian.TraceDegree.TracePullbackProviderU
import Jacobian.ComplexTorus.Smul

/-!
# Universe-polymorphic trace identity (push-pull = degree)

This file provides the universe-polymorphic trace identity
`analyticPushforward_analyticPullbackU` (E3b of the TraceDegree "E-chain") —
`analyticPushforwardU f hf (analyticPullbackU f hf Q) = analyticDegreeU f hf • Q`
— the universe-`u` companion of the Type-0 `analyticPushforward_analyticPullback`
(`AnalyticDegree.lean:476`), which is what the public `pushforward_pullback`
(`Solution.lean:175`) ultimately calls.

## Structure (route α — the former frontier-obligation pattern)

The Type-0 descent (`AnalyticDegree.lean`): `analyticPushPull_provider` (`:371`) ←
vector-level `pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul` (`:316`)
← matrix-level `traceFormsCoord_holomorphicTraceCoord_eq_degree_smul` (`:254`) ←
LM-level `traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul` (`:236`) ←
`trace_pullback_provider` (`:191`), the DEEP branched-cover trace-of-pullback =
degree·form identity (`traceFormsRegularSpec_provider` +
`branchedCoverData_of_nonconstant_holomorphic` + the regular-locus identity
principle + `trace_pullback_at_regular_value`), `{X Y : Type}`-bound.

The obligation is cut at the LM level: the single named obligation
`traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU` (companion
of `:236`) isolates exactly `trace_pullback_provider`. Everything above it — the
matrix-level and vector-level identities and the quotient descent — is proved
GENUINELY on top (pure linear algebra over the `Type 0` carriers `Fin g → ℂ`,
plus the universe-`u` descent lemmas `analyticPullback_mk_spec_rawU` /
`analyticPushforward_mk_spec_rawU`). The `⊥`-shortcut does NOT apply here:
`mk`-equality on the period quotient needs EXACT representative equality
`pushforwardTraceLiftCLMU (traceDualPullbackLiftCLMU v) = deg • v`, so the deep
identity is genuinely required (hence the one obligation, exactly as E2c).

The obligation has since been discharged by the route-β work (the full
universe-`u` port of the branched-cover trace machinery): it delegates to
`TracePullbackProviderU.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU`.
There are no sorries in this file.
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

omit [FiniteDimensionalHolomorphicOneForms ℂ X] [FiniteDimensionalHolomorphicOneForms ℂ Y] [CompactSpace Y] in
/-- **Universe-`u` trace-of-pullback = degree** — GENUINELY DISCHARGED (R-tracepullback).
Companion of the Type-0 `traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul`
(`AnalyticDegree.lean:236`); the genuine proof is
`TracePullbackProviderU.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU`
(the branched-cover trace-of-pullback identity `trace_pullback_provider` ported to
`Type u`, no sorry). -/
theorem traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
      (analyticDegreeU f hf : ℂ) • LinearMap.id :=
  TracePullbackProviderU.traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul_genuineU f hf

/-!
### Genuine descent (no sorry of its own)
-/

omit [CompactSpace Y] in
/-- **Matrix-level trace-pullback identity.** Companion of
`traceFormsCoord_holomorphicTraceCoord_eq_degree_smul` (`AnalyticDegree.lean:254`). -/
theorem traceFormsCoordU_holomorphicTraceCoordU_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsCoordU f hf).comp (holomorphicTraceCoordU f hf) =
      (analyticDegreeU f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  show (traceFormsCoordU f hf) (holomorphicTraceCoordU f hf v) =
    (analyticDegreeU f hf : ℂ) • v
  unfold traceFormsCoordU holomorphicTraceCoordU
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  have happ := LinearMap.congr_fun
    (traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smulU f hf)
    ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at happ
  rw [happ, map_smul, LinearEquiv.apply_symm_apply]

omit [CompactSpace Y] in
/-- **Vector-level trace-pullback identity.** Companion of
`pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul` (`AnalyticDegree.lean:316`):
`pushforwardTraceLiftU ∘ traceDualPullbackLiftU = (analyticDegreeU : ℂ) • id`. -/
theorem pushforwardTraceLiftU_traceDualPullbackLiftU_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (pushforwardTraceLiftLinearMapU f hf).comp (traceDualPullbackLiftU f hf) =
      (analyticDegreeU f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  show (Matrix.toLin' ((holomorphicTraceCoordU f hf).toMatrix').transpose)
      ((Matrix.toLin' ((traceFormsCoordU f hf).toMatrix').transpose) v) =
    (analyticDegreeU f hf : ℂ) • v
  set P := (holomorphicTraceCoordU f hf).toMatrix' with hP_def
  set T := (traceFormsCoordU f hf).toMatrix' with hT_def
  have hstep1 :
      (Matrix.toLin' P.transpose) ((Matrix.toLin' T.transpose) v) =
        (Matrix.toLin' (P.transpose * T.transpose)) v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul]
  rw [hstep1]
  rw [show P.transpose * T.transpose = (T * P).transpose from
    (Matrix.transpose_mul T P).symm]
  have hPmul :
      T * P = ((traceFormsCoordU f hf).comp (holomorphicTraceCoordU f hf)).toMatrix' := by
    rw [hT_def, hP_def]
    exact (LinearMap.toMatrix'_comp _ _).symm
  rw [hPmul, traceFormsCoordU_holomorphicTraceCoordU_eq_degree_smul f hf]
  simp only [map_smul, LinearMap.toMatrix'_id, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply]

/-- **The trace identity at `Type u`.** Universe-`u` companion of
`analyticPushforward_analyticPullback` (`AnalyticDegree.lean:476`):
`analyticPushforwardU f hf (analyticPullbackU f hf Q) = analyticDegreeU f hf • Q`.
Needed by the public `pushforward_pullback` for `X : Type u` (Milestone C). -/
theorem analyticPushforward_analyticPullbackU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobianU Y) :
    analyticPushforwardU f hf (analyticPullbackU f hf Q) =
      (analyticDegreeU f hf) • Q := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLatticeU Y) Q
  rw [show (analyticPullbackU f hf (ComplexTorus.mk _ (periodFullComplexLatticeU Y) v))
        = ComplexTorus.mk _ (periodFullComplexLatticeU X)
            (traceDualPullbackLiftCLMU f hf v) from
    analyticPullback_mk_spec_rawU f hf v]
  rw [analyticPushforward_mk_spec_rawU f hf (traceDualPullbackLiftCLMU f hf v)]
  have hvec :
      pushforwardTraceLiftCLMU f hf (traceDualPullbackLiftCLMU f hf v) =
        (analyticDegreeU f hf : ℂ) • v := by
    have h := pushforwardTraceLiftU_traceDualPullbackLiftU_eq_degree_smul f hf
    have happ := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at happ
    exact happ
  rw [show pushforwardTraceLiftCLMU f hf (traceDualPullbackLiftCLMU f hf v)
        = (analyticDegreeU f hf : ℂ) • v from hvec]
  rw [Nat.cast_smul_eq_nsmul ℂ (analyticDegreeU f hf) v]
  exact mk_nsmul (periodFullComplexLatticeU Y) (analyticDegreeU f hf) v

end JacobianChallenge.TraceDegree
