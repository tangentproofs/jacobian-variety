import Jacobian.TraceDegree.AnalyticPullbackContMDiffU
import Jacobian.TraceDegree.TraceFormsIdU
import Jacobian.TraceDegree.TraceFormsBundledCompU

/-!
# Universe-polymorphic analytic-pullback functoriality

This file provides the universe-polymorphic identity/composition laws for the
analytic pullback (E2c of the TraceDegree "E-chain", pullback side):
`analyticPullback_id_applyU` and `analyticPullback_comp_applyU` — the
universe-`u` companions of the Type-0 `analyticPullback_id_apply`
(`PullbackBasis.lean:1724`) / `analyticPullback_comp_apply` (`:1693`), needed by
the public `pullback_id_apply` / `pullback_comp_apply` for `X : Type u`
(Milestone C).

(All `PullbackBasis.lean` references in this file are to retired code:
the file now lives at `Attic/FalseGaps/PullbackBasis.lean` and is not built.)

## Structure (route α — the former frontier-obligation pattern)

The pullback side differs from the pushforward side (E1c, genuinely sorry-free)
in ONE place: its bottom functoriality lemma is the **trace** map's
functoriality `traceFormsBundledLM_id`/`_comp` (contravariant), whose Type-0
proof is the deep branched-cover trace identity — `idBranchedCoverData` +
`isRegularValue_idBranchedCoverData` + `idBranchedCoverData_compatible` +
`traceAtRegularValue_id` + `traceFormsBundled_id` +
`traceFormsBundled_comp_of_nonconstant` (`PullbackBasis.lean:752–1517`), all
defined at `{X Y Z : Type}` with their own ramification/regular-locus/
identity-principle apparatus. (Contrast the pushforward side, whose bottom lemma
`pullbackFormsBundledLM_id`/`_comp` is the pullback-OF-FORMS map, already
universe-polymorphic at `{X Y Z : Type*}` in
`HolomorphicForms/PullbackBundled.lean:179/190`.)

That deep trace identity is isolated here into exactly TWO named obligations
`traceFormsBundledLM_idU` / `traceFormsBundledLM_compU` — exactly as D2 isolated
`pathIntegralFunctional_separates_pointsU` for the Abel content. The ENTIRE
downstream chain — `traceFormsCoordU_id`/`_comp` →
`traceDualPullbackLiftU_id`/`_comp` → `analyticPullback_id_applyU`/`_comp_applyU`
— is proved GENUINELY on top (no sorry of its own). Both obligations have since
been discharged by the "E2-trace-id" route-β work (the universe-`u` port of the
branched-cover trace machinery): `traceFormsBundledLM_idU` delegates to
`TraceFormsIdU.traceFormsBundledLM_id_genuineU` and `traceFormsBundledLM_compU`
to `TraceFormsBundledCompU.traceFormsBundledLM_comp_genuineU`. There are no
sorries in this file.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods JacobianChallenge.ComplexTorus
open JacobianChallenge.AbelJacobi (BasisAnalyticJacobianU)

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [FiniteDimensionalHolomorphicOneForms ℂ Y]
variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]
  [FiniteDimensionalHolomorphicOneForms ℂ Z]

/-!
### The two deep branched-cover trace-identity obligations (both discharged)

The universe-`u` companions of the Type-0 `traceFormsBundledLM_id`
(`PullbackBasis.lean:954`) / `traceFormsBundledLM_comp` (`:1477`). Their genuine
proofs are the branched-cover trace identity (id case: identity principle on the
dense regular locus of `idBranchedCoverData`; comp case:
`traceFormsBundled_comp_of_nonconstant` plus the constant-map vanishing). Both
were discharged at `Type u` by the "E2-trace-id" task, in `TraceFormsIdU.lean`
and `TraceFormsBundledCompU.lean`; the two statements below just re-export them.
-/

omit [FiniteDimensionalHolomorphicOneForms ℂ X] in
/-- **Universe-`u` trace functoriality along `id`** — GENUINELY DISCHARGED (R-id).
Companion of the Type-0 `traceFormsBundledLM_id` (`PullbackBasis.lean:954`); the
genuine proof is `TraceFormsIdU.traceFormsBundledLM_id_genuineU` (the id-case
branched-cover chain ported to `Type u`, no sorry). -/
theorem traceFormsBundledLM_idU :
    traceFormsBundledLM (X := X) (Y := X) (id : X → X) contMDiff_id = LinearMap.id :=
  TraceFormsIdU.traceFormsBundledLM_id_genuineU

/-- **Universe-`u` trace functoriality along `g ∘ f`** — GENUINELY DISCHARGED
(R-comp). Companion of the Type-0 `traceFormsBundledLM_comp`
(`PullbackBasis.lean:1477`); the genuine proof is
`TraceFormsBundledCompU.traceFormsBundledLM_comp_genuineU` (no sorry). -/
theorem traceFormsBundledLM_compU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceFormsBundledLM (X := X) (Y := Z) (g ∘ f) (hg.comp hf) =
      (traceFormsBundledLM (X := Y) (Y := Z) g hg).comp
        (traceFormsBundledLM (X := X) (Y := Y) f hf) :=
  JacobianChallenge.TraceDegree.TraceFormsBundledCompU.traceFormsBundledLM_comp_genuineU f hf g hg

/-!
### Genuine downstream assembly (no sorry of its own)

`traceFormsCoordU` / `traceDualPullbackLiftU` functoriality, then the
`analyticPullbackU` identity/composition laws.
-/

/-- Identity functoriality of `traceFormsCoordU`. -/
theorem traceFormsCoordU_id :
    traceFormsCoordU (X := X) (Y := X) id contMDiff_id = LinearMap.id := by
  unfold traceFormsCoordU
  rw [traceFormsBundledLM_idU]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
  rw [LinearEquiv.apply_symm_apply]

/-- Composition functoriality of `traceFormsCoordU` (covariant on the trace). -/
theorem traceFormsCoordU_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceFormsCoordU (g ∘ f) (hg.comp hf) =
      (traceFormsCoordU g hg).comp (traceFormsCoordU f hf) := by
  unfold traceFormsCoordU
  rw [traceFormsBundledLM_compU f hf g hg]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Identity functoriality of the dual-pullback trace lift. -/
theorem traceDualPullbackLiftU_id :
    traceDualPullbackLiftU (X := X) (Y := X) id contMDiff_id = LinearMap.id := by
  unfold traceDualPullbackLiftU
  rw [traceFormsCoordU_id, LinearMap.toMatrix'_id, Matrix.transpose_one, Matrix.toLin'_one]

/-- Composition functoriality of the dual-pullback trace lift (contravariant). -/
theorem traceDualPullbackLiftU_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceDualPullbackLiftU (g ∘ f) (hg.comp hf) =
      (traceDualPullbackLiftU f hf).comp (traceDualPullbackLiftU g hg) := by
  apply LinearMap.ext
  intro v
  show (Matrix.toLin' ((traceFormsCoordU (g ∘ f) (hg.comp hf)).toMatrix').transpose) v =
    (Matrix.toLin' ((traceFormsCoordU f hf).toMatrix').transpose)
      ((Matrix.toLin' ((traceFormsCoordU g hg).toMatrix').transpose) v)
  rw [traceFormsCoordU_comp f hf g hg, LinearMap.toMatrix'_comp,
      Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.comp_apply]

/-- **Pullback along the identity is the identity.** Universe-`u` companion of the
Type-0 `analyticPullback_id_apply` (`PullbackBasis.lean:1724`). -/
theorem analyticPullback_id_applyU (P : BasisAnalyticJacobianU X) :
    analyticPullbackU (X := X) (Y := X) id contMDiff_id P = P := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [show (QuotientAddGroup.mk v : BasisAnalyticJacobianU X)
          = ComplexTorus.mk _ (periodFullComplexLatticeU X) v from rfl]
    rw [analyticPullback_mk_spec_rawU id contMDiff_id v]
    congr 1
    show (traceDualPullbackLiftCLMU (X := X) (Y := X) id contMDiff_id) v = v
    have : (traceDualPullbackLiftCLMU (X := X) (Y := X) id contMDiff_id : _ → _) v
        = traceDualPullbackLiftU (X := X) (Y := X) id contMDiff_id v := rfl
    rw [this, traceDualPullbackLiftU_id]
    rfl

/-- **Pullback distributes contravariantly over composition.** Universe-`u`
companion of the Type-0 `analyticPullback_comp_apply`
(`PullbackBasis.lean:1693`). -/
theorem analyticPullback_comp_applyU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobianU Z) :
    analyticPullbackU (g ∘ f) (hg.comp hf) P =
      analyticPullbackU f hf (analyticPullbackU g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [show (QuotientAddGroup.mk v : BasisAnalyticJacobianU Z)
          = ComplexTorus.mk _ (periodFullComplexLatticeU Z) v from rfl]
    rw [analyticPullback_mk_spec_rawU (g ∘ f) (hg.comp hf) v]
    rw [analyticPullback_mk_spec_rawU g hg v]
    rw [analyticPullback_mk_spec_rawU f hf (traceDualPullbackLiftCLMU g hg v)]
    congr 1
    show (traceDualPullbackLiftCLMU (g ∘ f) (hg.comp hf)) v
        = (traceDualPullbackLiftCLMU f hf) ((traceDualPullbackLiftCLMU g hg) v)
    have e1 : (traceDualPullbackLiftCLMU (g ∘ f) (hg.comp hf) : _ → _) v
        = traceDualPullbackLiftU (g ∘ f) (hg.comp hf) v := rfl
    have e2 : (traceDualPullbackLiftCLMU f hf : _ → _) ((traceDualPullbackLiftCLMU g hg) v)
        = traceDualPullbackLiftU f hf (traceDualPullbackLiftU g hg v) := rfl
    rw [e1, e2, traceDualPullbackLiftU_comp f hf g hg, LinearMap.comp_apply]

end JacobianChallenge.TraceDegree
