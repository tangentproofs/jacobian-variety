import Jacobian.TraceDegree.AnalyticPushforwardContMDiffU

/-!
# Universe-polymorphic analytic-pushforward functoriality

`Jacobian/TraceDegree/PushforwardBasis.lean` proves the identity/composition laws
of the Type-0 analytic pushforward (`analyticPushforward_id_apply` line 626 /
`analyticPushforward_comp_apply` line 599) by reducing — via `mk_surjective` and
the descent compatibility `analyticPushforward_mk_spec` — to the functoriality of
the trace-lift map, which in turn reduces (through the matrix transpose) to the
functoriality of the trace-coordinate map `holomorphicTraceCoord`.

This file provides the universe-polymorphic companions (E1c of the TraceDegree
"E-chain"), completing the universe-`u` analytic pushforward (def + smoothness
from E1-core/E1b, functoriality here). They are needed by the public
`pushforward_id_apply` / `pushforward_comp_apply` for `X : Type u` (Milestone C).

Every declaration is a verbatim mirror of its Type-0 original; the matrix /
linear-map machinery (`LinearMap.toMatrix'`, `Matrix.transpose`, `Matrix.toLin'`,
`pullbackFormsBundledLM_id`/`_comp`) is universe-polymorphic. Genuine — no sorry;
the only `sorryAx` dependence is transitive, through `periodFullComplexLatticeU`'s
inherited Periods layer-frontier obligations.
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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Identity functoriality of the universe-`u` trace-coordinate map. -/
theorem holomorphicTraceCoord_idU :
    holomorphicTraceCoordU (X := X) (Y := X) id contMDiff_id = LinearMap.id := by
  unfold holomorphicTraceCoordU
  rw [pullbackFormsBundledLM_id]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
  rw [LinearEquiv.apply_symm_apply]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] in
/-- Composition functoriality of the universe-`u` trace-coordinate map. -/
theorem holomorphicTraceCoord_compU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    holomorphicTraceCoordU (g ∘ f) (hg.comp hf) =
      (holomorphicTraceCoordU f hf).comp (holomorphicTraceCoordU g hg) := by
  unfold holomorphicTraceCoordU
  rw [pullbackFormsBundledLM_comp f hf g hg]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The universe-`u` trace-lift linear map along the identity is the identity. -/
theorem pushforwardTraceLiftLinearMapU_id :
    pushforwardTraceLiftLinearMapU (X := X) (Y := X) id contMDiff_id = LinearMap.id := by
  unfold pushforwardTraceLiftLinearMapU
  rw [holomorphicTraceCoord_idU, LinearMap.toMatrix'_id, Matrix.transpose_one,
      Matrix.toLin'_one]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] in
/-- The universe-`u` trace-lift linear map distributes over composition (covariantly). -/
theorem pushforwardTraceLiftLinearMapU_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLiftLinearMapU (g ∘ f) (hg.comp hf) v =
      pushforwardTraceLiftLinearMapU g hg (pushforwardTraceLiftLinearMapU f hf v) := by
  unfold pushforwardTraceLiftLinearMapU
  rw [holomorphicTraceCoord_compU f hf g hg, LinearMap.toMatrix'_comp,
      Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.comp_apply]

/--
Identity functoriality of the universe-`u` analytic pushforward. Universe-
polymorphic companion to `analyticPushforward_id_apply`.
-/
theorem analyticPushforward_id_applyU (P : BasisAnalyticJacobianU X) :
    analyticPushforwardU (X := X) (Y := X) id contMDiff_id P = P := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLatticeU X) P
  rw [analyticPushforward_mk_spec_rawU id contMDiff_id v]
  show ComplexTorus.mk _ (periodFullComplexLatticeU X)
    (pushforwardTraceLiftLinearMapU (X := X) (Y := X) id contMDiff_id v) = _
  rw [pushforwardTraceLiftLinearMapU_id]
  rfl

/--
Composition functoriality of the universe-`u` analytic pushforward. Universe-
polymorphic companion to `analyticPushforward_comp_apply`.
-/
theorem analyticPushforward_comp_applyU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobianU X) :
    analyticPushforwardU (g ∘ f) (hg.comp hf) P =
      analyticPushforwardU g hg (analyticPushforwardU f hf P) := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLatticeU X) P
  rw [analyticPushforward_mk_spec_rawU f hf v,
      analyticPushforward_mk_spec_rawU (g ∘ f) (hg.comp hf) v,
      analyticPushforward_mk_spec_rawU g hg (pushforwardTraceLiftCLMU f hf v)]
  congr 1
  exact pushforwardTraceLiftLinearMapU_comp f hf g hg v

end JacobianChallenge.TraceDegree
