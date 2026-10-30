import Jacobian.TraceDegree.AnalyticPushforwardU

/-!
# Universe-polymorphic analytic-pushforward smoothness

`PushforwardBasis.lean` (retired; now `Attic/FalseGaps/PushforwardBasis.lean`,
not built) proved the holomorphicity of the
Type-0 analytic pushforward (`analyticPushforward_contMDiff_raw`, line 417) by a
chart-based `ContMDiffOn` argument: on each chart source, `analyticPushforward`
agrees with `mk ∘ pushforwardTraceLiftCLM ∘ chart`, which is smooth as a
composition of the smooth chart map, the (continuous-linear, hence smooth)
trace-lift map, and the smooth quotient projection `mk`.

This file provides the universe-polymorphic companion `analyticPushforward_contMDiffU`
(E1b of the TraceDegree "E-chain"), together with its descent-compatibility
prerequisite `analyticPushforward_mk_spec_rawU`. It is the holomorphicity half of
`analyticPushforwardU` (E1-core), needed by the public `pushforward_contMDiff` for
`X : Type u` (Milestone C).

Both declarations are verbatim mirrors of their Type-0 originals
(`analyticPushforward_mk_spec_raw` / `analyticPushforward_contMDiff_raw`): the
chart machinery (`contMDiffOn_chart`, `ContinuousLinearMap.contMDiff`,
`ComplexTorus.contMDiff_mk`, `OpenPartialHomeomorph.left_inv'`,
`ContMDiff.comp_contMDiffOn`, `ContMDiffOn.congr`, `ContMDiffOn.contMDiffAt`) is
all universe-polymorphic, and the carriers `Fin (analyticGenus ℂ X) → ℂ` are
`Type 0`. Genuine — no sorry, and no `sorryAx` dependence: the Periods-layer
inputs reached through `periodFullComplexLatticeU` are all proved.
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
Descent compatibility: the universe-`u` analytic pushforward of a quotient
representative `mk v` is the quotient of the trace-lifted vector. Universe-
polymorphic companion to `analyticPushforward_mk_spec_raw`; holds by `rfl`.
-/
theorem analyticPushforward_mk_spec_rawU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforwardU f hf
      (ComplexTorus.mk _ (periodFullComplexLatticeU X) v) =
      ComplexTorus.mk _ (periodFullComplexLatticeU Y)
        (pushforwardTraceLiftCLMU f hf v) :=
  rfl

/--
Holomorphicity of the universe-`u` analytic pushforward. Universe-polymorphic
companion to `analyticPushforward_contMDiff`: a chart-based `ContMDiffOn`
argument, agreeing on each chart source with `mk ∘ pushforwardTraceLiftCLMU ∘ chart`.
-/
theorem analyticPushforward_contMDiffU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforwardU f hf) := by
  intro q
  set chartX := chartAt (Fin (analyticGenus ℂ X) → ℂ) q with chartX_def
  have hsrc : q ∈ chartX.source := mem_chart_source _ q
  have hMem : chartX.source ∈ nhds q := chartX.open_source.mem_nhds hsrc
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞) chartX chartX.source :=
    contMDiffOn_chart
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞) (pushforwardTraceLiftCLMU f hf) :=
    (pushforwardTraceLiftCLMU f hf).contMDiff
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ Y) → ℂ) (periodFullComplexLatticeU Y)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLatticeU Y)
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLatticeU Y)
          (pushforwardTraceLiftCLMU f hf (chartX q'))) chartX.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  have hEq : ∀ q' ∈ chartX.source,
      analyticPushforwardU f hf q' =
        ComplexTorus.mk _ (periodFullComplexLatticeU Y)
          (pushforwardTraceLiftCLMU f hf (chartX q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLatticeU X) (chartX q') = q' :=
      chartX.left_inv' hq'
    conv_lhs => rw [← hLeft]
    exact analyticPushforward_mk_spec_rawU f hf (chartX q')
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPushforwardU f hf) chartX.source :=
    hComp.congr (fun q' hq' => hEq q' hq')
  exact hOn.contMDiffAt hMem

end JacobianChallenge.TraceDegree
