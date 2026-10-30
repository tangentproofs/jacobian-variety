import Jacobian.TraceDegree.AnalyticPullbackU

/-!
# Universe-polymorphic analytic-pullback smoothness

`PullbackBasis.lean` (retired; now `Attic/FalseGaps/PullbackBasis.lean`, not
built) proved the holomorphicity of the Type-0
analytic pullback (`analyticPullback_contMDiff_raw`, line 440) by a chart-based
`ContMDiffOn` argument: on each chart source, `analyticPullback` agrees with
`mk ∘ traceDualPullbackLiftCLM ∘ chart`, which is smooth as a composition of the
smooth chart map, the (continuous-linear, hence smooth) dual-pullback trace lift,
and the smooth quotient projection `mk`.

This file provides the universe-polymorphic companion `analyticPullback_contMDiffU`
(E2b of the TraceDegree "E-chain", pullback side), together with its
descent-compatibility prerequisite `analyticPullback_mk_spec_rawU`. It is the
holomorphicity half of `analyticPullbackU` (E2-core), needed by the public
`pullback_contMDiff` for `X : Type u` (Milestone C).

Both declarations are verbatim mirrors of their Type-0 originals (the same proof
as the pushforward side `analyticPushforward_contMDiff`, with the contravariant
`Y → X` direction and `traceDualPullbackLiftCLMU` in place of the pushforward
trace lift). The chart machinery is universe-polymorphic and the carriers
`Fin (analyticGenus ℂ X) → ℂ` are `Type 0`. Genuine — no sorry, and no `sorryAx`
dependence: the Periods-layer inputs reached through `periodFullComplexLatticeU`
are all proved.
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
Descent compatibility: the universe-`u` analytic pullback of a quotient
representative `mk v` is the quotient of the dual-pullback-trace-lifted vector.
Universe-polymorphic companion to the Type-0 descent identity used in
`analyticPullback_contMDiff_raw`; holds by `rfl`.
-/
theorem analyticPullback_mk_spec_rawU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullbackU f hf
      (ComplexTorus.mk _ (periodFullComplexLatticeU Y) v) =
      ComplexTorus.mk _ (periodFullComplexLatticeU X)
        (traceDualPullbackLiftCLMU f hf v) :=
  rfl

/--
Holomorphicity of the universe-`u` analytic pullback. Universe-polymorphic
companion to `analyticPullback_contMDiff`: a chart-based `ContMDiffOn` argument,
agreeing on each chart source with `mk ∘ traceDualPullbackLiftCLMU ∘ chart`
(contravariant `Y → X`).
-/
theorem analyticPullback_contMDiffU
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullbackU f hf) := by
  intro q
  set chartY := chartAt (Fin (analyticGenus ℂ Y) → ℂ) q with chartY_def
  have hsrc : q ∈ chartY.source := mem_chart_source _ q
  have hMem : chartY.source ∈ nhds q := chartY.open_source.mem_nhds hsrc
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞) chartY chartY.source :=
    contMDiffOn_chart
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞) (traceDualPullbackLiftCLMU f hf) :=
    (traceDualPullbackLiftCLMU f hf).contMDiff
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLatticeU X)
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLatticeU X)
          (traceDualPullbackLiftCLMU f hf (chartY q'))) chartY.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  have hEq : ∀ q' ∈ chartY.source,
      analyticPullbackU f hf q' =
        ComplexTorus.mk _ (periodFullComplexLatticeU X)
          (traceDualPullbackLiftCLMU f hf (chartY q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLatticeU Y) (chartY q') = q' :=
      chartY.left_inv' hq'
    conv_lhs => rw [← hLeft]
    exact analyticPullback_mk_spec_rawU f hf (chartY q')
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPullbackU f hf) chartY.source :=
    hComp.congr (fun q' hq' => hEq q' hq')
  exact hOn.contMDiffAt hMem

end JacobianChallenge.TraceDegree
