import Jacobian.AbelJacobi.PathIntegralFunctionalU
import Jacobian.Periods.PeriodFullComplexLatticeU
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.MkSmooth
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Universe-polymorphic analytic Abel-Jacobi map

The analytic Abel–Jacobi map of a compact Riemann surface `X : Type u` with base point
`P`,

  `analyticOfCurveU X P Q = [(∫_P^Q ω₁, …, ∫_P^Q ω_g)] ∈ ℂ^g / Λ`,

landing in `BasisAnalyticJacobianU X = quotient (Fin (analyticGenus ℂ X) → ℂ)
(periodFullComplexLatticeU X)` — which, under `ULift.{u}`, is the public `Jacobian X`
carrier of `Jacobian/Solution.lean`. The integral is the genuine path integral
`pathIntegralFunctionalU` (period vector of a chosen chart chain); its class does not
depend on the chain (`pathIntegralFunctionalU_sub_mem`).

* `analyticOfCurve_selfU` (`P ↦ 0`) is **proved**: the integral from `P` to `P` along
  the chosen path is a period.
* `analyticOfCurve_contMDiffU` (holomorphicity) is **proved**: near any `Q₀` the map is
  `Q ↦ [c + (F₁(Q), …, F_g(Q))]` with `Fᵢ` local holomorphic primitives of `ωᵢ` in a
  chart ball (`Periods.chartForm_hasFDerivAt_primitive`).
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods JacobianChallenge.ComplexTorus

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

/--
The universe-`u` basis-aligned analytic Jacobian carrier: the complex torus
`ℂ^g / Λ` for the genuine period lattice `Λ`. Under `ULift.{u}` this is the public
`Jacobian X` carrier.
-/
abbrev BasisAnalyticJacobianU : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)

/--
The analytic Abel–Jacobi map `Q ↦ [∫_P^Q ω]` on the basis-aligned carrier: the class
modulo periods of the genuine path integral from `P` to `Q`.
-/
noncomputable def analyticOfCurveU (P : X) : X → BasisAnalyticJacobianU X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLatticeU X) (pathIntegralFunctionalU X P Q)

/-- The Abel–Jacobi map sends the base point to zero (the self-integral is a period). -/
lemma analyticOfCurve_selfU (P : X) : analyticOfCurveU X P P = 0 :=
  (mk_eq_zero_iff (periodFullComplexLatticeU X)).mpr (pathIntegralFunctionalU_self_mem P)

/--
The value of the Abel–Jacobi map is the class of the period vector of **any** chart chain
from `P` to `Q`.
-/
lemma analyticOfCurveU_eq_mk_periodVector (P Q : X) {l : List (ChartSegment X)}
    (hl : IsChain l P Q) :
    analyticOfCurveU X P Q =
      mk (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X) (periodVector X l) := by
  unfold analyticOfCurveU
  exact QuotientAddGroup.eq.mpr (by
    have h := pathIntegralFunctionalU_sub_mem (X := X) hl
    rw [← neg_mem_iff, neg_sub, sub_eq_neg_add] at h
    exact h)

/--
**Holomorphicity of the Abel–Jacobi map.** Near any point `Q₀`, with `c` the chart at
`Q₀` and `B` a ball around `c Q₀` in its target, the map is
`Q ↦ [v₀ + G (c Q)]`, where `v₀` is the period vector of a chain from `P` to `Q₀` and
`G w = (∫_{[c Q₀, w]} ω₁, …, ∫_{[c Q₀, w]} ω_g)` (chart readings); `G` is a holomorphic
primitive on `B` (`chartForm_hasFDerivAt_primitive`), the chart is holomorphic and the
quotient map is holomorphic.
-/
theorem analyticOfCurve_contMDiffU (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurveU X P) := by
  intro Q₀
  set c := chartAt ℂ Q₀ with hc
  have hQ₀ : Q₀ ∈ c.source := mem_chart_source ℂ Q₀
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp c.open_target (c Q₀) (c.map_source hQ₀)
  have hcenter : c Q₀ ∈ Metric.ball (c Q₀) r := Metric.mem_ball_self hr
  set b := holomorphicOneFormFinBasis ℂ X
  set l₀ := chosenChain X P Q₀
  -- the vector of local primitives
  set G : ℂ → Fin (analyticGenus ℂ X) → ℂ :=
    fun w i => ∫ᶜ x in Path.segment (c Q₀) w, chartForm Q₀ (b i) x with hG
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (c Q₀) r) := by
    intro w hw
    refine (differentiableAt_pi.mpr fun i => ?_).differentiableWithinAt
    exact (chartForm_hasFDerivAt_primitive Q₀ (b i) hB hw).differentiableAt
  have hGsmooth : ContDiffAt ℂ (⊤ : WithTop ℕ∞) G (c Q₀) :=
    (hGdiff.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds hcenter)
  -- the local formula
  set h : X → BasisAnalyticJacobianU X := fun Q =>
    mk (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLatticeU X)
      (periodVector X l₀ + G (c Q))
  have hU : c.source ∩ c ⁻¹' Metric.ball (c Q₀) r ∈ nhds Q₀ :=
    Filter.inter_mem (c.open_source.mem_nhds hQ₀)
      ((c.continuousAt hQ₀).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hcenter))
  have heq : analyticOfCurveU X P =ᶠ[nhds Q₀] h := by
    filter_upwards [hU] with Q hQ
    let seg : ChartSegment X := ⟨Q₀, c Q₀, c Q, c Q₀, r, hB, hcenter, hQ.2⟩
    have hseg : IsChain [seg] Q₀ Q := by
      simp [seg, ChartSegment.start, ChartSegment.stop, c.left_inv hQ₀, c.left_inv hQ.1, c]
    rw [analyticOfCurveU_eq_mk_periodVector X P Q ((chosenChain_isChain X P Q₀).append hseg),
      periodVector_append]
    congr 2
    funext i
    simp [periodVector, chainIntegral_cons, ChartSegment.integral, seg, G, b]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hGc : ContMDiffAt 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (fun Q => periodVector X l₀ + G (c Q)) Q₀ := by
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) c Q₀ :=
      (contMDiffOn_chart (n := ⊤)).contMDiffAt (c.open_source.mem_nhds hQ₀)
    have h2 : ContMDiffAt 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞) (fun w => periodVector X l₀ + G w) (c Q₀) :=
      (contDiffAt_const.add hGsmooth).contMDiffAt
    exact h2.comp Q₀ h1
  exact (ComplexTorus.contMDiff_mk (periodFullComplexLatticeU X)).contMDiffAt.comp Q₀ hGc

end JacobianChallenge.AbelJacobi
