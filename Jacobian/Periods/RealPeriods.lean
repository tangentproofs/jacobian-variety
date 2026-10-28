import Jacobian.Periods.ChartChain
import Jacobian.HolomorphicForms.Finiteness
import Mathlib.Analysis.Complex.AbsMax

/-!
# A holomorphic 1-form with purely imaginary periods vanishes

On a compact connected Riemann surface, if the real part of `∫_l ω` depends only on the
endpoints of the chart chain `l`, then `ω = 0`.

Proof: `u(Q) = Re ∫_{P₀}^{Q} ω` is then a well-defined function; in the chart at any `Q₀` it
is `u(Q₀) + Re H` with `H` a local primitive, so `u` is continuous and attains its maximum.
At a maximum point `exp ∘ H` has maximal modulus at the centre of a ball, so it is constant
there (maximum modulus principle): `u` is constant near the point and `H' = 0` there. The
set of maximum points is therefore open and closed, hence everything, and the chart
coefficient of `ω` vanishes at every point.

This is the analytic half of "the periods span `ℂ^g` over `ℝ`"
(`Periods.periodLattice_span`).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set Metric Filter
open scoped Manifold Topology

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The one-segment chain from `Q₀` to `c⁻¹ z` in the chart at `Q₀`. -/
noncomputable def radialSegment (Q₀ : X) {ρ : ℝ}
    (hB : ball (chartAt ℂ Q₀ Q₀) ρ ⊆ (chartAt ℂ Q₀).target) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ Q₀ Q₀) ρ) : ChartSegment X :=
  ⟨Q₀, chartAt ℂ Q₀ Q₀, z, chartAt ℂ Q₀ Q₀, ρ, hB, mem_ball_self (pos_of_mem_ball hz), hz⟩

theorem isChain_radialSegment (Q₀ : X) {ρ : ℝ}
    (hB : ball (chartAt ℂ Q₀ Q₀) ρ ⊆ (chartAt ℂ Q₀).target) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ Q₀ Q₀) ρ) :
    IsChain [radialSegment Q₀ hB hz] Q₀ ((chartAt ℂ Q₀).symm z) :=
  ⟨(chartAt ℂ Q₀).left_inv (mem_chart_source ℂ Q₀), rfl⟩

theorem chainIntegral_radialSegment (ω : HolomorphicOneForm ℂ X) (Q₀ : X) {ρ : ℝ}
    (hB : ball (chartAt ℂ Q₀ Q₀) ρ ⊆ (chartAt ℂ Q₀).target) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ Q₀ Q₀) ρ) :
    chainIntegral ω [radialSegment Q₀ hB hz] =
      ∫ᶜ x in Path.segment (chartAt ℂ Q₀ Q₀) z, chartForm Q₀ ω x := by
  simp [chainIntegral, ChartSegment.integral, radialSegment]

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- **A holomorphic 1-form whose integrals have path-independent real part is zero.** -/
theorem eq_zero_of_re_chainIntegral_eq (ω : HolomorphicOneForm ℂ X)
    (h : ∀ (P Q : X) (l₁ l₂ : List (ChartSegment X)), IsChain l₁ P Q → IsChain l₂ P Q →
      (chainIntegral ω l₁).re = (chainIntegral ω l₂).re) :
    ω = 0 := by
  classical
  obtain ⟨P₀⟩ := (inferInstance : Nonempty X)
  let γ : X → List (ChartSegment X) := fun Q => (exists_chain P₀ Q).choose
  have hγ : ∀ Q, IsChain (γ Q) P₀ Q := fun Q => (exists_chain P₀ Q).choose_spec
  let u : X → ℝ := fun Q => (chainIntegral ω (γ Q)).re
  have hdiff : ∀ (Q Q' : X) (l : List (ChartSegment X)), IsChain l Q Q' →
      u Q' = u Q + (chainIntegral ω l).re := by
    intro Q Q' l hl
    have := h P₀ Q' _ _ (hγ Q') ((hγ Q).append hl)
    show (chainIntegral ω (γ Q')).re = (chainIntegral ω (γ Q)).re + _
    rw [this, chainIntegral_append, Complex.add_re]
  -- local data in the chart at each point
  have hloc : ∀ Q₀ : X, ∃ ρ > 0, ∃ hB : ball (chartAt ℂ Q₀ Q₀) ρ ⊆ (chartAt ℂ Q₀).target,
      ∀ z (hz : z ∈ ball (chartAt ℂ Q₀ Q₀) ρ),
        u ((chartAt ℂ Q₀).symm z) =
          u Q₀ + (∫ᶜ x in Path.segment (chartAt ℂ Q₀ Q₀) z, chartForm Q₀ ω x).re := by
    intro Q₀
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.mp (chartAt ℂ Q₀).open_target _
      ((chartAt ℂ Q₀).map_source (mem_chart_source ℂ Q₀))
    refine ⟨ρ, hρ, hB, fun z hz => ?_⟩
    rw [hdiff Q₀ _ _ (isChain_radialSegment Q₀ hB hz), chainIntegral_radialSegment]
  choose ρ hρ hB hu using hloc
  set H : X → ℂ → ℂ := fun Q₀ z => ∫ᶜ x in Path.segment (chartAt ℂ Q₀ Q₀) z, chartForm Q₀ ω x
  have hHd : ∀ Q₀ z, z ∈ ball (chartAt ℂ Q₀ Q₀) (ρ Q₀) →
      HasFDerivAt (H Q₀) (chartForm Q₀ ω z) z := fun Q₀ z hz =>
    chartForm_hasFDerivAt_primitive Q₀ ω (hB Q₀) hz
  -- `u` near `Q₀` is `u Q₀ + Re (H Q₀ ∘ c)`
  have hnear : ∀ Q₀ : X, ∀ᶠ Q in 𝓝 Q₀, Q ∈ (chartAt ℂ Q₀).source ∧
      chartAt ℂ Q₀ Q ∈ ball (chartAt ℂ Q₀ Q₀) (ρ Q₀) := fun Q₀ =>
    Filter.Eventually.and ((chartAt ℂ Q₀).open_source.mem_nhds (mem_chart_source ℂ Q₀))
      (((chartAt ℂ Q₀).continuousAt (mem_chart_source ℂ Q₀)).preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self (hρ Q₀))))
  have hueq : ∀ Q₀ : X, ∀ Q, Q ∈ (chartAt ℂ Q₀).source →
      chartAt ℂ Q₀ Q ∈ ball (chartAt ℂ Q₀ Q₀) (ρ Q₀) →
      u Q = u Q₀ + (H Q₀ (chartAt ℂ Q₀ Q)).re := by
    intro Q₀ Q hQ hQb
    have := hu Q₀ _ hQb
    rwa [(chartAt ℂ Q₀).left_inv hQ] at this
  have hucont : Continuous u := by
    refine continuous_iff_continuousAt.mpr fun Q₀ => ?_
    have hc : ContinuousAt (fun Q => u Q₀ + (H Q₀ (chartAt ℂ Q₀ Q)).re) Q₀ := by
      have hH : ContinuousAt (H Q₀) (chartAt ℂ Q₀ Q₀) :=
        (hHd Q₀ _ (mem_ball_self (hρ Q₀))).continuousAt
      exact continuousAt_const.add (Complex.continuous_re.continuousAt.comp
        (hH.comp ((chartAt ℂ Q₀).continuousAt (mem_chart_source ℂ Q₀))))
    refine hc.congr ?_
    filter_upwards [hnear Q₀] with Q hQ
    exact (hueq Q₀ Q hQ.1 hQ.2).symm
  -- maximum
  obtain ⟨Q₁, -, hQ₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hucont.continuousOn
  set M : Set X := {Q | u Q = u Q₁}
  -- at a maximum point: `exp ∘ H` is constant on the ball
  have hconst : ∀ Q₀ ∈ M, EqOn (fun z => Complex.exp (H Q₀ z))
      (Function.const ℂ (Complex.exp (H Q₀ (chartAt ℂ Q₀ Q₀)))) (ball (chartAt ℂ Q₀ Q₀) (ρ Q₀)) := by
    intro Q₀ hQ₀
    have hc0 : chartAt ℂ Q₀ Q₀ ∈ ball (chartAt ℂ Q₀ Q₀) (ρ Q₀) := mem_ball_self (hρ Q₀)
    have hdiffH : DifferentiableOn ℂ (fun z => Complex.exp (H Q₀ z))
        (ball (chartAt ℂ Q₀ Q₀) (ρ Q₀)) := fun z hz =>
      ((hHd Q₀ z hz).differentiableAt.cexp).differentiableWithinAt
    refine Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball _ _).isPreconnected
      isOpen_ball hdiffH hc0 fun z hz => ?_
    simp only [mem_setOf_eq, Function.comp_apply, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h1 := hu Q₀ z hz
    have h2 := hu Q₀ _ hc0
    rw [(chartAt ℂ Q₀).left_inv (mem_chart_source ℂ Q₀)] at h2
    have hle : u ((chartAt ℂ Q₀).symm z) ≤ u Q₀ := by
      rw [show u Q₀ = u Q₁ from hQ₀]; exact hQ₁ (mem_univ _)
    show (H Q₀ z).re ≤ (H Q₀ (chartAt ℂ Q₀ Q₀)).re
    linarith
  have hMopen : IsOpen M := by
    refine isOpen_iff_mem_nhds.mpr fun Q₀ hQ₀ => ?_
    filter_upwards [hnear Q₀] with Q hQ
    have hc := hconst Q₀ hQ₀ hQ.2
    simp only [Function.const_apply] at hc
    have hre := congrArg Complex.re (congrArg Complex.log hc)
    have hn := congrArg (fun w => ‖w‖) hc
    simp only [Complex.norm_exp] at hn
    have hre' : (H Q₀ (chartAt ℂ Q₀ Q)).re = (H Q₀ (chartAt ℂ Q₀ Q₀)).re :=
      Real.exp_injective hn
    have h0 := hueq Q₀ Q₀ (mem_chart_source ℂ Q₀) (mem_ball_self (hρ Q₀))
    show u Q = u Q₁
    rw [hueq Q₀ Q hQ.1 hQ.2, hre', ← h0]
    exact hQ₀
  have hMclosed : IsClosed M := isClosed_eq hucont continuous_const
  have hMuniv : M = univ :=
    (IsClopen.eq_univ ⟨hMclosed, hMopen⟩ ⟨Q₁, rfl⟩)
  -- the chart coefficient vanishes everywhere
  refine holomorphicOneForm_eq_zero_of_chartCoeff ω fun Q₀ => ⟨Q₀, mem_chart_source ℂ Q₀, ?_⟩
  have hQ₀ : Q₀ ∈ M := hMuniv ▸ mem_univ Q₀
  have hc0 : chartAt ℂ Q₀ Q₀ ∈ ball (chartAt ℂ Q₀ Q₀) (ρ Q₀) := mem_ball_self (hρ Q₀)
  set c0 := chartAt ℂ Q₀ Q₀
  -- `exp ∘ H` is locally constant, so its derivative vanishes
  have hev : (fun z => Complex.exp (H Q₀ z)) =ᶠ[𝓝 c0] fun _ => Complex.exp (H Q₀ c0) := by
    filter_upwards [isOpen_ball.mem_nhds hc0] with z hz
    exact hconst Q₀ hQ₀ hz
  have hd0 : deriv (fun z => Complex.exp (H Q₀ z)) c0 = 0 := by
    rw [hev.deriv_eq]; simp
  have hHd' := (hHd Q₀ c0 hc0).hasDerivAt
  have hcomp := hHd'.cexp
  rw [hcomp.deriv] at hd0
  have hne : Complex.exp (H Q₀ c0) ≠ 0 := Complex.exp_ne_zero _
  have hval : chartForm Q₀ ω c0 1 = 0 := by
    rcases mul_eq_zero.mp hd0 with h | h
    · exact absurd h hne
    · exact h
  exact hval

end JacobianChallenge.Periods
