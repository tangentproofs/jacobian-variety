import Jacobian.Surface.Hodge8

/-!
# Transplanting a `(0,1)`-form from one chart; `∂̄` in genus zero

* `ext01 p ψ`: the `(0,1)`-form whose reading in the chart at `p` is `ψ` (a smooth function
  compactly supported in the chart target), read in every other chart by the transformation law.
* `dbar_solvable_of_forall_eq_zero`: if every holomorphic 1-form vanishes (genus zero), every
  smooth `(0,1)`-form is `∂̄u`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

open Classical in
/-- The `(0,1)`-form with reading `ψ` in the chart at `p`. -/
noncomputable def ext01 (p : X) (ψ : ℂ → ℂ) : X → ℂ → ℂ := fun q w =>
  if (chartAt ℂ q).symm w ∈ (chartAt ℂ p).source then
    (starRingEnd ℂ) (deriv (trans q p) w) * ψ (trans q p w)
  else 0

theorem ext01_is01 (p : X) (ψ : ℂ → ℂ) : Is01 (ext01 p ψ) := by
  intro q₁ q₂ w hw
  have hs : (chartAt ℂ q₂).symm (trans q₁ q₂ w) = (chartAt ℂ q₁).symm w := trans_symm_eq hw
  by_cases hp : (chartAt ℂ q₁).symm w ∈ (chartAt ℂ p).source
  · have hwp : w ∈ overlap q₁ p := ⟨hw.1, hp⟩
    have htt : trans q₂ p (trans q₁ q₂ w) = trans q₁ p w := by
      show chartAt ℂ p ((chartAt ℂ q₂).symm (trans q₁ q₂ w)) = chartAt ℂ p ((chartAt ℂ q₁).symm w)
      rw [hs]
    simp only [ext01]
    rw [if_pos hp, hs, if_pos hp, htt, deriv_trans_comp hw hwp, map_mul]
    ring
  · simp only [ext01]
    rw [if_neg hp, hs, if_neg hp, mul_zero]

/-- Smoothness of `ext01`, for `ψ` smooth and compactly supported in the chart target. -/
theorem smoothFam_ext01 {p : X} {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) {K : Set ℂ}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt ℂ p).target) (hψK : tsupport ψ ⊆ K) :
    SmoothFam (ext01 p ψ) := by
  intro q w hw
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hp : (chartAt ℂ q).symm w ∈ (chartAt ℂ p).source
  · have hwp : w ∈ overlap q p := ⟨hw, hp⟩
    have hev : ext01 p ψ q =ᶠ[𝓝 w] fun v =>
        (starRingEnd ℂ) (deriv (trans q p) v) * ψ (trans q p v) := by
      filter_upwards [(isOpen_overlap q p).mem_nhds hwp] with v hv
      simp only [ext01]
      rw [if_pos (show (chartAt ℂ q).symm v ∈ (chartAt ℂ p).source from hv.2)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h1 : ContDiffAt ℝ ∞ (deriv (trans q p)) w :=
      ((chartMap_analyticAt contMDiff_id hwp.1 hwp.2).deriv.contDiffAt).restrict_scalars ℝ
    exact (Complex.conjCLE.contDiff.contDiffAt.comp w h1).mul
      (hψ.contDiffAt.comp w (trans_contDiffAt hwp))
  · have hx : (chartAt ℂ q).symm w ∉ (chartAt ℂ p).symm '' K := fun h =>
      hp (symm_image_subset_source hKt h)
    have hclosed := (isCompact_symm_image hK hKt).isClosed
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [((chartAt ℂ q).continuousAt_symm hw).preimage_mem_nhds
      (hclosed.isOpen_compl.mem_nhds hx)] with v hv
    simp only [ext01]
    split_ifs with hvp
    · have : trans q p v ∉ K := fun hK' => hv ⟨_, hK', by
        show (chartAt ℂ p).symm (chartAt ℂ p ((chartAt ℂ q).symm v)) = _
        rw [(chartAt ℂ p).left_inv hvp]⟩
      rw [image_eq_zero_of_notMem_tsupport fun h => this (hψK h), mul_zero]
    · rfl

theorem ext01_self {p : X} {ψ : ℂ → ℂ} {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    ext01 p ψ p w = ψ w := by
  have hp : (chartAt ℂ p).symm w ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hw
  simp only [ext01, if_pos hp]
  rw [deriv_trans_self hw, map_one, one_mul,
    show trans p p w = w from (chartAt ℂ p).right_inv hw]

theorem chartCoeff_zero (q : X) (w : ℂ) : chartCoeff q (0 : HolomorphicOneForm ℂ X) w = 0 := by
  have := chartCoeff_add q (0 : HolomorphicOneForm ℂ X) 0 w
  rw [add_zero] at this
  linear_combination -this

/-- **`∂̄` in genus zero.** If every holomorphic 1-form vanishes, every smooth `(0,1)`-form is
`∂̄u` for a smooth `u`. -/
theorem dbar_solvable_of_forall_eq_zero [CompactSpace X] [ConnectedSpace X]
    (h0 : ∀ η : HolomorphicOneForm ℂ X, η = 0) {θ : X → ℂ → ℂ} (hθ : Is01 θ)
    (hθs : SmoothFam θ) :
    ∃ u : X → ℂ, IsSmooth u ∧ ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, θ q w = dbar (rd u q) w := by
  obtain ⟨u, hu, ν, hν⟩ := hodge_decomp hθ hθs
  refine ⟨u, hu, fun q w hw => ?_⟩
  rw [hν q w hw, h0 ν, chartCoeff_zero, map_zero, add_zero]

end JacobianChallenge.Surface
