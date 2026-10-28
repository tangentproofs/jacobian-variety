import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Cauchy–Pompeiu formula

For a compactly supported `C¹` function `φ : ℂ → ℂ`,

  `∫ ∂φ/∂z̄ (w + ζ) / ζ dA(ζ) = -π φ(w)`.

Proof: in polar coordinates `ζ = r e^{iθ}` the integrand times the Jacobian `r` is
`½ (∂_r g + (i/r) ∂_θ g)` with `g(r, θ) = φ(w + r e^{iθ})`; the radial term integrates to
`-g(0) = -φ(w)` and the angular term to `0` by periodicity.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Metric Filter Topology Complex Real
open scoped Convolution

/-- The Wirtinger derivative `∂/∂z̄ = ½(∂ₓ + i ∂_y)`. -/
noncomputable def dbar (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ φ z 1 + I * fderiv ℝ φ z I) / 2

/-- An `ℝ`-linear map on `ℂ` is determined by its values at `1` and `I`. -/
theorem clm_apply_eq_re_im (D : ℂ →L[ℝ] ℂ) (z : ℂ) : D z = z.re * D 1 + z.im * D I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add, show (z.re : ℂ) = z.re • (1 : ℂ) by simp,
    show (z.im : ℂ) * I = z.im • I by simp [Complex.real_smul], D.map_smul, D.map_smul]
  simp [Complex.real_smul]

theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- The polar-coordinate integrand of the Cauchy–Pompeiu formula. -/
theorem polar_dbar_div (D : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r • ((D 1 + I * D I) / 2 / circleMap 0 r θ) =
      D (exp (θ * I)) / 2 + I * D (I * exp (θ * I)) / 2 := by
  set e := exp (θ * I)
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hconj : e * (starRingEnd ℂ) e = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
  have hc : (starRingEnd ℂ) e = e⁻¹ := eq_inv_of_mul_eq_one_right hconj
  rw [clm_apply_eq_re_im D e, clm_apply_eq_re_im D (I * e), circleMap_zero]
  have hre : ((e.re : ℂ) - e.im * I) = e⁻¹ := by
    rw [← hc]; apply Complex.ext <;> simp
  have h1 : (I * e).re = -e.im := by simp
  have h2 : (I * e).im = e.re := by simp
  rw [h1, h2, Complex.real_smul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  calc (r : ℂ) * ((D 1 + I * D I) / 2 / (r * e))
      = e⁻¹ * (D 1 + I * D I) / 2 := by field_simp
    _ = ((e.re : ℂ) - e.im * I) * (D 1 + I * D I) / 2 := by rw [hre]
    _ = _ := by push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- A continuous function on `ℝ × ℝ` vanishing on `s` outside a compact set is integrable on `s`. -/
theorem integrableOn_of_continuous_of_eq_zero {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    {K s : Set (ℝ × ℝ)} (hK : IsCompact K) (hs : MeasurableSet s) (h0 : ∀ p ∈ s \ K, f p = 0) :
    IntegrableOn f s :=
  (hf.continuousOn.integrableOn_compact hK).of_forall_diff_eq_zero hs h0

theorem integrableOn_of_continuous_of_eq_zero' {f : ℝ → ℂ} (hf : Continuous f)
    {K s : Set ℝ} (hK : IsCompact K) (hs : MeasurableSet s) (h0 : ∀ p ∈ s \ K, f p = 0) :
    IntegrableOn f s :=
  (hf.continuousOn.integrableOn_compact hK).of_forall_diff_eq_zero hs h0

theorem circleMap_eq_add (w : ℂ) (r θ : ℝ) : circleMap w r θ = w + r * exp (θ * I) := rfl

theorem norm_circleMap_ge (w : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    r - ‖w‖ ≤ ‖circleMap w r θ‖ := by
  have h := norm_sub_le (circleMap w r θ) w
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr] at h
  linarith

/-- **Cauchy–Pompeiu formula** for compactly supported `C¹` functions. -/
theorem integral_dbar_div {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (w : ℂ) : ∫ ζ, dbar φ (w + ζ) / ζ = -(π * φ w) := by
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 ≤ R ∧ tsupport φ ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 0, le_max_right _ _, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  set D : ℂ → ℂ →L[ℝ] ℂ := fun z => fderiv ℝ φ z with hDdef
  have hDc : Continuous D := hφ.continuous_fderiv one_ne_zero
  have hdiff : ∀ z, HasFDerivAt φ (D z) z := fun z =>
    ((hφ.differentiable one_ne_zero) z).hasFDerivAt
  have hD0 : ∀ z, R < ‖z‖ → D z = 0 := by
    intro z hz
    have : z ∉ tsupport φ := fun h => by
      have := hR h; rw [mem_closedBall_zero_iff] at this; linarith
    exact Function.notMem_support.mp fun h' => this (support_fderiv_subset ℝ h')
  have hφ0 : ∀ z, R < ‖z‖ → φ z = 0 := by
    intro z hz
    exact image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h; rw [mem_closedBall_zero_iff] at this; linarith
  set M := ‖w‖ + R
  let A : ℝ × ℝ → ℂ := fun p => D (circleMap w p.1 p.2) (exp (p.2 * I)) / 2
  let B : ℝ × ℝ → ℂ := fun p => I * D (circleMap w p.1 p.2) (I * exp (p.2 * I)) / 2
  have hcm : Continuous fun p : ℝ × ℝ => circleMap w p.1 p.2 := by
    simp only [circleMap_eq_add]; fun_prop
  have hAc : Continuous A := by
    have : Continuous fun p : ℝ × ℝ => exp (p.2 * I) := by fun_prop
    exact ((hDc.comp hcm).clm_apply this).div_const 2
  have hBc : Continuous B := by
    have : Continuous fun p : ℝ × ℝ => I * exp (p.2 * I) := by fun_prop
    exact (continuous_const.mul ((hDc.comp hcm).clm_apply this)).div_const 2
  have hbig : ∀ p : ℝ × ℝ, M < p.1 → D (circleMap w p.1 p.2) = 0 := by
    intro p hp
    apply hD0
    have := norm_circleMap_ge w (r := p.1) (by
      have : 0 ≤ M := by positivity
      linarith) p.2
    linarith
  have htarget : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hAB : EqOn (fun p : ℝ × ℝ => p.1 • (dbar φ (w + Complex.polarCoord.symm p) /
      Complex.polarCoord.symm p)) (A + B) (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [Pi.add_apply, A, B, polarCoord_symm_eq_circleMap]
    rw [show w + circleMap 0 r θ = circleMap w r θ by simp [circleMap_eq_add]]
    exact polar_dbar_div (D (circleMap w r θ)) hr θ
  rw [← Complex.integral_comp_polarCoord_symm,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    setIntegral_congr_fun htarget hAB]
  -- integrability of the two pieces
  have hK : IsCompact (Icc (0 : ℝ) M ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hAi : IntegrableOn A (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine integrableOn_of_continuous_of_eq_zero hAc hK htarget ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    have : M < r := by
      by_contra h
      exact hn ⟨⟨le_of_lt hr, not_lt.mp h⟩, Ioo_subset_Icc_self hθ⟩
    simp [A, hbig (r, θ) this]
  have hBi : IntegrableOn B (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine integrableOn_of_continuous_of_eq_zero hBc hK htarget ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    have : M < r := by
      by_contra h
      exact hn ⟨⟨le_of_lt hr, not_lt.mp h⟩, Ioo_subset_Icc_self hθ⟩
    simp [B, hbig (r, θ) this]
  simp only [Pi.add_apply]
  rw [integral_add hAi hBi]
  -- the angular piece vanishes
  have hBzero : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, B p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hBi]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_).trans (integral_zero _ _)
    have hr : 0 < r := hr
    let h : ℝ → ℂ := fun θ => φ (circleMap w r θ)
    let h' : ℝ → ℂ := fun θ => D (circleMap w r θ) (circleMap 0 r θ * I)
    have hh : ∀ θ, HasDerivAt h (h' θ) θ := fun θ =>
      (hdiff _).comp_hasDerivAt θ (hasDerivAt_circleMap w r θ)
    have hB' : ∀ θ, B (r, θ) = I / (2 * r) * h' θ := by
      intro θ
      simp only [B, h', circleMap_zero]
      rw [show (r : ℂ) * exp (θ * I) * I = (r : ℝ) • (I * exp (θ * I)) by
        rw [Complex.real_smul]; ring, (D _).map_smul, Complex.real_smul]
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    simp_rw [hB']
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hh θ)]
    · have : h π = h (-π) := by
        have hp := periodic_circleMap w r (-π)
        rw [show -π + 2 * π = π by ring] at hp
        simp only [h]; rw [hp]
      rw [this, sub_self, mul_zero]
    · have hc : Continuous h' := by
        simp only [h', circleMap_zero]
        exact (hDc.comp (continuous_circleMap w r)).clm_apply (by fun_prop)
      exact hc.intervalIntegrable _ _
  -- the radial piece
  have hAval : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, A p = -(π * φ w) := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap]
    have hAi' : IntegrableOn (fun p : ℝ × ℝ => A p.swap) (Ioo (-π) π ×ˢ Ioi (0 : ℝ))
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      refine integrableOn_of_continuous_of_eq_zero (hAc.comp continuous_swap)
        (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-π) π ×ˢ Icc (0 : ℝ) M))
        (measurableSet_Ioo.prod measurableSet_Ioi) ?_
      rintro ⟨θ, r⟩ ⟨⟨hθ, hr⟩, hn⟩
      have : M < r := by
        by_contra h
        exact hn ⟨Ioo_subset_Icc_self hθ, ⟨le_of_lt hr, not_lt.mp h⟩⟩
      simp [A, hbig (r, θ) this]
    rw [setIntegral_prod _ hAi']
    have hinner : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), A (r, θ) = -(φ w) / 2 := by
      intro θ
      let g : ℝ → ℂ := fun r => φ (circleMap w r θ)
      let g' : ℝ → ℂ := fun r => D (circleMap w r θ) (exp (θ * I))
      have hg : ∀ r, HasDerivAt g (g' r) r := by
        intro r
        have h1 : HasDerivAt (fun r : ℝ => circleMap w r θ) (exp (θ * I)) r := by
          simp only [circleMap_eq_add]
          simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (exp (θ * I))).const_add w
        exact (hdiff _).comp_hasDerivAt r h1
      have hg'c : Continuous g' := by
        simp only [g']
        exact (hDc.comp (by simp only [circleMap_eq_add]; fun_prop)).clm_apply continuous_const
      have hfar : ∀ r, M < r → g' r = 0 := fun r hr => by
        simp [g', hbig (r, θ) hr]
      have hgfar : ∀ r, M < r → g r = 0 := fun r hr => by
        apply hφ0
        have := norm_circleMap_ge w (r := r) (by
          have : 0 ≤ M := by positivity
          linarith) θ
        linarith
      have hint : IntegrableOn g' (Ioi 0) := by
        refine integrableOn_of_continuous_of_eq_zero' hg'c (isCompact_Icc : IsCompact
          (Icc (0 : ℝ) M)) measurableSet_Ioi ?_
        rintro r ⟨hr, hn⟩
        exact hfar r (by
          by_contra h
          exact hn ⟨le_of_lt hr, not_lt.mp h⟩)
      have hlim : Tendsto g atTop (𝓝 0) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [eventually_gt_atTop M] with r hr using (hgfar r hr).symm)
      have := integral_Ioi_of_hasDerivAt_of_tendsto (hg 0).continuousAt.continuousWithinAt
        (fun r _ => hg r) hint hlim
      simp only [A]
      rw [integral_div, this]
      simp [g, circleMap_eq_add]
    simp only [Prod.swap_prod_mk]
    simp_rw [hinner]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [pi_pos])]
    simp only [real_smul]
    push_cast
    ring
  rw [hAval, hBzero, add_zero]

/-! ### The Cauchy transform -/

/-- The Cauchy kernel `t ↦ 1/t`. -/
noncomputable def cauchyKernel (t : ℂ) : ℂ := t⁻¹

theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (ae_of_all _ fun t => ?_) measurable_inv.aestronglyMeasurable
  simp [cauchyKernel, Real.rpow_neg_one]

/-- The Cauchy transform `T ψ (w) = (1/π) ∫ ψ(w - t)/t dA(t)`: a right inverse of `∂/∂z̄` on
compactly supported smooth functions (`dbar_cauchyTransform`). -/
noncomputable def cauchyTransform (ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * (cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ) w

theorem cauchyTransform_eq (ψ : ℂ → ℂ) (w : ℂ) :
    cauchyTransform ψ w = (π : ℂ)⁻¹ * ∫ t, t⁻¹ * ψ (w - t) := by
  simp only [cauchyTransform, convolution_def, cauchyKernel, ContinuousLinearMap.mul_apply']

theorem contDiff_cauchyTransform {ψ : ℂ → ℂ} {n : ℕ∞} (hψ : ContDiff ℝ n ψ)
    (hs : HasCompactSupport ψ) : ContDiff ℝ n (cauchyTransform ψ) :=
  contDiff_const.mul (hs.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hψ)

theorem fderiv_cauchyTransform_apply {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) (w v : ℂ) :
    fderiv ℝ (cauchyTransform ψ) w v = (π : ℂ)⁻¹ * ∫ t, t⁻¹ * fderiv ℝ ψ (w - t) v := by
  have h := (hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_cauchyKernel hψ w).const_mul ((π : ℂ)⁻¹)
  rw [show cauchyTransform ψ = fun w => (π : ℂ)⁻¹ *
    (cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ) w from rfl, h.fderiv]
  rw [ContinuousLinearMap.smul_apply, convolution_precompR_apply _ locallyIntegrable_cauchyKernel
    (hs.fderiv (𝕜 := ℝ)) (hψ.continuous_fderiv one_ne_zero)]
  simp [convolution_def, cauchyKernel, smul_eq_mul]

theorem dbar_cauchyTransform {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    (w : ℂ) : dbar (cauchyTransform ψ) w = ψ w := by
  have hint : ∀ v : ℂ, Integrable fun t => t⁻¹ * fderiv ℝ ψ (w - t) v := by
    intro v
    have := (hs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_cauchyKernel
      ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const) w
    simpa [ConvolutionExistsAt, cauchyKernel] using this
  unfold dbar
  rw [fderiv_cauchyTransform_apply hψ hs, fderiv_cauchyTransform_apply hψ hs]
  have key : ∫ t, (t⁻¹ * fderiv ℝ ψ (w - t) 1 + I * (t⁻¹ * fderiv ℝ ψ (w - t) I)) =
      2 * ∫ ζ, dbar ψ (w + ζ) / ζ * (-1) := by
    rw [← integral_const_mul, ← integral_neg_eq_self]
    congr 1; funext ζ
    unfold dbar
    rw [sub_neg_eq_add]
    by_cases hζ : ζ = 0
    · simp [hζ]
    · field_simp
      ring
  have hsum : (∫ t, t⁻¹ * fderiv ℝ ψ (w - t) 1) + I * ∫ t, t⁻¹ * fderiv ℝ ψ (w - t) I =
      2 * π * ψ w := by
    rw [← integral_const_mul, ← integral_add (hint 1) ((hint I).const_mul I), key,
      integral_mul_const, integral_dbar_div hψ hs]
    ring
  have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  calc _ = (π : ℂ)⁻¹ * ((∫ t, t⁻¹ * fderiv ℝ ψ (w - t) 1) +
        I * ∫ t, t⁻¹ * fderiv ℝ ψ (w - t) I) / 2 := by ring
    _ = ψ w := by rw [hsum]; field_simp

end JacobianChallenge.Analysis
