import Jacobian.Analysis.WeylDbar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Cauchy–Pompeiu along a segment

For a compactly supported `C¹` function `φ : ℂ → ℂ` and a segment `[a, b]`,

  `∫ ∂φ/∂z̄ (z) · Log((z - b)/(z - a)) dA(z) = π (b - a) ∫₀¹ φ(a + t (b - a)) dt`,

i.e. `π ∫_{[a,b]} φ dz`. Off the segment, `Log((z - b)/(z - a)) = -(b - a) ∫₀¹ dt/(z - b_t)`
(`b_t = a + t (b - a)`); exchange the integrals and apply the Cauchy–Pompeiu formula
`integral_dbar_div` at each `b_t`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Metric Filter Topology Complex Real
open scoped Convolution

/-- The point `a + t (b - a)` of the segment `[a, b]`. -/
noncomputable abbrev segPt (a b : ℂ) (t : ℝ) : ℂ := a + t * (b - a)

theorem continuous_segPt (a b : ℂ) : Continuous (segPt a b) := by
  unfold segPt; fun_prop

theorem segPt_mem_segment (a b : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segPt a b t ∈ segment ℝ a b := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [segPt, Complex.real_smul]⟩

theorem sub_segPt_ne_zero {a b z : ℂ} (hz : z ∉ segment ℝ a b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : z - segPt a b t ≠ 0 := fun h =>
  hz (sub_eq_zero.mp h ▸ segPt_mem_segment a b ht)

/-- Off the segment, the ratio `(z - b_t)/(z - a)` stays in the slit plane. -/
theorem div_mem_slitPlane {a b z : ℂ} (hz : z ∉ segment ℝ a b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (z - segPt a b t) / (z - a) ∈ slitPlane := by
  have hza : z - a ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ left_mem_segment ℝ a b)
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  rw [Complex.le_def] at hle
  set y := (z - segPt a b t) / (z - a)
  have hy : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hle.2])
  set s : ℝ := -y.re
  have hle1 : y.re ≤ 0 := by simpa using hle.1
  have hs : 0 ≤ s := by simp only [s]; linarith
  have heq : z - segPt a b t = -(s : ℂ) * (z - a) := by
    have : z - segPt a b t = y * (z - a) := by simp only [y]; field_simp
    rw [this, hy]; simp [s]
  apply hz
  rw [segment_eq_image']
  have h1s : (0 : ℝ) < 1 + s := by linarith
  refine ⟨t / (1 + s), ⟨by have := ht.1; positivity, ?_⟩, ?_⟩
  · rw [div_le_one h1s]; linarith [ht.2]
  · simp only [segPt] at heq
    have h1s' : (1 + (s : ℂ)) ≠ 0 := by exact_mod_cast h1s.ne'
    show a + ((t / (1 + s) : ℝ) : ℂ) * (b - a) = z
    push_cast
    field_simp
    linear_combination -heq

/-- **The logarithm as an integral along the segment.** -/
theorem log_div_eq_integral {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    Complex.log ((z - b) / (z - a)) = -(b - a) * ∫ t in (0 : ℝ)..1, (z - segPt a b t)⁻¹ := by
  have hza : z - a ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ left_mem_segment ℝ a b)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => Complex.log ((z - segPt a b t) / (z - a)))
      (-(b - a) * (z - segPt a b t)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => (z - segPt a b t) / (z - a)) (-(b - a) / (z - a)) t := by
      have := ((((hasDerivAt_id t).ofReal_comp).mul_const (b - a)).const_add a).const_sub z
      simpa [segPt, neg_div] using this.div_const (z - a)
    convert h1.clog_real (div_mem_slitPlane hz ht) using 1
    have hne := sub_segPt_ne_zero hz ht
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => -(b - a) * (z - segPt a b t)⁻¹) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact (continuousAt_const.mul (((continuous_const.sub (continuous_segPt a b)).continuousAt).inv₀
      (sub_segPt_ne_zero hz ht))).continuousWithinAt
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint]
  simp [segPt]

/-- A segment in `ℂ` is Lebesgue-null. -/
theorem volume_segment (a b : ℂ) : volume (segment ℝ a b) = 0 := by
  refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume (affineSpan ℝ {a, b}) ?_)
  · rw [segment_eq_image_lineMap]
    rintro _ ⟨t, -, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t a b
  · intro htop
    have hdir := congrArg AffineSubspace.direction htop
    rw [direction_affineSpan, AffineSubspace.direction_top, vectorSpan_pair] at hdir
    have h1 := finrank_span_le_card (R := ℝ) ({a -ᵥ b} : Set ℂ)
    rw [hdir, finrank_top, Complex.finrank_real_complex] at h1
    simp at h1

theorem hasCompactSupport_dbar' {φ : ℂ → ℂ} (hs : HasCompactSupport φ) :
    HasCompactSupport (dbar φ) :=
  HasCompactSupport.intro hs.isCompact fun _ hz =>
    dbar_eq_zero_of_eventuallyEq (c := 0) (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem locallyIntegrable_inv_norm : LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (ae_of_all _ fun t => ?_) (measurable_norm.inv).aestronglyMeasurable
  simp [Real.rpow_neg_one]

/-- Integrability of `ψ(z)/(z - c)` for `ψ` continuous with compact support. -/
theorem integrable_mul_inv_sub {ψ : ℂ → ℂ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ)
    (c : ℂ) : Integrable (fun z => ψ z * (z - c)⁻¹) := by
  have hψ' : Continuous fun ζ => ψ (ζ + c) := hψ.comp (continuous_id.add continuous_const)
  have hs' : HasCompactSupport fun ζ => ψ (ζ + c) := hs.comp_homeomorph (Homeomorph.addRight c)
  have h0 : Integrable (fun ζ => ψ (ζ + c) * ζ⁻¹) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport fun ζ => ψ (ζ + c))
      ?_ fun z hz => ?_
    · have := (locallyIntegrable_cauchyKernel.integrableOn_isCompact hs'.isCompact).mul_continuousOn
        hψ'.continuousOn hs'.isCompact
      simpa [cauchyKernel, mul_comm] using this
    · simp [image_eq_zero_of_notMem_tsupport hz]
  simpa using h0.comp_sub_right c

/-- **Cauchy–Pompeiu along a segment.** -/
theorem integral_dbar_mul_log {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (a b : ℂ) :
    ∫ z, dbar φ z * Complex.log ((z - b) / (z - a)) =
      π * (b - a) * ∫ t in (0 : ℝ)..1, φ (segPt a b t) := by
  have hDc : Continuous (dbar φ) := continuous_dbar hφ
  have hDs : HasCompactSupport (dbar φ) := hasCompactSupport_dbar' hs
  -- off the (null) segment, replace the logarithm by its integral formula
  have hae : (fun z => dbar φ z * Complex.log ((z - b) / (z - a))) =ᵐ[volume]
      fun z => -(b - a) * ∫ t in (0 : ℝ)..1, dbar φ z * (z - segPt a b t)⁻¹ := by
    have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ segment ℝ a b :=
      measure_eq_zero_iff_ae_notMem.mp (volume_segment a b)
    filter_upwards [hnull] with z hz
    rw [log_div_eq_integral hz, intervalIntegral.integral_const_mul]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  -- exchange the integrals
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (t : ℝ) (z : ℂ) => dbar φ z * (z - segPt a b t)⁻¹)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hDc.measurable.comp measurable_snd).mul
      ((continuous_snd.sub ((continuous_segPt a b).comp continuous_fst)).measurable.inv)
  have hconv : Continuous fun c : ℂ => ∫ z, ‖dbar φ z‖ * ‖z - c‖⁻¹ := by
    have hc := (hDs.norm).continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      locallyIntegrable_inv_norm hDc.norm
    refine hc.congr fun c => ?_
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    rw [← integral_sub_left_eq_self _ (μ := volume) c]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [sub_sub_cancel, norm_sub_rev c z, mul_comm]
  have hint : Integrable (Function.uncurry fun (t : ℝ) (z : ℂ) => dbar φ z * (z - segPt a b t)⁻¹)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨ae_of_all _ fun t => ?_, ?_⟩
    · exact integrable_mul_inv_sub hDc hDs (segPt a b t)
    · have : Continuous fun t : ℝ => ∫ z, ‖dbar φ z * (z - segPt a b t)⁻¹‖ := by
        refine (hconv.comp (continuous_segPt a b)).congr fun t => ?_
        simp [norm_inv]
      exact (this.integrableOn_Icc (a := 0) (b := 1)).mono_set
        (by rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hint]
  have hinner : ∀ t : ℝ, ∫ z, dbar φ z * (z - segPt a b t)⁻¹ = -(π * φ (segPt a b t)) := by
    intro t
    rw [← integral_dbar_div hφ hs (segPt a b t), ← integral_add_left_eq_self (μ := volume)
      (fun z => dbar φ z * (z - segPt a b t)⁻¹) (segPt a b t)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp [div_eq_mul_inv]
  simp_rw [hinner]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring

end JacobianChallenge.Analysis
