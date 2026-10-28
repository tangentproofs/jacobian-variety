import Jacobian.Analysis.CauchyPompeiu
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Weyl's lemma for `∂/∂z̄`

An integrable function `U` on a disc with `∫ U ∂φ/∂z̄ = 0` for all test functions `φ` agrees
almost everywhere, on a smaller disc, with a holomorphic function (`weyl_dbar_ball`). The
inhomogeneous version (`weyl_dbar_inhom`): if `∫ U ∂φ/∂z̄ = -∫ f φ` with `f` smooth, then `U`
agrees a.e. near each point with a smooth `u` with `∂u/∂z̄ = f`.

Proof (homogeneous case): cut off, `V = χ U`; then `∂V/∂z̄ = F := U ∂χ/∂z̄` weakly, and `F`
vanishes near the centre. Testing against Cauchy transforms (`dbar_cauchyTransform`) and
Fubini give `V = (1/π) ∫ F(ζ)/(w - ζ) dA(ζ)` a.e. near the centre, and the right side is
holomorphic there (differentiation under the integral sign; the kernel is not singular on
the support of `F`).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Metric Filter Topology Complex Real
open scoped ContDiff

/-! ### Calculus of `dbar` -/

theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := by
  unfold dbar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ f z) :
    dbar f z = 0 := by
  unfold dbar
  rw [h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have : fderiv ℂ f z I = I * fderiv ℂ f z 1 := by
    rw [← smul_eq_mul, ← (fderiv ℂ f z).map_smul, smul_eq_mul, mul_one]
  rw [this, ← mul_assoc, I_mul_I]
  ring

theorem dbar_eq_zero_of_eventuallyEq {f : ℂ → ℂ} {z : ℂ} {c : ℂ} (h : f =ᶠ[𝓝 z] fun _ => c) :
    dbar f z = 0 := by
  unfold dbar
  rw [h.fderiv_eq]
  simp

/-- Cauchy–Riemann: a real-differentiable function with `∂f/∂z̄ = 0` is complex
differentiable. -/
theorem differentiableAt_of_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (h : dbar f z = 0) : DifferentiableAt ℂ f z := by
  set D := fderiv ℝ f z
  have hI : D I = I * D 1 := by
    have h2 : D 1 + I * D I = 0 := by
      have := h; unfold dbar at this
      have h4 : (2 : ℂ) ≠ 0 := two_ne_zero
      simpa [D] using (div_eq_zero_iff.mp this).resolve_right h4
    linear_combination (-I) * h2 + (D I) * Complex.I_sq
  let L : ℂ →L[ℂ] ℂ := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (D 1)
  refine ⟨L, hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt ?_⟩
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.coe_restrictScalars', clm_apply_eq_re_im D v, hI]
  simp only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  have hv : (v.re : ℂ) + v.im * I = v := Complex.re_add_im v
  nth_rewrite 1 [← hv]
  ring

/-- Integration by parts for `∂/∂z̄`. -/
theorem integral_mul_dbar {g φ : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) :
    ∫ z, g z * dbar φ z = -∫ z, dbar g z * φ z := by
  have hgc := hg.continuous
  have hφc := hφ.continuous
  have hg' := hg.continuous_fderiv one_ne_zero
  have hφ' := hφ.continuous_fderiv one_ne_zero
  have ibp : ∀ v : ℂ, ∫ z, g z * fderiv ℝ φ z v = -∫ z, fderiv ℝ g z v * φ z := by
    intro v
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
    · exact (hg'.clm_apply continuous_const).mul hφc |>.integrable_of_hasCompactSupport
        hs.mul_left
    · exact hgc.mul (hφ'.clm_apply continuous_const) |>.integrable_of_hasCompactSupport
        (hs.fderiv_apply (𝕜 := ℝ) v).mul_left
    · exact (hgc.mul hφc).integrable_of_hasCompactSupport hs.mul_left
    · exact fun z _ => (hg.differentiable one_ne_zero) z
    · exact fun z _ => (hφ.differentiable one_ne_zero) z
  have i1 : ∀ v : ℂ, Integrable fun z => g z * fderiv ℝ φ z v := fun v =>
    hgc.mul (hφ'.clm_apply continuous_const) |>.integrable_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) v).mul_left
  have i2 : ∀ v : ℂ, Integrable fun z => fderiv ℝ g z v * φ z := fun v =>
    (hg'.clm_apply continuous_const).mul hφc |>.integrable_of_hasCompactSupport hs.mul_left
  unfold dbar
  have e1 : ∫ z, g z * ((fderiv ℝ φ z 1 + I * fderiv ℝ φ z I) / 2) =
      (1 / 2 : ℂ) * (∫ z, g z * fderiv ℝ φ z 1) + (I / 2) * ∫ z, g z * fderiv ℝ φ z I := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i1 1).const_mul _)
      ((i1 I).const_mul _)]
    congr 1; funext z; ring
  have e2 : ∫ z, (fderiv ℝ g z 1 + I * fderiv ℝ g z I) / 2 * φ z =
      (1 / 2 : ℂ) * (∫ z, fderiv ℝ g z 1 * φ z) + (I / 2) * ∫ z, fderiv ℝ g z I * φ z := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i2 1).const_mul _)
      ((i2 I).const_mul _)]
    congr 1; funext z; ring
  rw [e1, e2, ibp 1, ibp I]
  ring

/-- A holomorphic function on an open set is smooth there. -/
theorem DifferentiableOn.contDiffOn_real {f : ℂ → ℂ} {s : Set ℂ} (hf : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : ContDiffOn ℝ ∞ f s :=
  (hf.contDiffOn hs (n := ∞)).restrict_scalars ℝ

/-! ### Integrability helpers -/

theorem integrable_mul_of_integrableOn {U g : ℂ → ℂ} {K : Set ℂ} (hU : IntegrableOn U K)
    (hK : MeasurableSet K) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgK : ∀ z ∉ K, g z = 0) : Integrable fun z => U z * g z := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
  have : (fun z => U z * g z) = fun z => K.indicator U z * g z := by
    funext z
    by_cases hz : z ∈ K
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz, hgK z hz]
  rw [this]
  exact ((integrable_indicator_iff hK).mpr hU).mul_bdd hg.aestronglyMeasurable (ae_of_all _ hC)

/-- A function continuous on an open set times a continuous function compactly supported in
it is continuous. -/
theorem continuous_mul_of_tsupport_subset' {a b : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (ha : ContinuousOn a W) (hb : Continuous b) (hbW : tsupport b ⊆ W) :
    Continuous fun x => a x * b x := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ W
  · exact (ha.continuousAt (hW.mem_nhds hx)).mul hb.continuousAt
  · have hx' : x ∉ tsupport b := fun h => hx (hbW h)
    have hev : (fun x => a x * b x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact continuousAt_const.congr hev.symm

theorem integrable_mul_of_continuousOn {a b : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (ha : ContinuousOn a W) (hb : Continuous b) (hbs : HasCompactSupport b)
    (hbW : tsupport b ⊆ W) : Integrable fun z => a z * b z :=
  (continuous_mul_of_tsupport_subset' hW ha hb hbW).integrable_of_hasCompactSupport hbs.mul_left

/-! ### Weyl's lemma -/

/-- **Weyl's lemma for `∂/∂z̄`.** An integrable function on a disc which is weakly holomorphic
agrees a.e. on the disc of a quarter of the radius with a holomorphic function. -/
theorem weyl_dbar_ball {U : ℂ → ℂ} {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hU : IntegrableOn U (ball x R))
    (hw : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x R →
      ∫ z, U z * dbar φ z = 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball x (R / 4)) ∧
      ∀ᵐ z, z ∈ ball x (R / 4) → U z = h z := by
  -- the cutoff
  let b : ContDiffBump x := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let χ : ℂ → ℂ := fun z => (b z : ℂ)
  have hχ : ContDiff ℝ ∞ χ := ofRealCLM.contDiff.comp b.contDiff
  have hχs : HasCompactSupport χ := b.hasCompactSupport.comp_left ofReal_zero
  have hχt : tsupport χ ⊆ ball x R := by
    refine (tsupport_comp_subset ofReal_zero _).trans ?_
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by show 3 * R / 4 < R; linarith)
  have hχ1 : ∀ z ∈ closedBall x (R / 2), χ z = 1 := fun z hz => by
    simp [χ, b.one_of_mem_closedBall hz]
  have hdχ : ∀ z ∈ ball x (R / 2), dbar χ z = 0 := fun z hz =>
    dbar_eq_zero_of_eventuallyEq (c := 1) (by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact hχ1 y (ball_subset_closedBall hy))
  have hdχ0 : ∀ z ∉ ball x R, dbar χ z = 0 := fun z hz =>
    dbar_eq_zero_of_eventuallyEq (c := 0) (notMem_tsupport_iff_eventuallyEq.mp
      fun h => hz (hχt h))
  have hχ0 : ∀ z ∉ ball x R, χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hχt h)
  have hχd : ∀ z, DifferentiableAt ℝ χ z := fun z => (hχ.differentiable (by simp)) z
  have hdχc : Continuous (dbar χ) := by
    have := hχ.continuous_fderiv (n := ∞) (by simp)
    unfold dbar
    exact ((this.clm_apply continuous_const).add
      (continuous_const.mul (this.clm_apply continuous_const))).div_const 2
  have hdχs : HasCompactSupport (dbar χ) :=
    HasCompactSupport.intro (isCompact_closedBall x R) fun z hz =>
      hdχ0 z fun h => hz (ball_subset_closedBall h)
  set V : ℂ → ℂ := fun z => χ z * U z with hV
  set F : ℂ → ℂ := fun z => U z * dbar χ z with hF
  have hVi : Integrable V := by
    have := integrable_mul_of_integrableOn hU measurableSet_ball hχ.continuous hχs hχ0
    simpa [V, mul_comm] using this
  have hFi : Integrable F := integrable_mul_of_integrableOn hU measurableSet_ball hdχc hdχs hdχ0
  -- Claim A: `∂V/∂z̄ = F` weakly, against any smooth function
  have hA : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → ∫ z, V z * dbar ψ z = -∫ z, F z * ψ z := by
    intro ψ hψ
    have ht := hw (fun z => χ z * ψ z) (hχ.mul hψ) hχs.mul_right
      ((tsupport_mul_subset_left).trans hχt)
    have hψd : ∀ z, DifferentiableAt ℝ ψ z := fun z => (hψ.differentiable (by simp)) z
    have hdψc : Continuous (dbar ψ) := by
      have := hψ.continuous_fderiv (n := ∞) (by simp)
      unfold dbar
      exact ((this.clm_apply continuous_const).add
        (continuous_const.mul (this.clm_apply continuous_const))).div_const 2
    have i1 : Integrable fun z => V z * dbar ψ z := by
      have := integrable_mul_of_integrableOn hU measurableSet_ball (hχ.continuous.mul hdψc)
        hχs.mul_right (fun z hz => by simp [hχ0 z hz])
      refine this.congr (ae_of_all _ fun z => ?_)
      simp only [V, Pi.mul_apply]; ring
    have i2 : Integrable fun z => F z * ψ z := by
      have := integrable_mul_of_integrableOn hU measurableSet_ball (hdχc.mul hψ.continuous)
        hdχs.mul_right (fun z hz => by simp [hdχ0 z hz])
      refine this.congr (ae_of_all _ fun z => ?_)
      simp only [F, Pi.mul_apply]; ring
    have hsplit : (fun z => U z * dbar (fun z => χ z * ψ z) z) =
        fun z => V z * dbar ψ z + F z * ψ z := by
      funext z
      rw [dbar_mul (hχd z) (hψd z)]
      simp only [V, F]; ring
    rw [hsplit, integral_add i1 i2] at ht
    linear_combination ht
  -- the candidate holomorphic function
  have hdist : ∀ w ∈ ball x (R / 4), ∀ ζ, F ζ ≠ 0 → R / 4 ≤ ‖w - ζ‖ := by
    intro w hw ζ hζ
    have hζ' : ζ ∉ ball x (R / 2) := fun h => hζ (by simp [F, hdχ ζ h])
    rw [mem_ball, not_lt, dist_eq_norm] at hζ'
    rw [mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le (ζ - x) (w - x)
    rw [show ζ - x - (w - x) = -(w - ζ) by ring, norm_neg] at this
    linarith
  have hkb : ∀ w ∈ ball x (R / 4), ∀ ζ, ‖F ζ * (w - ζ)⁻¹‖ ≤ ‖F ζ‖ * (4 / R) := by
    intro w hw ζ
    by_cases hζ : F ζ = 0
    · simp [hζ]
    · rw [norm_mul, norm_inv]
      gcongr
      have := hdist w hw ζ hζ
      rw [inv_le_comm₀ (by linarith [show 0 < R / 4 by positivity]) (by positivity)]
      calc (4 / R)⁻¹ = R / 4 := by rw [inv_div]
        _ ≤ ‖w - ζ‖ := this
  let G : ℂ → ℂ := fun w => (π : ℂ)⁻¹ * ∫ ζ, F ζ * (w - ζ)⁻¹
  have hmeasK : ∀ w, AEStronglyMeasurable (fun ζ => F ζ * (w - ζ)⁻¹) := fun w =>
    hFi.aestronglyMeasurable.mul (measurable_const.sub measurable_id).inv.aestronglyMeasurable
  have hG : DifferentiableOn ℂ G (ball x (R / 4)) := by
    intro w₀ hw₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
      (F := fun w ζ => F ζ * (w - ζ)⁻¹) (x₀ := w₀)
      (F' := fun w ζ => F ζ * (-1 / (w - ζ) ^ 2))
      (bound := fun ζ => ‖F ζ‖ * (4 / R) ^ 2)
      (isOpen_ball.mem_nhds hw₀) (Eventually.of_forall hmeasK)
      ((hFi.norm.mul_const (4 / R)).mono' (hmeasK w₀) (ae_of_all _ (hkb w₀ hw₀)))
      (hFi.aestronglyMeasurable.mul
        ((((measurable_const.sub measurable_id).pow_const 2).const_div
          (-1 : ℂ)).aestronglyMeasurable))
      (ae_of_all _ fun ζ w hw => by
        by_cases hζ : F ζ = 0
        · simp [hζ]
        · have h1 := hdist w hw ζ hζ
          have hpos : 0 < ‖w - ζ‖ := by linarith [show 0 < R / 4 by positivity]
          rw [norm_mul, norm_div, norm_neg, norm_one, norm_pow]
          gcongr
          rw [div_le_iff₀ (pow_pos hpos 2), ← mul_pow]
          have : 1 ≤ 4 / R * ‖w - ζ‖ := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hR]; linarith
          exact one_le_pow₀ this)
      (hFi.norm.mul_const _)
      (ae_of_all _ fun ζ w hw => by
        by_cases hζ : F ζ = 0
        · simp only [hζ, zero_mul]; exact hasDerivAt_const w (0 : ℂ)
        · have hne : w - ζ ≠ 0 := by
            have := hdist w hw ζ hζ
            intro h; rw [h, norm_zero] at this; linarith [show 0 < R / 4 by positivity]
          have := (((hasDerivAt_id w).sub_const ζ).inv hne).const_mul (F ζ)
          simpa using this)
    exact (key.2.differentiableAt.const_mul _).differentiableWithinAt
  -- Claim B: `V = G` against test functions supported near the centre
  have hφi : ∀ φ : ℂ → ℂ, Continuous φ → HasCompactSupport φ → Integrable φ := fun φ hc hs =>
    hc.integrable_of_hasCompactSupport hs
  have hB : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x (R / 4) →
      ∫ z, V z * φ z = ∫ z, G z * φ z := by
    intro φ hφ hφs hφt
    set ψ := cauchyTransform φ
    have hψ : ContDiff ℝ ∞ ψ := contDiff_cauchyTransform (n := ⊤) hφ hφs
    have h1 : ∫ z, V z * φ z = ∫ z, V z * dbar ψ z := by
      congr 1; funext z
      rw [dbar_cauchyTransform (hφ.of_le (by simp)) hφs]
    rw [h1, hA ψ hψ]
    have eψ : ∀ ζ, ψ ζ = (π : ℂ)⁻¹ * ∫ w, (ζ - w)⁻¹ * φ w := by
      intro ζ
      show cauchyTransform φ ζ = _
      rw [cauchyTransform_eq, ← integral_sub_left_eq_self _ volume ζ]
      simp
    let K : ℂ → ℂ → ℂ := fun ζ w => F ζ * (w - ζ)⁻¹ * φ w
    have eL : ∀ ζ, F ζ * ψ ζ = -((π : ℂ)⁻¹ * ∫ w, K ζ w) := by
      intro ζ
      have : ∫ w, K ζ w = -∫ w, F ζ * ((ζ - w)⁻¹ * φ w) := by
        rw [← integral_neg]
        congr 1; funext w
        simp only [K]
        rw [show (ζ - w)⁻¹ = -(w - ζ)⁻¹ by rw [← neg_sub, inv_neg]]
        ring
      rw [eψ, this, integral_const_mul]
      ring
    have eR : ∀ w, G w * φ w = (π : ℂ)⁻¹ * ∫ ζ, K ζ w := by
      intro w
      simp only [G, K]
      rw [mul_assoc, ← integral_mul_const]
    simp_rw [eL, eR]
    rw [integral_neg, neg_neg, integral_const_mul, integral_const_mul]
    congr 1
    -- Fubini
    obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφs
    have hKi : Integrable (Function.uncurry K) (volume.prod volume) := by
      have hb : Integrable (fun p : ℂ × ℂ => (4 / R) * (‖F p.1‖ * ‖φ p.2‖))
          (volume.prod volume) :=
        (hFi.norm.mul_prod (hφi φ hφ.continuous hφs).norm).const_mul _
      refine hb.mono' ?_ (ae_of_all _ fun p => ?_)
      · exact ((hFi.aestronglyMeasurable.comp_fst).mul
          ((measurable_snd.sub measurable_fst).inv.aestronglyMeasurable)).mul
          (hφ.continuous.aestronglyMeasurable.comp_snd)
      · obtain ⟨ζ, w⟩ := p
        simp only [Function.uncurry_apply_pair, K]
        by_cases hw : φ w = 0
        · simp [hw]
        · have hwb : w ∈ ball x (R / 4) := hφt (subset_tsupport _ hw)
          rw [norm_mul]
          have := hkb w hwb ζ
          calc ‖F ζ * (w - ζ)⁻¹‖ * ‖φ w‖ ≤ ‖F ζ‖ * (4 / R) * ‖φ w‖ := by gcongr
            _ = 4 / R * (‖F ζ‖ * ‖φ w‖) := by ring
    exact integral_integral_swap hKi
  -- conclude
  have hVG : ∀ᵐ z, z ∈ ball x (R / 4) → V z - G z = 0 := by
    refine isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hVi.integrableOn.locallyIntegrableOn).sub
        (hG.continuousOn.locallyIntegrableOn measurableSet_ball))
      fun g hg hgs hgt => ?_
    set φ : ℂ → ℂ := fun z => (g z : ℂ)
    have hφ : ContDiff ℝ ∞ φ := ofRealCLM.contDiff.comp hg
    have hφs : HasCompactSupport φ := hgs.comp_left ofReal_zero
    have hφt : tsupport φ ⊆ ball x (R / 4) := (tsupport_comp_subset ofReal_zero _).trans hgt
    have := hB φ hφ hφs hφt
    obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφs
    have i1 : Integrable fun z => V z * φ z :=
      hVi.mul_bdd hφ.continuous.aestronglyMeasurable (ae_of_all _ hC)
    have i2 : Integrable fun z => G z * φ z :=
      integrable_mul_of_continuousOn isOpen_ball hG.continuousOn hφ.continuous hφs hφt
    have e : (fun z => g z • (V z - G z)) = fun z => V z * φ z - G z * φ z := by
      funext z; simp only [φ, Complex.real_smul]; ring
    rw [e, integral_sub i1 i2, this, sub_self]
  refine ⟨G, hG, ?_⟩
  filter_upwards [hVG] with z hz hzb
  have h1 : χ z = 1 := hχ1 z (ball_subset_closedBall (ball_subset_ball (by linarith) hzb))
  have := hz hzb
  simp only [V, h1, one_mul] at this
  exact sub_eq_zero.mp this

theorem dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  unfold dbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem continuous_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dbar f) := by
  have := hf.continuous_fderiv one_ne_zero
  unfold dbar
  exact ((this.clm_apply continuous_const).add
    (continuous_const.mul (this.clm_apply continuous_const))).div_const 2

/-- A cutoff times a function smooth on an open set containing its support is smooth. -/
theorem contDiff_mul_of_tsupport_subset {χ f : ℂ → ℂ} {W : Set ℂ} {n : WithTop ℕ∞}
    (hW : IsOpen W) (hχ : ContDiff ℝ n χ) (hf : ContDiffOn ℝ n f W) (hχW : tsupport χ ⊆ W) :
    ContDiff ℝ n fun z => χ z * f z := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z ∈ W
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hW.mem_nhds hz))
  · have hz' : z ∉ tsupport χ := fun h => hz (hχW h)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz'] with y hy
    simp [hy]

/-- **Weyl's lemma for `∂/∂z̄`, inhomogeneous form.** If `∂U/∂z̄ = f` weakly on a disc, with
`f` smooth, then near the centre `U` agrees a.e. with a smooth `u` with `∂u/∂z̄ = f`. -/
theorem weyl_dbar_inhom {U f : ℂ → ℂ} {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hU : IntegrableOn U (ball x R)) (hf : ContDiffOn ℝ ∞ f (ball x R))
    (hw : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x R →
      ∫ z, U z * dbar φ z = -∫ z, f z * φ z) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (ball x (R / 8)) ∧ (∀ z ∈ ball x (R / 8), dbar u z = f z) ∧
      ∀ᵐ z, z ∈ ball x (R / 8) → U z = u z := by
  let b : ContDiffBump x := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let χ : ℂ → ℂ := fun z => (b z : ℂ)
  have hχ : ContDiff ℝ ∞ χ := ofRealCLM.contDiff.comp b.contDiff
  have hχs : HasCompactSupport χ := b.hasCompactSupport.comp_left ofReal_zero
  have hχt : tsupport χ ⊆ ball x R := by
    refine (tsupport_comp_subset ofReal_zero _).trans ?_
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by show 3 * R / 4 < R; linarith)
  have hχ1 : ∀ z ∈ closedBall x (R / 2), χ z = 1 := fun z hz => by
    simp [χ, b.one_of_mem_closedBall hz]
  set ψ : ℂ → ℂ := fun z => χ z * f z
  have hψ : ContDiff ℝ ∞ ψ := contDiff_mul_of_tsupport_subset isOpen_ball hχ hf hχt
  have hψs : HasCompactSupport ψ := hχs.mul_right
  set g := cauchyTransform ψ
  have hg : ContDiff ℝ ∞ g := contDiff_cauchyTransform (n := ⊤) hψ hψs
  have hdg : ∀ z, dbar g z = ψ z := dbar_cauchyTransform (hψ.of_le (by simp)) hψs
  -- `U - g` is weakly holomorphic on the half disc
  have hW : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x (R / 2) →
      ∫ z, (U z - g z) * dbar φ z = 0 := by
    intro φ hφ hφs hφt
    have hφt' : tsupport φ ⊆ ball x R := hφt.trans (ball_subset_ball (by linarith))
    have hdφ := continuous_dbar (hφ.of_le (by simp))
    have hdφs : HasCompactSupport (dbar φ) :=
      HasCompactSupport.intro hφs.isCompact fun z hz =>
        dbar_eq_zero_of_eventuallyEq (c := 0) (notMem_tsupport_iff_eventuallyEq.mp hz)
    have hdφ0 : ∀ z ∉ ball x R, dbar φ z = 0 := fun z hz =>
      dbar_eq_zero_of_eventuallyEq (c := 0) (notMem_tsupport_iff_eventuallyEq.mp
        fun h => hz (hφt' h))
    have i1 : Integrable fun z => U z * dbar φ z :=
      integrable_mul_of_integrableOn hU measurableSet_ball hdφ hdφs hdφ0
    have i2 : Integrable fun z => g z * dbar φ z :=
      (hg.continuous.mul hdφ).integrable_of_hasCompactSupport hdφs.mul_left
    have hibp := integral_mul_dbar (hg.of_le (by simp)) (hφ.of_le (by simp)) hφs
    have hfφ : ∫ z, dbar g z * φ z = ∫ z, f z * φ z := by
      congr 1; funext z
      rw [hdg z]
      by_cases hz : z ∈ tsupport φ
      · simp [ψ, hχ1 z (ball_subset_closedBall (hφt hz))]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp_rw [sub_mul]
    rw [integral_sub i1 i2, hw φ hφ hφs hφt', hibp, hfφ]
    ring
  have hUg : IntegrableOn (fun z => U z - g z) (ball x (R / 2)) :=
    (hU.mono_set (ball_subset_ball (by linarith))).sub
      (hg.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x (R / 2))
        |>.mono_set ball_subset_closedBall)
  obtain ⟨h, hh, hae⟩ := weyl_dbar_ball (by positivity) hUg hW
  have hR8 : R / 2 / 4 = R / 8 := by ring
  rw [hR8] at hh hae
  refine ⟨fun z => g z + h z, ?_, ?_, ?_⟩
  · exact hg.contDiffOn.add (DifferentiableOn.contDiffOn_real hh isOpen_ball)
  · intro z hz
    have hhz : DifferentiableAt ℂ h z := hh.differentiableAt (isOpen_ball.mem_nhds hz)
    rw [dbar_add ((hg.differentiable (by simp)) z) (hhz.restrictScalars ℝ), hdg z,
      dbar_eq_zero_of_differentiableAt hhz, add_zero]
    simp [ψ, hχ1 z (ball_subset_closedBall (ball_subset_ball (by linarith) hz))]
  · filter_upwards [hae] with z hz hzb
    have := hz hzb
    linear_combination this

end JacobianChallenge.Analysis
