import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Poincaré inequality on a square (`L¹` form)

For `f : ℝ × ℝ → ℂ` of class `C¹` and the square `B = [a, a+L] × [b, b+L]`,

  `∫_B ‖f - f_B‖ ≤ L ∫_B (‖∂₁ f‖ + ‖∂₂ f‖)`,

where `f_B` is the mean of `f` over `B`. Proof: `f(p) - f(q)` is a horizontal plus a vertical
increment, each bounded by the integral of the partial derivative along a full side; integrate
over `p, q ∈ B` (Fubini).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Filter Topology

/-- The closed square `[a, a+L] × [b, b+L]`. -/
def box (a b L : ℝ) : Set (ℝ × ℝ) := Icc a (a + L) ×ˢ Icc b (b + L)

theorem measurableSet_box (a b L : ℝ) : MeasurableSet (box a b L) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem isCompact_box (a b L : ℝ) : IsCompact (box a b L) :=
  isCompact_Icc.prod isCompact_Icc

theorem volume_real_box (a b : ℝ) {L : ℝ} (hL : 0 ≤ L) : volume.real (box a b L) = L ^ 2 := by
  rw [box, Measure.volume_eq_prod, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul,
    Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Increment of a `C¹` function along a segment of a line, bounded by the integral of the
norm of the derivative over a containing interval. -/
theorem norm_sub_le_integral_norm_deriv {F F' : ℝ → ℂ} {α β s t : ℝ}
    (hF : ∀ τ, HasDerivAt F (F' τ) τ) (hF' : Continuous F') (hs : s ∈ Icc α β)
    (ht : t ∈ Icc α β) : ‖F s - F t‖ ≤ ∫ τ in α..β, ‖F' τ‖ := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hF τ)
    (hF'.intervalIntegrable _ _)]
  refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
  rw [intervalIntegral.integral_of_le (hs.1.trans hs.2)]
  refine setIntegral_mono_set (hF'.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ fun _ => norm_nonneg _) (Eventually.of_forall fun τ hτ => ?_)
  simp only [uIoc] at hτ
  exact ⟨lt_of_le_of_lt (le_min ht.1 hs.1) hτ.1, hτ.2.trans (max_le ht.2 hs.2)⟩

variable {f : ℝ × ℝ → ℂ}

/-- **Poincaré inequality** on a square, `L¹` form. -/
theorem poincare_box (hf : ContDiff ℝ 1 f) (a b : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ p in box a b L, ‖f p - (L ^ 2)⁻¹ • ∫ q in box a b L, f q‖ ≤
      L * ∫ p in box a b L, (‖fderiv ℝ f p (1, 0)‖ + ‖fderiv ℝ f p (0, 1)‖) := by
  set B := box a b L
  set I := Icc a (a + L)
  set J := Icc b (b + L)
  have hB : MeasurableSet B := measurableSet_box a b L
  have hBc : IsCompact B := isCompact_box a b L
  have hvol : volume.real B = L ^ 2 := volume_real_box a b hL.le
  have hL2 : (L ^ 2) ≠ 0 := by positivity
  have hdf : ∀ p, HasFDerivAt f (fderiv ℝ f p) p := fun p =>
    ((hf.differentiable one_ne_zero) p).hasFDerivAt
  have hDc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set g₁ : ℝ × ℝ → ℂ := fun p => fderiv ℝ f p (1, 0)
  set g₂ : ℝ × ℝ → ℂ := fun p => fderiv ℝ f p (0, 1)
  have hg₁ : Continuous g₁ := hDc.clm_apply continuous_const
  have hg₂ : Continuous g₂ := hDc.clm_apply continuous_const
  set h₁ : ℝ → ℝ := fun y => ∫ t in a..a + L, ‖g₁ (t, y)‖
  set h₂ : ℝ → ℝ := fun x => ∫ t in b..b + L, ‖g₂ (x, t)‖
  have hh₁ : Continuous h₁ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y t => ‖g₁ (t, y)‖) (by fun_prop) _ _
  have hh₂ : Continuous h₂ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => ‖g₂ (x, t)‖) (by fun_prop) _ _
  -- (1) the two-step increment bound
  have hinc : ∀ p ∈ B, ∀ q ∈ B, ‖f p - f q‖ ≤ h₁ p.2 + h₂ q.1 := by
    rintro ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩
    have e : f (p₁, p₂) - f (q₁, q₂) = (f (p₁, p₂) - f (q₁, p₂)) + (f (q₁, p₂) - f (q₁, q₂)) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine norm_sub_le_integral_norm_deriv (F := fun t => f (t, p₂))
        (F' := fun t => g₁ (t, p₂)) (fun τ => ?_) (by fun_prop) hp₁ hq₁
      exact (hdf _).comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ p₂))
    · refine norm_sub_le_integral_norm_deriv (F := fun t => f (q₁, t))
        (F' := fun t => g₂ (q₁, t)) (fun τ => ?_) (by fun_prop) hp₂ hq₂
      exact (hdf _).comp_hasDerivAt τ ((hasDerivAt_const τ q₁).prodMk (hasDerivAt_id τ))
  -- integrability facts
  have hh₁i : IntegrableOn (fun p : ℝ × ℝ => h₁ p.2) B :=
    (hh₁.comp continuous_snd).continuousOn.integrableOn_compact hBc
  have hh₂i : IntegrableOn (fun p : ℝ × ℝ => h₂ p.1) B :=
    (hh₂.comp continuous_fst).continuousOn.integrableOn_compact hBc
  have hfi : IntegrableOn f B := hf.continuous.continuousOn.integrableOn_compact hBc
  have hcont2 : ∀ p, Continuous fun q => ‖f p - f q‖ := fun p => by fun_prop
  -- (2) pointwise bound on the deviation from the mean
  set c : ℂ := (L ^ 2)⁻¹ • ∫ q in B, f q
  set M₂ : ℝ := ∫ q in B, h₂ q.1
  have hdev : ∀ p ∈ B, ‖f p - c‖ ≤ h₁ p.2 + (L ^ 2)⁻¹ * M₂ := by
    intro p hp
    have e : f p - c = (L ^ 2)⁻¹ • ∫ q in B, (f p - f q) := by
      rw [integral_sub (continuous_const.continuousOn.integrableOn_compact hBc) hfi, setIntegral_const,
        hvol, smul_sub, smul_smul, inv_mul_cancel₀ hL2, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖∫ q in B, (f p - f q)‖ ≤ ∫ q in B, (h₁ p.2 + h₂ q.1) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on ((hcont2 p).continuousOn.integrableOn_compact hBc)
        ((continuous_const.add (hh₂.comp continuous_fst)).continuousOn.integrableOn_compact hBc)
        hB fun q hq => hinc p hp q hq
    have h2 : ∫ q in B, (h₁ p.2 + h₂ q.1) = L ^ 2 * h₁ p.2 + M₂ := by
      rw [integral_add (continuous_const.continuousOn.integrableOn_compact hBc) hh₂i,
        setIntegral_const,
        hvol, smul_eq_mul]
    calc (L ^ 2)⁻¹ * ‖∫ q in B, (f p - f q)‖ ≤ (L ^ 2)⁻¹ * (L ^ 2 * h₁ p.2 + M₂) := by
          rw [← h2]; gcongr
      _ = h₁ p.2 + (L ^ 2)⁻¹ * M₂ := by field_simp
  -- (3) integrate
  have hstep : ∫ p in B, ‖f p - c‖ ≤ (∫ p in B, h₁ p.2) + M₂ := by
    calc ∫ p in B, ‖f p - c‖ ≤ ∫ p in B, (h₁ p.2 + (L ^ 2)⁻¹ * M₂) :=
          setIntegral_mono_on ((hf.continuous.sub continuous_const).norm.continuousOn
            |>.integrableOn_compact hBc)
            ((hh₁.comp continuous_snd).add continuous_const |>.continuousOn
              |>.integrableOn_compact hBc) hB hdev
      _ = (∫ p in B, h₁ p.2) + M₂ := by
          rw [integral_add hh₁i (continuous_const.continuousOn.integrableOn_compact hBc),
            setIntegral_const, hvol, smul_eq_mul]
          field_simp
  -- (4) Fubini for the two terms
  have hg₁i : IntegrableOn (fun p => ‖g₁ p‖) B := hg₁.norm.continuousOn.integrableOn_compact hBc
  have hg₂i : IntegrableOn (fun p => ‖g₂ p‖) B := hg₂.norm.continuousOn.integrableOn_compact hBc
  have hT₁ : ∫ p in B, h₁ p.2 = L * ∫ p in B, ‖g₁ p‖ := by
    have e1 : ∫ p in B, h₁ p.2 = L * ∫ y in J, h₁ y := by
      have hi : IntegrableOn (fun p : ℝ × ℝ => h₁ p.2) (I ×ˢ J) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hh₁.comp continuous_snd).continuousOn.integrableOn_compact hBc
      rw [show B = I ×ˢ J from rfl, Measure.volume_eq_prod, setIntegral_prod _ hi]
      simp only [setIntegral_const, smul_eq_mul]
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    have e2 : ∫ y in J, h₁ y = ∫ p in B, ‖g₁ p‖ := by
      simp only [h₁]
      have : ∀ y, ∫ t in a..a + L, ‖g₁ (t, y)‖ = ∫ t in I, ‖g₁ (t, y)‖ := fun y => by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      simp_rw [this]
      have hi : IntegrableOn (fun p => ‖g₁ p‖) (I ×ˢ J) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hg₁i
      rw [show B = I ×ˢ J from rfl, Measure.volume_eq_prod, setIntegral_prod _ hi]
      rw [← integral_integral_swap]
      rw [IntegrableOn, ← Measure.prod_restrict] at hi
      exact hi
    rw [e1, e2]
  have hT₂ : M₂ = L * ∫ p in B, ‖g₂ p‖ := by
    have e1 : M₂ = L * ∫ x in I, h₂ x := by
      simp only [M₂]
      have hi : IntegrableOn (fun p : ℝ × ℝ => h₂ p.1) (I ×ˢ J) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hh₂.comp continuous_fst).continuousOn.integrableOn_compact hBc
      rw [show B = I ×ˢ J from rfl, Measure.volume_eq_prod, setIntegral_prod _ hi]
      simp only [setIntegral_const, smul_eq_mul]
      rw [integral_const_mul, Real.volume_real_Icc_of_le (by linarith)]
      ring
    have e2 : ∫ x in I, h₂ x = ∫ p in B, ‖g₂ p‖ := by
      simp only [h₂]
      have : ∀ x, ∫ t in b..b + L, ‖g₂ (x, t)‖ = ∫ t in J, ‖g₂ (x, t)‖ := fun x => by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      simp_rw [this]
      have hi : IntegrableOn (fun p => ‖g₂ p‖) (I ×ˢ J) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hg₂i
      rw [show B = I ×ˢ J from rfl, Measure.volume_eq_prod, setIntegral_prod _ hi]
    rw [e1, e2]
  calc ∫ p in B, ‖f p - c‖ ≤ (∫ p in B, h₁ p.2) + M₂ := hstep
    _ = L * ∫ p in B, (‖g₁ p‖ + ‖g₂ p‖) := by
        rw [hT₁, hT₂, integral_add hg₁i hg₂i]; ring

end JacobianChallenge.Analysis
