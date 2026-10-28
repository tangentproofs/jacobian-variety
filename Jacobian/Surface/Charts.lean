import Jacobian.Analysis.WeylDbar
import Jacobian.HolomorphicForms.TraceLocal
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Calculus on a Riemann surface in charts

* `rd u p = u ∘ c_p⁻¹`: the reading of a function in the chart at `p`;
  `trans p q = c_q ∘ c_p⁻¹`: the transition map, holomorphic on `overlap p q`.
* `dz`, `dbar`: the Wirtinger derivatives; chain rules under holomorphic maps
  (`dbar_comp_holo`, `dz_comp_holo`), giving the transformation laws of `∂u` (type `(1,0)`)
  and `∂̄u` (type `(0,1)`).
* `IsSmooth u`: every chart reading is `C^∞` (over `ℝ`) on the chart target.
* Change of variables under a holomorphic injective map, with Jacobian `|τ'|²`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods MeasureTheory Set Metric Filter
  Topology Complex
open scoped Manifold ContDiff

/-! ### Wirtinger calculus in the plane -/

/-- The Wirtinger derivative `∂/∂z = ½(∂ₓ - i ∂_y)`. -/
noncomputable def dz (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) / 2

/-- An `ℝ`-linear map on `ℂ` in Wirtinger form: `D a = a ∂ + ā ∂̄`. -/
theorem clm_apply_eq_wirtinger (D : ℂ →L[ℝ] ℂ) (a : ℂ) :
    D a = a * ((D 1 - I * D I) / 2) + (starRingEnd ℂ) a * ((D 1 + I * D I) / 2) := by
  rw [clm_apply_eq_re_im D a]
  conv_rhs => rw [← Complex.re_add_im a]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Chain rule for `∂/∂z̄` under a holomorphic map: `∂̄(g ∘ τ) = conj(τ') (∂̄g) ∘ τ`. -/
theorem dbar_comp_holo {g τ : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g (τ w))
    (hτ : DifferentiableAt ℂ τ w) :
    dbar (g ∘ τ) w = (starRingEnd ℂ) (deriv τ w) * dbar g (τ w) := by
  have hτr : HasFDerivAt τ ((fderiv ℂ τ w).restrictScalars ℝ) w :=
    hτ.hasFDerivAt.restrictScalars ℝ
  have h := (hg.hasFDerivAt.comp w hτr).fderiv
  unfold dbar
  rw [h]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  have e1 : fderiv ℂ τ w 1 = deriv τ w := fderiv_apply_one_eq_deriv
  have eI : fderiv ℂ τ w I = I * deriv τ w := by
    rw [← e1, ← smul_eq_mul, ← (fderiv ℂ τ w).map_smul, smul_eq_mul, mul_one]
  rw [e1, eI, clm_apply_eq_wirtinger (fderiv ℝ g (τ w)) (deriv τ w),
    clm_apply_eq_wirtinger (fderiv ℝ g (τ w)) (I * deriv τ w)]
  simp only [map_mul, Complex.conj_I]
  set A := fderiv ℝ g (τ w) 1
  set B := fderiv ℝ g (τ w) I
  set t := deriv τ w
  linear_combination ((t * ((A - I * B) / 2) - (starRingEnd ℂ) t * ((A + I * B) / 2)) / 2) *
    Complex.I_sq

/-- Chain rule for `∂/∂z` under a holomorphic map: `∂(g ∘ τ) = τ' (∂g) ∘ τ`. -/
theorem dz_comp_holo {g τ : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g (τ w))
    (hτ : DifferentiableAt ℂ τ w) :
    dz (g ∘ τ) w = deriv τ w * dz g (τ w) := by
  have hτr : HasFDerivAt τ ((fderiv ℂ τ w).restrictScalars ℝ) w :=
    hτ.hasFDerivAt.restrictScalars ℝ
  have h := (hg.hasFDerivAt.comp w hτr).fderiv
  unfold dz
  rw [h]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  have e1 : fderiv ℂ τ w 1 = deriv τ w := fderiv_apply_one_eq_deriv
  have eI : fderiv ℂ τ w I = I * deriv τ w := by
    rw [← e1, ← smul_eq_mul, ← (fderiv ℂ τ w).map_smul, smul_eq_mul, mul_one]
  rw [e1, eI, clm_apply_eq_wirtinger (fderiv ℝ g (τ w)) (deriv τ w),
    clm_apply_eq_wirtinger (fderiv ℝ g (τ w)) (I * deriv τ w)]
  simp only [map_mul, Complex.conj_I]
  set A := fderiv ℝ g (τ w) 1
  set B := fderiv ℝ g (τ w) I
  set t := deriv τ w
  linear_combination (((starRingEnd ℂ) t * ((A + I * B) / 2) - t * ((A - I * B) / 2)) / 2) *
    Complex.I_sq

/-- The real Jacobian of a holomorphic map is `|τ'|²`. -/
theorem det_restrictScalars_fderiv {τ : ℂ → ℂ} {w : ℂ} :
    ((fderiv ℂ τ w).restrictScalars ℝ).det = ‖deriv τ w‖ ^ 2 := by
  have hL : (fderiv ℂ τ w : ℂ →ₗ[ℂ] ℂ) = deriv τ w • LinearMap.id := by
    apply LinearMap.ext_ring
    simp [fderiv_apply_one_eq_deriv]
  show LinearMap.det ((fderiv ℂ τ w : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, hL, LinearMap.det_smul, LinearMap.det_id,
    Module.finrank_self, pow_one, mul_one, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/-- **Change of variables** under a holomorphic map injective on a measurable set. -/
theorem integral_image_holo {τ : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hτ : ∀ w ∈ s, DifferentiableAt ℂ τ w) (hinj : InjOn τ s) (g : ℂ → ℂ) :
    ∫ v in τ '' s, g v = ∫ w in s, ‖deriv τ w‖ ^ 2 * g (τ w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw => ((hτ w hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  congr 1; funext w
  rw [det_restrictScalars_fderiv, abs_of_nonneg (by positivity), Complex.real_smul]
  push_cast; ring

end JacobianChallenge.Surface
