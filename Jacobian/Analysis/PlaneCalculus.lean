import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Calculus in the plane: the Laplacian and Green's identity

* `laplacian_eq_dirDeriv`: on `ℂ ≅ ℝ²`, `Δ f = ∂₁∂₁ f + ∂ᵢ∂ᵢ f` for `C²` functions.
* `integral_laplacian_mul`: Green's identity `∫ Δf · g = ∫ f · Δg` for `g` compactly supported
  and `f` of class `C²` on a neighbourhood of the support of `g`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Analysis

open MeasureTheory Set Metric Filter Topology Laplacian

/-- The derivative of `f` in the direction `v`. -/
noncomputable def dirDeriv (f : ℂ → ℝ) (v : ℂ) (x : ℂ) : ℝ := fderiv ℝ f x v

theorem laplacian_eq_dirDeriv {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = dirDeriv (dirDeriv f 1) 1 x + dirDeriv (dirDeriv f Complex.I) Complex.I x := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv : ∀ v, dirDeriv (dirDeriv f v) v x = fderiv ℝ (fderiv ℝ f) x v v := by
    intro v
    unfold dirDeriv
    rw [show (fun y => fderiv ℝ f y v) = fun y => (fderiv ℝ f y) ((fun _ => v) y) from rfl,
      fderiv_clm_apply h1 (differentiableAt_const v)]
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, hv, hv]
  simp [iteratedFDeriv_two_apply]

/-- A function continuous on an open set times a function supported in it is continuous. -/
theorem continuous_mul_of_tsupport_subset {a b : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun x => a x * b x := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact ((ha.continuousAt (hU.mem_nhds hx)).mul hb.continuousAt)
  · have hx' : x ∉ tsupport b := fun h => hx (hbU h)
    have hev : (fun x => a x * b x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact continuousAt_const.congr hev.symm

theorem hasCompactSupport_mul_of_right {a b : ℂ → ℝ} (hb : HasCompactSupport b) :
    HasCompactSupport fun x => a x * b x :=
  hb.mul_left

/-- First-order integration by parts in direction `v`, with `g` compactly supported and `f`
of class `C¹` on an open neighbourhood of its support. -/
theorem integral_mul_dirDeriv {f g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) (v : ℂ) :
    ∫ x, f x * dirDeriv g v x = -∫ x, dirDeriv f v x * g x := by
  have hfd : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hf'c : ContinuousOn (fun x => dirDeriv f v x) U := by
    have := (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
    exact this.clm_apply continuousOn_const
  have hg' : Continuous fun x => dirDeriv g v x :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg's : HasCompactSupport fun x => dirDeriv g v x := hgs.fderiv_apply (𝕜 := ℝ) v
  have htg' : tsupport (fun x => dirDeriv g v x) ⊆ U := by
    exact (tsupport_fderiv_apply_subset ℝ v).trans hgU
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (continuous_mul_of_tsupport_subset hU hf'c hg.continuous hgU).integrable_of_hasCompactSupport
      hgs.mul_left
  · exact (continuous_mul_of_tsupport_subset hU hf.continuousOn hg' htg').integrable_of_hasCompactSupport
      hg's.mul_left
  · exact (continuous_mul_of_tsupport_subset hU hf.continuousOn hg.continuous hgU).integrable_of_hasCompactSupport
      hgs.mul_left
  · exact fun x hx => hfd x (hgU hx)
  · intro x _
    exact (hg.differentiable one_ne_zero).differentiableAt

/-- **Green's identity** in the plane: `∫ Δf · g = ∫ f · Δg` for `g ∈ C²_c` and `f` of class
`C²` on an open neighbourhood of the support of `g`. -/
theorem integral_laplacian_mul {f g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    ∫ x, Δ f x * g x = ∫ x, f x * Δ g x := by
  -- one direction `v` at a time
  have key : ∀ v : ℂ, ∫ x, dirDeriv (dirDeriv f v) v x * g x =
      ∫ x, f x * dirDeriv (dirDeriv g v) v x := by
    intro v
    have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by norm_num)
    have hfv : ContDiffOn ℝ 1 (dirDeriv f v) U := by
      have := (hf.fderiv_of_isOpen hU (m := 1) (by norm_num))
      exact this.clm_apply contDiffOn_const
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
    have hgv : ContDiff ℝ 1 (dirDeriv g v) :=
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hgvs : HasCompactSupport (dirDeriv g v) := hgs.fderiv_apply (𝕜 := ℝ) v
    have hgvU : tsupport (dirDeriv g v) ⊆ U := by
      exact (tsupport_fderiv_apply_subset ℝ v).trans hgU
    have e1 := integral_mul_dirDeriv hU hfv hg1 hgs hgU v
    have e2 := integral_mul_dirDeriv hU hf1 hgv hgvs hgvU v
    linarith
  have hlf : ∀ x ∈ U, Δ f x = dirDeriv (dirDeriv f 1) 1 x +
      dirDeriv (dirDeriv f Complex.I) Complex.I x := fun x hx =>
    laplacian_eq_dirDeriv (hf.contDiffAt (hU.mem_nhds hx))
  have hlg : ∀ x, Δ g x = dirDeriv (dirDeriv g 1) 1 x +
      dirDeriv (dirDeriv g Complex.I) Complex.I x := fun x =>
    laplacian_eq_dirDeriv hg.contDiffAt
  have hL : (fun x => Δ f x * g x) = fun x =>
      dirDeriv (dirDeriv f 1) 1 x * g x + dirDeriv (dirDeriv f Complex.I) Complex.I x * g x := by
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [hlf x (hgU hx)]; ring
    · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hR : (fun x => f x * Δ g x) = fun x =>
      f x * dirDeriv (dirDeriv g 1) 1 x + f x * dirDeriv (dirDeriv g Complex.I) Complex.I x := by
    funext x; rw [hlg x]; ring
  -- integrability of the four pieces
  have hint : ∀ v : ℂ, Integrable (fun x => dirDeriv (dirDeriv f v) v x * g x) ∧
      Integrable (fun x => f x * dirDeriv (dirDeriv g v) v x) := by
    intro v
    have hffc : ContinuousOn (dirDeriv (dirDeriv f v) v) U := by
      have h2 : ContDiffOn ℝ 1 (dirDeriv f v) U := by
        have := (hf.fderiv_of_isOpen hU (m := 1) (by norm_num))
        exact this.clm_apply contDiffOn_const
      exact (h2.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    have hggc : Continuous (dirDeriv (dirDeriv g v) v) := by
      have h2 : ContDiff ℝ 1 (dirDeriv g v) :=
        (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      exact (h2.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hggs : HasCompactSupport (dirDeriv (dirDeriv g v) v) :=
      (hgs.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v
    have hggU : tsupport (dirDeriv (dirDeriv g v) v) ⊆ U := by
      exact (tsupport_fderiv_apply_subset ℝ v).trans
        ((tsupport_fderiv_apply_subset ℝ v).trans hgU)
    exact ⟨(continuous_mul_of_tsupport_subset hU hffc hg.continuous hgU).integrable_of_hasCompactSupport
        hgs.mul_left,
      (continuous_mul_of_tsupport_subset hU hf.continuousOn hggc hggU).integrable_of_hasCompactSupport
        hggs.mul_left⟩
  rw [hL, hR, integral_add (hint 1).1 (hint Complex.I).1, integral_add (hint 1).2 (hint Complex.I).2,
    key 1, key Complex.I]

end JacobianChallenge.Analysis
