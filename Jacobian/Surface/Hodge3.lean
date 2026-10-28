import Jacobian.Surface.Hodge2
import Jacobian.Analysis.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Hodge decomposition, part 3: `‖∂v‖ = ‖∂̄v‖`

* `dz_dbar_comm`: `∂∂̄ = ∂̄∂` on `C²` functions (symmetry of second derivatives).
* `integral_norm_dz_eq`: on a compact surface `∫ |∂v|² = ∫ |∂̄v|²`; the difference is
  `∂(v ∂̄v̄) - ∂̄(v ∂v̄)`, which integrates to `0` by Stokes.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

theorem hasFDerivAt_fderiv_apply {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ f) z)
    (v : ℂ) : HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) z).flip v) z := by
  have := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  simpa using this

/-- `∂∂̄ = ∂̄∂` on `C²` functions. -/
theorem dz_dbar_comm {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dbar f) z = dbar (dz f) z := by
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set D := fderiv ℝ (fderiv ℝ f) z
  have h1 := hasFDerivAt_fderiv_apply hd 1
  have hI := hasFDerivAt_fderiv_apply hd I
  have hdb : HasFDerivAt (dbar f) ((2 : ℂ)⁻¹ • (D.flip 1 + I • D.flip I)) z := by
    have := (h1.add (hI.const_smul I)).const_smul (2 : ℂ)⁻¹
    convert this using 1
    funext y; simp only [dbar, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hdz : HasFDerivAt (dz f) ((2 : ℂ)⁻¹ • (D.flip 1 - I • D.flip I)) z := by
    have := (h1.sub (hI.const_smul I)).const_smul (2 : ℂ)⁻¹
    convert this using 1
    funext y; simp only [dz, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  show (fderiv ℝ (dbar f) z 1 - I * fderiv ℝ (dbar f) z I) / 2 =
    (fderiv ℝ (dz f) z 1 + I * fderiv ℝ (dz f) z I) / 2
  rw [hdb.fderiv, hdz.fderiv]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  have hs : D 1 I = D I 1 := hsymm 1 I
  rw [hs]
  ring

/-! ### Poincaré on squares in `ℂ` -/

/-- The closed square `[a, a+L] × [b, b+L]` in `ℂ`. -/
def cbox (a b L : ℝ) : Set ℂ := measurableEquivRealProd ⁻¹' box a b L

theorem measurableSet_cbox (a b L : ℝ) : MeasurableSet (cbox a b L) :=
  measurableEquivRealProd.measurable (measurableSet_box a b L)

theorem mem_cbox {a b L : ℝ} {w : ℂ} :
    w ∈ cbox a b L ↔ w.re ∈ Icc a (a + L) ∧ w.im ∈ Icc b (b + L) := Iff.rfl

theorem setIntegral_cbox {a b L : ℝ} (g : ℝ × ℝ → ℂ) :
    ∫ w in cbox a b L, g (measurableEquivRealProd w) = ∫ p in box a b L, g p :=
  Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    measurableEquivRealProd.measurableEmbedding g _

theorem setIntegral_cbox_real {a b L : ℝ} (g : ℝ × ℝ → ℝ) :
    ∫ w in cbox a b L, g (measurableEquivRealProd w) = ∫ p in box a b L, g p :=
  Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    measurableEquivRealProd.measurableEmbedding g _

theorem equivRealProdCLM_symm_measurableEquiv (w : ℂ) :
    Complex.equivRealProdCLM.symm (measurableEquivRealProd w) = w := by
  rw [Complex.equivRealProdCLM_symm_apply, Complex.measurableEquivRealProd_apply]
  exact Complex.re_add_im w

theorem fderiv_apply_eq_dz_add_dbar (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z 1 = dz f z + dbar f z := by unfold dz dbar; ring

theorem fderiv_apply_I_eq (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z I = I * (dz f z - dbar f z) := by
  unfold dz dbar; ring_nf; rw [Complex.I_sq]; ring

/-- **Poincaré inequality** on a square of `ℂ`, `L¹` form. -/
theorem poincare_cbox {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (a b : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ w in cbox a b L, ‖f w - (L ^ 2)⁻¹ • ∫ v in cbox a b L, f v‖ ≤
      L * ∫ w in cbox a b L, (‖fderiv ℝ f w 1‖ + ‖fderiv ℝ f w I‖) := by
  set F : ℝ × ℝ → ℂ := f ∘ Complex.equivRealProdCLM.symm
  have hF : ContDiff ℝ 1 F := hf.comp Complex.equivRealProdCLM.symm.contDiff
  have h := poincare_box hF a b hL
  have hfF : ∀ w, F (measurableEquivRealProd w) = f w := fun w => by
    show f (Complex.equivRealProdCLM.symm (measurableEquivRealProd w)) = f w
    rw [equivRealProdCLM_symm_measurableEquiv]
  have hdF : ∀ p v, fderiv ℝ F p v = fderiv ℝ f (Complex.equivRealProdCLM.symm p)
      (Complex.equivRealProdCLM.symm v) := by
    intro p v
    have := ((hf.differentiable one_ne_zero) (Complex.equivRealProdCLM.symm p)).hasFDerivAt.comp p
      Complex.equivRealProdCLM.symm.hasFDerivAt
    rw [this.fderiv]; rfl
  have e10 : Complex.equivRealProdCLM.symm (1, 0) = 1 := by
    simp [Complex.equivRealProdCLM_symm_apply]
  have e01 : Complex.equivRealProdCLM.symm (0, 1) = I := by
    simp [Complex.equivRealProdCLM_symm_apply]
  have hmean : ∫ q in box a b L, F q = ∫ v in cbox a b L, f v := by
    rw [← setIntegral_cbox]; simp_rw [hfF]
  rw [hmean] at h
  rw [← setIntegral_cbox_real (g := fun p => ‖F p - (L ^ 2)⁻¹ • ∫ v in cbox a b L, f v‖),
    ← setIntegral_cbox_real (g := fun p => ‖fderiv ℝ F p (1, 0)‖ + ‖fderiv ℝ F p (0, 1)‖)] at h
  simp_rw [hfF, hdF, equivRealProdCLM_symm_measurableEquiv, e10, e01] at h
  exact h

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem integral_sub {σ τ : X → ℂ → ℂ} (hσ : ∀ q, ContinuousOn (σ q) (chartAt ℂ q).target)
    (hτ : ∀ q, ContinuousOn (τ q) (chartAt ℂ q).target) :
    A.integral (σ - τ) = A.integral σ - A.integral τ := by
  unfold integral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hS := (A.S_subset_closedBall i)
  have hK := A.closedBall_subset_target i
  exact MeasureTheory.integral_sub ((((hσ _).mono hK).integrableOn_compact (isCompact_closedBall _ _)).mono_set hS)
    ((((hτ _).mono hK).integrableOn_compact (isCompact_closedBall _ _)).mono_set hS)

/-- **`∫ |∂v|² = ∫ |∂̄v|²`** on a compact surface. -/
theorem integral_norm_dz_eq [CompactSpace X] {v : X → ℂ} (hv : IsSmooth v) :
    A.integral (fun p w => (starRingEnd ℂ) (dzF v p w) * dzF v p w) =
      A.integral (fun p w => (starRingEnd ℂ) (dbarF v p w) * dbarF v p w) := by
  set vb : X → ℂ := fun x => (starRingEnd ℂ) (v x)
  have hvb : IsSmooth vb := hv.conj
  set γ := smulF v (dbarF vb)
  set β := smulF v (dzF vb)
  have hγ : Is01 γ := (dbarF_is01 hvb).smulF v
  have hβ : Is10 β := (dzF_is10 hvb).smulF v
  have hγs : SmoothFam γ := (smoothFam_dbarF hvb).smulF hv
  have hβs : SmoothFam β := (smoothFam_dzF hvb).smulF hv
  have h1 := A.integral_dzFam_eq_zero hγ hγs
  have h2 := A.integral_dbarFam_eq_zero hβ hβs
  have hdiff : A.integral (fun p w => (starRingEnd ℂ) (dzF v p w) * dzF v p w) -
      A.integral (fun p w => (starRingEnd ℂ) (dbarF v p w) * dbarF v p w) =
      A.integral (dzFam γ) - A.integral (dbarFam β) := by
    have hc1 : ∀ q, ContinuousOn (fun w => (starRingEnd ℂ) (dzF v q w) * dzF v q w)
        (chartAt ℂ q).target := fun q =>
      (Complex.continuous_conj.comp_continuousOn ((smoothFam_dzF hv).contFam q)).mul
        ((smoothFam_dzF hv).contFam q)
    have hc2 : ∀ q, ContinuousOn (fun w => (starRingEnd ℂ) (dbarF v q w) * dbarF v q w)
        (chartAt ℂ q).target := fun q =>
      (Complex.continuous_conj.comp_continuousOn ((smoothFam_dbarF hv).contFam q)).mul
        ((smoothFam_dbarF hv).contFam q)
    have hc3 : ∀ q, ContinuousOn (dzFam γ q) (chartAt ℂ q).target := fun q =>
      (contDiffOn_dz (chartAt ℂ q).open_target (hγs q)).continuousOn
    have hc4 : ∀ q, ContinuousOn (dbarFam β q) (chartAt ℂ q).target := fun q =>
      (contDiffOn_dbar (chartAt ℂ q).open_target (hβs q)).continuousOn
    rw [← A.integral_sub hc1 hc2, ← A.integral_sub hc3 hc4]
    refine A.integral_congr fun i w hw => ?_
    have e1 : γ (A.p i) = fun w => rd v (A.p i) w * dbar (rd vb (A.p i)) w := rfl
    have e2 : β (A.p i) = fun w => rd v (A.p i) w * dz (rd vb (A.p i)) w := rfl
    simp only [Pi.sub_apply, dzFam, dbarFam, dzF, dbarF]
    rw [e1, e2]
    have hvd := hv.differentiableAt hw
    have hvbd := hvb.differentiableAt hw (p := A.p i)
    have hrd : rd vb (A.p i) = fun w => (starRingEnd ℂ) (rd v (A.p i) w) := rfl
    have hc : ContDiffAt ℝ ∞ (rd vb (A.p i)) w := hvb.contDiffAt hw
    have hdbd : DifferentiableAt ℝ (dbar (rd vb (A.p i))) w :=
      ((contDiffOn_dbar (chartAt ℂ (A.p i)).open_target (hvb (A.p i))).contDiffAt
        ((chartAt ℂ (A.p i)).open_target.mem_nhds hw)).differentiableAt (by simp)
    have hdzd : DifferentiableAt ℝ (dz (rd vb (A.p i))) w :=
      ((contDiffOn_dz (chartAt ℂ (A.p i)).open_target (hvb (A.p i))).contDiffAt
        ((chartAt ℂ (A.p i)).open_target.mem_nhds hw)).differentiableAt (by simp)
    rw [dz_mul hvd hdbd, dbar_mul hvd hdzd, dz_dbar_comm (hc.of_le (WithTop.coe_le_coe.mpr le_top)), hrd,
      dbar_conj hvd, dz_conj hvd]
    ring
  rw [h1, h2, sub_zero, sub_eq_zero] at hdiff
  exact hdiff

theorem norm_toL2_dzF_eq [CompactSpace X] {v : X → ℂ} (hv : IsSmooth v) :
    ‖A.toL2 (dzF v) (smoothFam_dzF hv).contFam‖ = ‖A.toL2 (dbarF v) (smoothFam_dbarF hv).contFam‖ := by
  have h := A.integral_norm_dz_eq hv
  have e1 := A.norm_toL2_sq (smoothFam_dzF hv).contFam
  have e2 := A.norm_toL2_sq (smoothFam_dbarF hv).contFam
  rw [h] at e1
  rw [← e2] at e1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp e1

end DiscAtlas

end JacobianChallenge.Surface
