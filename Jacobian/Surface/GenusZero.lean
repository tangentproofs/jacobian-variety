import Jacobian.Surface.Extend01
import Jacobian.HolomorphicForms.MeromorphicToBranchedCover
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints

/-!
# Genus zero: a function with a single simple pole

On a compact connected Riemann surface on which every holomorphic 1-form vanishes, we build,
for any point `P`, a function `f : X → ℂ` holomorphic off `P` with a simple pole at `P`:
take the local principal part `χ(w)/(w - z₀)` (with `χ` a cutoff equal to `1` near `z₀`),
whose `∂̄` is a smooth compactly supported `(0,1)`-form `ψ`; solve `∂̄u = ψ` globally
(`dbar_solvable_of_forall_eq_zero`); then `f = χ/(w - z₀) - u`.

The one-point extension of `f` is then a holomorphic map `X → ℂ̂` of degree one, hence a
homeomorphism (`homeomorph_onePoint_of_forall_eq_zero`).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

/-! ### The local principal part -/

section Local

variable {z₀ : ℂ} (χ : ContDiffBump z₀)

/-- The cutoff, as a complex-valued function. -/
noncomputable def cutC : ℂ → ℂ := fun w => ((χ w : ℝ) : ℂ)

/-- The local principal part `χ(w)/(w - z₀)`. -/
noncomputable def ppart : ℂ → ℂ := fun w => cutC χ w * (w - z₀)⁻¹

/-- Its `∂̄`: `∂̄χ(w)/(w - z₀)` (smooth, since `∂̄χ = 0` near `z₀`). -/
noncomputable def ppartDbar : ℂ → ℂ := fun w => dbar (cutC χ) w * (w - z₀)⁻¹

theorem contDiff_cutC : ContDiff ℝ ∞ (cutC χ) :=
  ofRealCLM.contDiff.comp χ.contDiff

theorem contDiff_dbar_cutC : ContDiff ℝ ∞ (dbar (cutC χ)) :=
  contDiffOn_univ.mp (contDiffOn_dbar isOpen_univ (contDiff_cutC χ).contDiffOn)

theorem cutC_eq_one {w : ℂ} (hw : w ∈ ball z₀ χ.rIn) : cutC χ w = 1 := by
  simp [cutC, χ.one_of_mem_closedBall (ball_subset_closedBall hw)]

theorem dbar_cutC_eq_zero {w : ℂ} (hw : w ∈ ball z₀ χ.rIn) : dbar (cutC χ) w = 0 :=
  dbar_eq_zero_of_eventuallyEq (c := 1) (by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv using cutC_eq_one χ hv)

theorem cutC_eq_zero {w : ℂ} (hw : w ∉ ball z₀ χ.rOut) : cutC χ w = 0 := by
  simp only [mem_ball, not_lt] at hw
  simp [cutC, χ.zero_of_le_dist hw]

theorem ppart_eq_inv {w : ℂ} (hw : w ∈ ball z₀ χ.rIn) : ppart χ w = (w - z₀)⁻¹ := by
  simp [ppart, cutC_eq_one χ hw]

theorem ppart_eq_zero {w : ℂ} (hw : w ∉ ball z₀ χ.rOut) : ppart χ w = 0 := by
  simp [ppart, cutC_eq_zero χ hw]

theorem tsupport_ppart : tsupport (ppart χ) ⊆ closedBall z₀ χ.rOut := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  by_contra h
  exact hw (ppart_eq_zero χ fun h' => h (ball_subset_closedBall h'))

theorem tsupport_ppartDbar : tsupport (ppartDbar χ) ⊆ closedBall z₀ χ.rOut := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  by_contra h
  apply hw
  have hw' : w ∉ ball z₀ χ.rOut := fun h' => h (ball_subset_closedBall h')
  have : dbar (cutC χ) w = 0 := by
    refine dbar_eq_zero_of_eventuallyEq (c := 0) ?_
    have hc : IsClosed (closedBall z₀ χ.rOut) := isClosed_closedBall
    have hw'' : w ∉ closedBall z₀ χ.rOut := h
    filter_upwards [hc.isOpen_compl.mem_nhds hw''] with v hv
    exact cutC_eq_zero χ fun h' => hv (ball_subset_closedBall h')
  simp [ppartDbar, this]

theorem ppartDbar_eq_zero {w : ℂ} (hw : w ∈ ball z₀ χ.rIn) : ppartDbar χ w = 0 := by
  simp [ppartDbar, dbar_cutC_eq_zero χ hw]

theorem contDiff_ppartDbar : ContDiff ℝ ∞ (ppartDbar χ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = z₀
  · subst hw
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self χ.rIn_pos)] with v hv
    exact ppartDbar_eq_zero χ hv
  · have hinv : ContDiffAt ℝ ∞ (fun v : ℂ => (v - z₀)⁻¹) w :=
      ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hw))
    exact (contDiff_dbar_cutC χ).contDiffAt.mul hinv

theorem contDiffAt_ppart {w : ℂ} (hw : w ≠ z₀) : ContDiffAt ℝ ∞ (ppart χ) w :=
  (contDiff_cutC χ).contDiffAt.mul
    ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hw))

theorem dbar_ppart {w : ℂ} (hw : w ≠ z₀) : dbar (ppart χ) w = ppartDbar χ w := by
  have hinvC : DifferentiableAt ℂ (fun v : ℂ => (v - z₀)⁻¹) w :=
    (differentiableAt_id.sub (differentiableAt_const _)).inv (sub_ne_zero.mpr hw)
  have := dbar_mul (f := cutC χ) (g := fun v : ℂ => (v - z₀)⁻¹) (z := w)
    ((contDiff_cutC χ).differentiable (by simp) w) (hinvC.restrictScalars ℝ)
  show dbar (fun v => cutC χ v * (v - z₀)⁻¹) w = dbar (cutC χ) w * (w - z₀)⁻¹
  rw [this, dbar_eq_zero_of_differentiableAt hinvC, mul_zero, zero_add, mul_comm]

end Local

theorem dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  unfold dbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-! ### The global function with a single simple pole -/

section Global

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

theorem exists_bump (P : X) : ∃ χ : ContDiffBump (chartAt ℂ P P),
    closedBall (chartAt ℂ P P) χ.rOut ⊆ (chartAt ℂ P).target := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (chartAt ℂ P).open_target _ (mem_chart_target ℂ P)
  refine ⟨⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩, ?_⟩
  exact (closedBall_subset_ball (show 2 * ε / 3 < ε by linarith)).trans hball

/-- The data of the construction: a bump `χ` in the chart at `P`, and a smooth `u` with
`∂̄u = ∂̄(χ/(w - z₀))`, the right side transplanted from the chart at `P`. -/
structure PoleData (P : X) where
  χ : ContDiffBump (chartAt ℂ P P)
  hχ : closedBall (chartAt ℂ P P) χ.rOut ⊆ (chartAt ℂ P).target
  u : X → ℂ
  hu : IsSmooth u
  hdbar : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, ext01 P (ppartDbar χ) q w = dbar (rd u q) w

namespace PoleData

variable {P : X} (d : PoleData P)

/-- The function with a single simple pole at `P`: `χ/(w - z₀) - u`. -/
noncomputable def fn : X → ℂ := fun x => extend P (ppart d.χ) x - d.u x

theorem rd_fn (q : X) : rd d.fn q = fun v => rd (extend P (ppart d.χ)) q v - rd d.u q v := rfl

/-- Off `P`, the reading of `fn` in any chart is smooth with `∂̄ = 0`. -/
theorem fn_local {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (hP : (chartAt ℂ q).symm w ≠ P) :
    ContDiffAt ℝ ∞ (rd d.fn q) w ∧ dbar (rd d.fn q) w = 0 := by
  have hu := d.hu.contDiffAt hw
  suffices h : ContDiffAt ℝ ∞ (rd (extend P (ppart d.χ)) q) w ∧
      dbar (rd (extend P (ppart d.χ)) q) w = ext01 P (ppartDbar d.χ) q w by
    refine ⟨d.rd_fn q ▸ h.1.sub hu, ?_⟩
    rw [d.rd_fn q, dbar_sub (h.1.differentiableAt (by simp)) (hu.differentiableAt (by simp)), h.2,
      d.hdbar q w hw, sub_self]
  by_cases hs : (chartAt ℂ q).symm w ∈ (chartAt ℂ P).source
  · have hwo : w ∈ overlap q P := ⟨hw, hs⟩
    have hev : rd (extend P (ppart d.χ)) q =ᶠ[𝓝 w] ppart d.χ ∘ trans q P := by
      filter_upwards [(isOpen_overlap q P).mem_nhds hwo] with v hv
      have hv2 : (chartAt ℂ q).symm v ∈ (chartAt ℂ P).source := hv.2
      simp only [rd_apply, extend, if_pos hv2, Function.comp_apply]
      rfl
    have hne : trans q P w ≠ chartAt ℂ P P := by
      intro h
      exact hP ((chartAt ℂ P).injOn hs (mem_chart_source ℂ P) h)
    have hg := contDiffAt_ppart d.χ hne
    refine ⟨(hg.comp w (trans_contDiffAt hwo)).congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_congr hev, dbar_comp_holo (hg.differentiableAt (by simp))
      (trans_differentiableAt hwo), dbar_ppart d.χ hne]
    simp only [ext01, if_pos hs]
  · have hK := isCompact_closedBall (chartAt ℂ P P) d.χ.rOut
    have hx : (chartAt ℂ q).symm w ∉ (chartAt ℂ P).symm '' closedBall (chartAt ℂ P P) d.χ.rOut :=
      fun h => hs (symm_image_subset_source d.hχ h)
    have hev0 := extend_eventuallyEq_zero hK d.hχ (tsupport_ppart d.χ) hx
    have hev : rd (extend P (ppart d.χ)) q =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
      hev0.comp_tendsto ((chartAt ℂ q).continuousAt_symm hw)
    refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_eq_zero_of_eventuallyEq hev]
    simp only [ext01, if_neg hs]

/-- Off `P`, `fn` is holomorphic in charts. -/
theorem analyticAt_rd_fn {x : X} (hx : x ≠ P) :
    AnalyticAt ℂ (rd d.fn x) (chartAt ℂ x x) := by
  set W := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {P}ᶜ
  have hW : IsOpen W := (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage
    (chartAt ℂ x).open_target isOpen_compl_singleton
  have hxW : chartAt ℂ x x ∈ W := ⟨mem_chart_target ℂ x, by
    show (chartAt ℂ x).symm (chartAt ℂ x x) ≠ P
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx⟩
  refine DifferentiableOn.analyticAt (s := W) (fun w hw => ?_) (hW.mem_nhds hxW)
  obtain ⟨h1, h2⟩ := d.fn_local hw.1 hw.2
  exact (differentiableAt_of_dbar_eq_zero (h1.differentiableAt (by simp)) h2).differentiableWithinAt

/-- Near `P`, `u` is holomorphic in the chart at `P`. -/
theorem analyticAt_rd_u : AnalyticAt ℂ (rd d.u P) (chartAt ℂ P P) := by
  have hsub : ball (chartAt ℂ P P) d.χ.rIn ⊆ (chartAt ℂ P).target :=
    (ball_subset_ball d.χ.rIn_lt_rOut.le).trans (ball_subset_closedBall.trans d.hχ)
  refine DifferentiableOn.analyticAt (s := ball (chartAt ℂ P P) d.χ.rIn) (fun w hw => ?_)
    (isOpen_ball.mem_nhds (mem_ball_self d.χ.rIn_pos))
  have h1 := d.hu.contDiffAt (hsub hw)
  have h2 : dbar (rd d.u P) w = 0 := by
    rw [← d.hdbar P w (hsub hw), ext01_self (hsub hw), ppartDbar_eq_zero d.χ hw]
  exact (differentiableAt_of_dbar_eq_zero (h1.differentiableAt (by simp)) h2).differentiableWithinAt

/-- Near `P`, `fn` reads `(w - z₀)⁻¹ - u` in the chart at `P`. -/
theorem rd_fn_eq_near :
    rd d.fn P =ᶠ[𝓝 (chartAt ℂ P P)] fun w => (w - chartAt ℂ P P)⁻¹ - rd d.u P w := by
  have hsub : ball (chartAt ℂ P P) d.χ.rIn ⊆ (chartAt ℂ P).target :=
    (ball_subset_ball d.χ.rIn_lt_rOut.le).trans (ball_subset_closedBall.trans d.hχ)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self d.χ.rIn_pos)] with w hw
  rw [d.rd_fn P]
  simp only
  rw [rd_extend_self (hsub hw), ppart_eq_inv d.χ hw]

end PoleData

end Global

/-! ### The map to the Riemann sphere -/

section Sphere

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

private theorem identityChart_coe (z : ℂ) : (identityChart : OnePoint ℂ → ℂ) ↑z = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

private theorem inv_sub_eq (a b : ℂ) (ha : a ≠ 0) : (a⁻¹ - b)⁻¹ = a / (1 - a * b) := by
  rw [show a⁻¹ - b = (1 - a * b) / a by field_simp, inv_div]

namespace PoleData

variable {P : X} (d : PoleData P)

/-- The extension of `fn` to a map to the Riemann sphere, `∞` at `P`. -/
noncomputable def toSphere : X → OnePoint ℂ := onePointExtend d.fn P

theorem toSphere_at : d.toSphere P = OnePoint.infty := onePointExtend_at _ _

theorem toSphere_off {x : X} (hx : x ≠ P) : d.toSphere x = ↑(d.fn x) := onePointExtend_off hx

theorem toSphere_eq_infty_iff {x : X} : d.toSphere x = OnePoint.infty ↔ x = P := by
  refine ⟨fun h => ?_, fun h => h ▸ d.toSphere_at⟩
  by_contra hx
  rw [d.toSphere_off hx] at h
  exact OnePoint.coe_ne_infty _ h

/-- The reading of `toSphere` in the inversion chart at `∞`:
`k(v) = (v - z₀)/(1 - (v - z₀) u(v))`. -/
noncomputable def kfun : ℂ → ℂ := fun v =>
  (v - chartAt ℂ P P) / (1 - (v - chartAt ℂ P P) * rd d.u P v)

theorem analyticAt_den :
    AnalyticAt ℂ (fun v => 1 - (v - chartAt ℂ P P) * rd d.u P v) (chartAt ℂ P P) :=
  analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul d.analyticAt_rd_u)

theorem analyticAt_kfun : AnalyticAt ℂ d.kfun (chartAt ℂ P P) :=
  (analyticAt_id.sub analyticAt_const).div d.analyticAt_den
    (show (1 : ℂ) - (chartAt ℂ P P - chartAt ℂ P P) * rd d.u P (chartAt ℂ P P) ≠ 0 by simp)

theorem kfun_center : d.kfun (chartAt ℂ P P) = 0 := by simp [kfun]

theorem kfun_ne_zero : ∀ᶠ v in 𝓝 (chartAt ℂ P P), v ≠ chartAt ℂ P P → d.kfun v ≠ 0 := by
  filter_upwards [d.analyticAt_den.continuousAt.eventually_ne
    (show (1 : ℂ) - (chartAt ℂ P P - chartAt ℂ P P) * rd d.u P (chartAt ℂ P P) ≠ 0 by simp)]
    with v hv hv0
  exact div_ne_zero (sub_ne_zero.mpr hv0) hv

/-- In the inversion chart at `∞`, `toSphere` reads `kfun` near `P`. -/
theorem invFwd_toSphere_eq :
    (fun v => invFwd (d.toSphere ((chartAt ℂ P).symm v))) =ᶠ[𝓝 (chartAt ℂ P P)] d.kfun := by
  have hT := (chartAt ℂ P).open_target.mem_nhds (mem_chart_target ℂ P)
  filter_upwards [d.rd_fn_eq_near, hT] with v hv hvT
  by_cases hv0 : v = chartAt ℂ P P
  · rw [hv0, (chartAt ℂ P).left_inv (mem_chart_source ℂ P), d.toSphere_at, invFwd_infty,
      d.kfun_center]
  · have hne : (chartAt ℂ P).symm v ≠ P := fun h => by
      have := (chartAt ℂ P).right_inv hvT
      rw [h] at this
      exact hv0 this.symm
    rw [d.toSphere_off hne, invFwd_coe]
    change (rd d.fn P v)⁻¹ = _
    rw [hv, kfun, inv_sub_eq _ _ (sub_ne_zero.mpr hv0)]

theorem isHolomorphicAt_toSphere_pole : IsHolomorphicAt d.toSphere P := by
  unfold IsHolomorphicAt chartLocalAt
  rw [d.toSphere_at]
  exact d.analyticAt_kfun.congr d.invFwd_toSphere_eq.symm

theorem isHolomorphicAt_toSphere_off {x : X} (hx : x ≠ P) : IsHolomorphicAt d.toSphere x := by
  unfold IsHolomorphicAt chartLocalAt
  rw [d.toSphere_off hx]
  refine (d.analyticAt_rd_fn hx).congr ?_
  have hW : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {P}ᶜ) :=
    (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ x).open_target isOpen_compl_singleton
  have hxW : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {P}ᶜ :=
    ⟨mem_chart_target ℂ x, by
      show (chartAt ℂ x).symm (chartAt ℂ x x) ≠ P
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx⟩
  filter_upwards [hW.mem_nhds hxW] with v hv
  have hv2 : (chartAt ℂ x).symm v ≠ P := hv.2
  simp only [Function.comp_apply, d.toSphere_off hv2]
  exact (identityChart_coe _).symm

theorem isHolomorphicAt_toSphere (x : X) : IsHolomorphicAt d.toSphere x := by
  by_cases hx : x = P
  · exact hx ▸ d.isHolomorphicAt_toSphere_pole
  · exact d.isHolomorphicAt_toSphere_off hx

theorem continuousAt_fn {x : X} (hx : x ≠ P) : ContinuousAt d.fn x := by
  refine ((d.analyticAt_rd_fn hx).continuousAt.comp
    ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))).congr ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp only [Function.comp_apply, rd_apply, (chartAt ℂ x).left_inv hy]

theorem continuous_toSphere : Continuous d.toSphere := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = P
  · subst hx
    have hc : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    have h1 := hc.eventually d.invFwd_toSphere_eq
    have h2 := hc.eventually d.kfun_ne_zero
    refine ((continuousOn_univ.mp continuousOn_invBwd).continuousAt.comp
      (d.analyticAt_kfun.continuousAt.comp hc)).congr ?_
    filter_upwards [h1, h2, (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)]
      with y hy1 hy2 hys
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hys] at hy1 ⊢
    by_cases hyx : y = x
    · rw [hyx, d.toSphere_at, (d.invFwd_toSphere_eq.self_of_nhds).symm.trans rfl]
      simp [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), d.toSphere_at]
    · have hcy : chartAt ℂ x y ≠ chartAt ℂ x x := fun h =>
        hyx ((chartAt ℂ x).injOn hys (mem_chart_source ℂ x) h)
      have hk := hy2 hcy
      rw [← hy1]
      have hsrc : d.toSphere y ∈ ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ)) := by
        intro h0
        apply hk
        rw [← hy1, show d.toSphere y = ↑(0 : ℂ) from h0, invFwd_coe, inv_zero]
      exact invBwd_invFwd hsrc
  · refine (OnePoint.continuous_coe.continuousAt.comp (d.continuousAt_fn hx)).congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact (d.toSphere_off hy).symm

theorem contMDiff_toSphere :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) d.toSphere :=
  ContMDiff.of_isHolomorphic_and_continuous d.isHolomorphicAt_toSphere d.continuous_toSphere

theorem mapAnalyticOrderAt_toSphere : mapAnalyticOrderAt d.toSphere P = 1 := by
  unfold mapAnalyticOrderAt chartLocalAt
  rw [d.toSphere_at]
  have hev : (fun t => (chartAt ℂ (OnePoint.infty : OnePoint ℂ) ∘ d.toSphere ∘
      (chartAt ℂ P).symm) t - (chartAt ℂ (OnePoint.infty : OnePoint ℂ) ∘ d.toSphere ∘
      (chartAt ℂ P).symm) (chartAt ℂ P P)) =ᶠ[𝓝 (chartAt ℂ P P)] d.kfun := by
    have h0 : invFwd (d.toSphere ((chartAt ℂ P).symm (chartAt ℂ P P))) =
        d.kfun (chartAt ℂ P P) := d.invFwd_toSphere_eq.self_of_nhds
    filter_upwards [d.invFwd_toSphere_eq] with t ht
    change invFwd (d.toSphere ((chartAt ℂ P).symm t)) -
      invFwd (d.toSphere ((chartAt ℂ P).symm (chartAt ℂ P P))) = _
    rw [ht, h0, d.kfun_center, sub_zero]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev]
  have : analyticOrderAt d.kfun (chartAt ℂ P P) = (1 : ℕ) := by
    rw [d.analyticAt_kfun.analyticOrderAt_eq_natCast]
    refine ⟨fun v => (1 - (v - chartAt ℂ P P) * rd d.u P v)⁻¹,
      d.analyticAt_den.inv (by simp), by simp, Eventually.of_forall fun v => ?_⟩
    simp [kfun, div_eq_mul_inv]
  rw [this]
  rfl

theorem nonconst_toSphere : ¬ ∃ y₀ : OnePoint ℂ, ∀ x, d.toSphere x = y₀ := by
  rintro ⟨y₀, hy₀⟩
  haveI : Nonempty X := ⟨P⟩
  obtain ⟨a, b, hab⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := X)
  have h : ∀ x, x = P := fun x => d.toSphere_eq_infty_iff.mp ((hy₀ x).trans
    ((hy₀ P).symm.trans d.toSphere_at))
  exact hab ((h a).trans (h b).symm)

/-- **Degree one.** `toSphere` is a bijection `X → ℂ̂`. -/
theorem bijective_toSphere [CompactSpace X] [ConnectedSpace X] :
    Function.Bijective d.toSphere := by
  have hf := d.contMDiff_toSphere
  have hHol := isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hw := hasWeightedFiberConservation_of_contMDiff hf
  let B := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic hHol hw
    d.nonconst_toSphere
  refine degree_one_bijective B ?_
  rw [branchedDegree_eq_weightedFiberCard B OnePoint.infty]
  have hfib : (B.finite_fiber OnePoint.infty).toFinset = {P} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_singleton]
    exact d.toSphere_eq_infty_iff
  show ((B.finite_fiber OnePoint.infty).toFinset).sum B.ramificationIndex = 1
  rw [hfib, Finset.sum_singleton]
  exact d.mapAnalyticOrderAt_toSphere

end PoleData

/-- **Genus zero ⇒ Riemann sphere.** A compact connected Riemann surface on which every
holomorphic 1-form vanishes is homeomorphic to `ℂ̂`. -/
theorem homeomorph_onePoint_of_forall_eq_zero [CompactSpace X] [ConnectedSpace X]
    (h0 : ∀ η : HolomorphicOneForm ℂ X, η = 0) : Nonempty (X ≃ₜ OnePoint ℂ) := by
  obtain ⟨P⟩ : Nonempty X := inferInstance
  obtain ⟨χ, hχ⟩ := exists_bump P
  obtain ⟨u, hu, hdbar⟩ := dbar_solvable_of_forall_eq_zero h0 (ext01_is01 P (ppartDbar χ))
    (smoothFam_ext01 (contDiff_ppartDbar χ) (isCompact_closedBall _ _) hχ (tsupport_ppartDbar χ))
  let d : PoleData P := ⟨χ, hχ, u, hu, hdbar⟩
  let e : X ≃ OnePoint ℂ := Equiv.ofBijective d.toSphere d.bijective_toSphere
  have he : Continuous e := d.continuous_toSphere
  exact ⟨he.homeoOfEquivCompactToT2⟩

end Sphere

end JacobianChallenge.Surface
