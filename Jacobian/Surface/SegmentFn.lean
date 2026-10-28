import Jacobian.Surface.GenusZero
import Jacobian.Analysis.SegmentCP

/-!
# The function `(z - b)/(z - a)` attached to a chart segment

For a chart segment `s` from `a` to `b` (in the chart at `s.p`, inside a ball `B` of the chart
target) we build a smooth nowhere-vanishing function `E s : X → ℂ`, equal to `1` away from `B`
and to `(z - b)/(z - a)` near the segment: `E = exp(χ · Log((z - b)/(z - a)))` with `χ` a
cutoff equal to `1` near the segment. Its logarithmic `∂̄`-derivative is the smooth
compactly supported `(0,1)`-form `θ s` (in the chart at `s.p`: `Log((z-b)/(z-a)) · ∂̄χ`):

* `E_local`: off the two end points, `E s` is smooth with `∂̄(E s) = (E s) · θ s` in every chart;
* `E_vertex`: at any point `v`, in the chart at `v`, `E s = (w - w₀)^e · K` on a punctured
  neighbourhood, with `K` smooth near `w₀ = c_v(v)`, `K(w₀) ≠ 0`, and `e = [v = stop] - [v = start]`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

/-- `∂̄` of `exp ∘ g`. -/
theorem dbar_cexp {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => Complex.exp (g w)) z = Complex.exp (g z) * dbar g z := by
  unfold dbar
  rw [(hg.hasFDerivAt.cexp).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

section Seg

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

namespace Seg

variable (s : ChartSegment X)

/-- The radius of a closed ball about the centre containing the segment. -/
noncomputable def ρ : ℝ := max (dist s.a s.center) (dist s.b s.center)

theorem ρ_lt : ρ s < s.radius := max_lt (mem_ball.mp s.a_mem) (mem_ball.mp s.b_mem)

theorem ρ_nonneg : 0 ≤ ρ s := le_max_of_le_left dist_nonneg

/-- The cutoff: `1` on a ball containing the segment, supported inside the segment's ball. -/
noncomputable def bump : ContDiffBump s.center where
  rIn := ρ s + (s.radius - ρ s) / 3
  rOut := ρ s + 2 * (s.radius - ρ s) / 3
  rIn_pos := by have := ρ_lt s; have := ρ_nonneg s; linarith
  rIn_lt_rOut := by have := ρ_lt s; linarith

theorem segment_subset_closedBall : segment ℝ s.a s.b ⊆ closedBall s.center (ρ s) :=
  (convex_closedBall _ _).segment_subset (mem_closedBall.mpr (le_max_left _ _))
    (mem_closedBall.mpr (le_max_right _ _))

theorem closedBall_subset_rIn : closedBall s.center (ρ s) ⊆ ball s.center (bump s).rIn :=
  closedBall_subset_ball (by simp only [bump]; linarith [ρ_lt s])

theorem a_mem_rIn : s.a ∈ ball s.center (bump s).rIn :=
  closedBall_subset_rIn s (mem_closedBall.mpr (le_max_left _ _))

theorem b_mem_rIn : s.b ∈ ball s.center (bump s).rIn :=
  closedBall_subset_rIn s (mem_closedBall.mpr (le_max_right _ _))

theorem closedBall_rOut_subset_target :
    closedBall s.center (bump s).rOut ⊆ (chartAt ℂ s.p).target :=
  (closedBall_subset_ball (by simp only [bump]; linarith [ρ_lt s])).trans s.ball_subset

theorem a_mem_target : s.a ∈ (chartAt ℂ s.p).target := s.ball_subset s.a_mem

theorem b_mem_target : s.b ∈ (chartAt ℂ s.p).target := s.ball_subset s.b_mem

/-- The logarithm `Log((z - b)/(z - a))`. -/
noncomputable def L (z : ℂ) : ℂ := Complex.log ((z - s.b) / (z - s.a))

theorem differentiableOn_L : DifferentiableOn ℂ (L s) (segment ℝ s.a s.b)ᶜ := by
  intro z hz
  have hza : z - s.a ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ left_mem_segment ℝ s.a s.b)
  have hslit := div_mem_slitPlane hz (t := 1) (by simp)
  simp only [segPt, Complex.ofReal_one, one_mul, add_sub_cancel] at hslit
  have hd : DifferentiableAt ℂ (fun w : ℂ => (w - s.b) / (w - s.a)) z :=
    (differentiableAt_id.sub (differentiableAt_const _)).div
      (differentiableAt_id.sub (differentiableAt_const _)) hza
  exact (hd.clog hslit).differentiableWithinAt

theorem isOpen_segment_compl : IsOpen (segment ℝ s.a s.b)ᶜ :=
  (by rw [segment_eq_image_lineMap]; exact (isCompact_Icc.image
    AffineMap.lineMap_continuous).isClosed.isOpen_compl)

theorem analyticAt_L {z : ℂ} (hz : z ∉ segment ℝ s.a s.b) : AnalyticAt ℂ (L s) z :=
  (differentiableOn_L s).analyticAt ((isOpen_segment_compl s).mem_nhds hz)

/-- The `(0,1)`-form in the chart at `s.p`: `Log((z-b)/(z-a)) · ∂̄χ`. -/
noncomputable def ψ (z : ℂ) : ℂ := L s z * dbar (cutC (bump s)) z

theorem ψ_eq_zero_of_mem {z : ℂ} (hz : z ∈ ball s.center (bump s).rIn) : ψ s z = 0 := by
  simp [ψ, dbar_cutC_eq_zero _ hz]

theorem not_mem_segment_of_not_mem_rIn {z : ℂ} (hz : z ∉ ball s.center (bump s).rIn) :
    z ∉ segment ℝ s.a s.b := fun h =>
  hz (closedBall_subset_rIn s (segment_subset_closedBall s h))

theorem contDiff_ψ : ContDiff ℝ ∞ (ψ s) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball s.center (bump s).rIn
  · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv using ψ_eq_zero_of_mem s hv
  · have hL : ContDiffAt ℝ ∞ (L s) z :=
      (analyticAt_L s (not_mem_segment_of_not_mem_rIn s hz)).contDiffAt.restrict_scalars ℝ
    exact hL.mul (contDiff_dbar_cutC _).contDiffAt

theorem tsupport_ψ : tsupport (ψ s) ⊆ closedBall s.center (bump s).rOut := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra h
  apply hz
  have : dbar (cutC (bump s)) z = 0 := by
    refine dbar_eq_zero_of_eventuallyEq (c := 0) ?_
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds h] with v hv
    exact cutC_eq_zero _ fun h' => hv (ball_subset_closedBall h')
  simp [ψ, this]

/-- The transplanted `(0,1)`-form. -/
noncomputable def θ : X → ℂ → ℂ := ext01 s.p (ψ s)

theorem θ_is01 : Is01 (θ s) := ext01_is01 _ _

theorem smoothFam_θ : SmoothFam (θ s) :=
  smoothFam_ext01 (contDiff_ψ s) (isCompact_closedBall _ _) (closedBall_rOut_subset_target s)
    (tsupport_ψ s)

/-- The function in the chart at `s.p`. -/
noncomputable def Ep (z : ℂ) : ℂ := Complex.exp (cutC (bump s) z * L s z)

theorem Ep_ne_zero (z : ℂ) : Ep s z ≠ 0 := Complex.exp_ne_zero _

theorem Ep_eq_one {z : ℂ} (hz : z ∉ ball s.center (bump s).rOut) : Ep s z = 1 := by
  simp [Ep, cutC_eq_zero _ hz]

theorem Ep_eq_ratio {z : ℂ} (hz : z ∈ ball s.center (bump s).rIn) (ha : z ≠ s.a)
    (hb : z ≠ s.b) : Ep s z = (z - s.b) / (z - s.a) := by
  rw [Ep, cutC_eq_one _ hz, one_mul, L, Complex.exp_log]
  exact div_ne_zero (sub_ne_zero.mpr hb) (sub_ne_zero.mpr ha)

/-- Off `a, b`, `Ep` is smooth with `∂̄ Ep = Ep · ψ`. -/
theorem Ep_local {z : ℂ} (ha : z ≠ s.a) (hb : z ≠ s.b) :
    ContDiffAt ℝ ∞ (Ep s) z ∧ dbar (Ep s) z = Ep s z * ψ s z := by
  by_cases hz : z ∈ ball s.center (bump s).rIn
  · have hev : Ep s =ᶠ[𝓝 z] fun w => (w - s.b) / (w - s.a) := by
      filter_upwards [isOpen_ball.mem_nhds hz, isOpen_ne.mem_nhds ha, isOpen_ne.mem_nhds hb]
        with w hw hwa hwb using Ep_eq_ratio s hw hwa hwb
    have hd : DifferentiableAt ℂ (fun w => (w - s.b) / (w - s.a)) z :=
      (differentiableAt_id.sub (differentiableAt_const _)).div
        (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr ha)
    have han : AnalyticAt ℂ (fun w => (w - s.b) / (w - s.a)) z :=
      ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr ha))
    refine ⟨(han.contDiffAt.restrict_scalars ℝ).congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_congr hev, dbar_eq_zero_of_differentiableAt hd, ψ_eq_zero_of_mem s hz, mul_zero]
  · have hseg := not_mem_segment_of_not_mem_rIn s hz
    have hLa := analyticAt_L s hseg
    have hg : ContDiffAt ℝ ∞ (fun w => cutC (bump s) w * L s w) z :=
      (contDiff_cutC _).contDiffAt.mul (hLa.contDiffAt.restrict_scalars ℝ)
    have hexp : ContDiffAt ℝ ∞ (Ep s) z :=
      (((Complex.contDiff_exp (𝕜 := ℂ) (n := ∞)).restrict_scalars ℝ).contDiffAt).comp z hg
    refine ⟨hexp, ?_⟩
    have hgd : DifferentiableAt ℝ (fun w => cutC (bump s) w * L s w) z :=
      hg.differentiableAt (by simp)
    rw [show Ep s = fun w => Complex.exp (cutC (bump s) w * L s w) from rfl, dbar_cexp hgd,
      dbar_mul ((contDiff_cutC _).differentiable (by simp) z)
        (hLa.differentiableAt.restrictScalars ℝ),
      dbar_eq_zero_of_differentiableAt hLa.differentiableAt]
    simp only [ψ]
    ring

open Classical in
/-- The global function: `Ep` read in the chart at `s.p`, and `1` elsewhere. -/
noncomputable def E (x : X) : ℂ :=
  if x ∈ (chartAt ℂ s.p).source then Ep s (chartAt ℂ s.p x) else 1

theorem E_ne_zero (x : X) : E s x ≠ 0 := by
  unfold E; split_ifs
  · exact Ep_ne_zero s _
  · exact one_ne_zero

theorem E_eq_one {x : X}
    (hx : x ∉ (chartAt ℂ s.p).symm '' closedBall s.center (bump s).rOut) : E s x = 1 := by
  unfold E
  split_ifs with h
  · refine Ep_eq_one s fun hb => hx ⟨_, ball_subset_closedBall hb, ?_⟩
    exact (chartAt ℂ s.p).left_inv h
  · rfl

/-- The start and end points of the segment on the surface. -/
theorem chart_eq_a_iff {x : X} (hx : x ∈ (chartAt ℂ s.p).source) :
    chartAt ℂ s.p x = s.a ↔ x = s.start := by
  constructor
  · intro h
    show x = (chartAt ℂ s.p).symm s.a
    rw [← h, (chartAt ℂ s.p).left_inv hx]
  · rintro rfl
    exact (chartAt ℂ s.p).right_inv (a_mem_target s)

theorem chart_eq_b_iff {x : X} (hx : x ∈ (chartAt ℂ s.p).source) :
    chartAt ℂ s.p x = s.b ↔ x = s.stop := by
  constructor
  · intro h
    show x = (chartAt ℂ s.p).symm s.b
    rw [← h, (chartAt ℂ s.p).left_inv hx]
  · rintro rfl
    exact (chartAt ℂ s.p).right_inv (b_mem_target s)

theorem start_mem_source : s.start ∈ (chartAt ℂ s.p).source :=
  (chartAt ℂ s.p).map_target (a_mem_target s)

theorem stop_mem_source : s.stop ∈ (chartAt ℂ s.p).source :=
  (chartAt ℂ s.p).map_target (b_mem_target s)

/-- **`E` off the end points.** -/
theorem E_local {q : X} {w : ℂ} (hw : w ∈ (chartAt ℂ q).target)
    (ha : (chartAt ℂ q).symm w ≠ s.start) (hb : (chartAt ℂ q).symm w ≠ s.stop) :
    ContDiffAt ℝ ∞ (rd (E s) q) w ∧ dbar (rd (E s) q) w = rd (E s) q w * θ s q w := by
  by_cases hs : (chartAt ℂ q).symm w ∈ (chartAt ℂ s.p).source
  · have hwo : w ∈ overlap q s.p := ⟨hw, hs⟩
    have hev : rd (E s) q =ᶠ[𝓝 w] Ep s ∘ trans q s.p := by
      filter_upwards [(isOpen_overlap q s.p).mem_nhds hwo] with v hv
      have hv2 : (chartAt ℂ q).symm v ∈ (chartAt ℂ s.p).source := hv.2
      simp only [rd_apply, E, if_pos hv2, Function.comp_apply]
      rfl
    have hza : trans q s.p w ≠ s.a := fun h => ha ((chart_eq_a_iff s hs).mp h)
    have hzb : trans q s.p w ≠ s.b := fun h => hb ((chart_eq_b_iff s hs).mp h)
    obtain ⟨h1, h2⟩ := Ep_local s hza hzb
    refine ⟨(h1.comp w (trans_contDiffAt hwo)).congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_congr hev, dbar_comp_holo (h1.differentiableAt (by simp))
      (trans_differentiableAt hwo), h2, hev.self_of_nhds]
    simp only [θ, ext01, if_pos hs, Function.comp_apply]
    ring
  · have hK := isCompact_closedBall s.center (bump s).rOut
    have hx : (chartAt ℂ q).symm w ∉
        (chartAt ℂ s.p).symm '' closedBall s.center (bump s).rOut :=
      fun h => hs (symm_image_subset_source (closedBall_rOut_subset_target s) h)
    have hev0 : E s =ᶠ[𝓝 ((chartAt ℂ q).symm w)] fun _ => (1 : ℂ) := by
      filter_upwards [((isCompact_symm_image hK
        (closedBall_rOut_subset_target s)).isClosed.isOpen_compl).mem_nhds hx] with y hy
      exact E_eq_one s hy
    have hev : rd (E s) q =ᶠ[𝓝 w] fun _ => (1 : ℂ) :=
      hev0.comp_tendsto ((chartAt ℂ q).continuousAt_symm hw)
    refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_eq_zero_of_eventuallyEq hev]
    simp only [θ, ext01, if_neg hs, mul_zero]

/-- The order of `E s` at `v`: `+1` at the end point, `-1` at the start point. -/
noncomputable def ord (v : X) : ℤ := by
  classical
  exact (if v = s.stop then 1 else 0) - (if v = s.start then 1 else 0)

theorem a_eq_b_of_start_eq_stop (h : s.start = s.stop) : s.a = s.b :=
  (chartAt ℂ s.p).symm.injOn (a_mem_target s) (b_mem_target s) h

theorem E_eq_one_of_start_eq_stop (h : s.start = s.stop) (x : X) : E s x = 1 := by
  have hab := a_eq_b_of_start_eq_stop s h
  have hL : ∀ z, L s z = 0 := fun z => by
    rw [L, hab]
    by_cases hz : z = s.b
    · simp [hz]
    · rw [div_self (sub_ne_zero.mpr hz), Complex.log_one]
  unfold E; split_ifs
  · simp [Ep, hL]
  · rfl

/-- **`E` at any point**: a zero/pole of order `ord s v` times a smooth non-vanishing factor. -/
theorem E_vertex (v : X) :
    ∃ K : ℂ → ℂ, (∀ᶠ w in 𝓝 (chartAt ℂ v v), ContDiffAt ℝ ∞ K w) ∧
      K (chartAt ℂ v v) ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] (chartAt ℂ v v),
        rd (E s) v w = (w - chartAt ℂ v v) ^ (ord s v) * K w := by
  classical
  set w₀ := chartAt ℂ v v
  have hw₀ : w₀ ∈ (chartAt ℂ v).target := mem_chart_target ℂ v
  have hsv : (chartAt ℂ v).symm w₀ = v := (chartAt ℂ v).left_inv (mem_chart_source ℂ v)
  by_cases hss : s.start = s.stop
  · -- degenerate segment: `E ≡ 1`
    refine ⟨fun _ => 1, Eventually.of_forall fun _ => contDiffAt_const, one_ne_zero,
      Eventually.of_forall fun w => ?_⟩
    have : ord s v = 0 := by unfold ord; by_cases h : v = s.stop <;> simp [h, hss]
    rw [this, zpow_zero, one_mul, rd_apply, E_eq_one_of_start_eq_stop s hss]
  by_cases hvs : v = s.start
  · -- the start point: a simple pole
    have hord : ord s v = -1 := by
      unfold ord; rw [if_neg (fun h => hss (hvs.symm.trans h)), if_pos hvs]; norm_num
    have hvsrc : v ∈ (chartAt ℂ s.p).source := hvs ▸ start_mem_source s
    have hwo : w₀ ∈ overlap v s.p := ⟨hw₀, by
      show (chartAt ℂ v).symm w₀ ∈ (chartAt ℂ s.p).source; rw [hsv]; exact hvsrc⟩
    set τ := trans v s.p
    have hτ₀ : τ w₀ = s.a := by
      show chartAt ℂ s.p ((chartAt ℂ v).symm w₀) = s.a
      rw [hsv]; exact (chart_eq_a_iff s hvsrc).mpr hvs
    have hab : s.a ≠ s.b := fun h => hss (by
      show (chartAt ℂ s.p).symm s.a = (chartAt ℂ s.p).symm s.b; rw [h])
    have hOv : overlap v s.p ∈ 𝓝 w₀ := (isOpen_overlap v s.p).mem_nhds hwo
    have hdiff : DifferentiableOn ℂ τ (overlap v s.p) := fun w hw =>
      (trans_differentiableAt hw).differentiableWithinAt
    have hds : AnalyticAt ℂ (dslope τ w₀) w₀ :=
      ((differentiableOn_dslope hOv).mpr hdiff).analyticAt hOv
    have hds₀ : dslope τ w₀ w₀ ≠ 0 := by rw [dslope_same]; exact deriv_trans_ne_zero hwo
    have hτa : AnalyticAt ℂ τ w₀ := hdiff.analyticAt hOv
    set K : ℂ → ℂ := fun w => (τ w - s.b) / dslope τ w₀ w
    have hK : AnalyticAt ℂ K w₀ := (hτa.sub analyticAt_const).div hds hds₀
    refine ⟨K, hK.eventually_analyticAt.mono fun w hw => hw.contDiffAt.restrict_scalars ℝ, ?_, ?_⟩
    · simp only [K, hτ₀]
      exact div_ne_zero (sub_ne_zero.mpr hab) hds₀
    · have hτc : ContinuousAt τ w₀ := hτa.continuousAt
      have h1 : ∀ᶠ w in 𝓝 w₀, τ w ∈ ball s.center (bump s).rIn :=
        hτc.preimage_mem_nhds (by rw [hτ₀]; exact isOpen_ball.mem_nhds (a_mem_rIn s))
      have h2 : ∀ᶠ w in 𝓝 w₀, τ w ≠ s.b := hτc.eventually_ne (by rw [hτ₀]; exact hab)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hOv, h1, h2] with w hw hw1 hw2 hne
      have hwa : τ w ≠ s.a := fun h =>
        hne (trans_injOn v s.p hw hwo (h.trans hτ₀.symm))
      have hslope : τ w - s.a = (w - w₀) * dslope τ w₀ w := by
        rw [← hτ₀, ← smul_eq_mul, sub_smul_dslope]
      have hwne : w - w₀ ≠ 0 := sub_ne_zero.mpr hne
      have hdne : dslope τ w₀ w ≠ 0 := fun h => hwa (sub_eq_zero.mp (by rw [hslope, h, mul_zero]))
      have hw2' : (chartAt ℂ v).symm w ∈ (chartAt ℂ s.p).source := hw.2
      rw [hord, rd_apply, E, if_pos hw2']
      change Ep s (τ w) = _
      rw [Ep_eq_ratio s hw1 hwa hw2, hslope, zpow_neg_one]
      simp only [K]
      field_simp
  by_cases hvt : v = s.stop
  · -- the end point: a simple zero
    have hord : ord s v = 1 := by
      unfold ord; rw [if_pos hvt, if_neg hvs]; norm_num
    have hvsrc : v ∈ (chartAt ℂ s.p).source := hvt ▸ stop_mem_source s
    have hwo : w₀ ∈ overlap v s.p := ⟨hw₀, by
      show (chartAt ℂ v).symm w₀ ∈ (chartAt ℂ s.p).source; rw [hsv]; exact hvsrc⟩
    set τ := trans v s.p
    have hτ₀ : τ w₀ = s.b := by
      show chartAt ℂ s.p ((chartAt ℂ v).symm w₀) = s.b
      rw [hsv]; exact (chart_eq_b_iff s hvsrc).mpr hvt
    have hab : s.a ≠ s.b := fun h => hss (by
      show (chartAt ℂ s.p).symm s.a = (chartAt ℂ s.p).symm s.b; rw [h])
    have hOv : overlap v s.p ∈ 𝓝 w₀ := (isOpen_overlap v s.p).mem_nhds hwo
    have hdiff : DifferentiableOn ℂ τ (overlap v s.p) := fun w hw =>
      (trans_differentiableAt hw).differentiableWithinAt
    have hds : AnalyticAt ℂ (dslope τ w₀) w₀ :=
      ((differentiableOn_dslope hOv).mpr hdiff).analyticAt hOv
    have hds₀ : dslope τ w₀ w₀ ≠ 0 := by rw [dslope_same]; exact deriv_trans_ne_zero hwo
    have hτa : AnalyticAt ℂ τ w₀ := hdiff.analyticAt hOv
    set K : ℂ → ℂ := fun w => dslope τ w₀ w / (τ w - s.a)
    have hden : τ w₀ - s.a ≠ 0 := by rw [hτ₀]; exact sub_ne_zero.mpr hab.symm
    have hK : AnalyticAt ℂ K w₀ := hds.div (hτa.sub analyticAt_const) hden
    refine ⟨K, hK.eventually_analyticAt.mono fun w hw => hw.contDiffAt.restrict_scalars ℝ,
      div_ne_zero hds₀ hden, ?_⟩
    have hτc : ContinuousAt τ w₀ := hτa.continuousAt
    have h1 : ∀ᶠ w in 𝓝 w₀, τ w ∈ ball s.center (bump s).rIn :=
      hτc.preimage_mem_nhds (by rw [hτ₀]; exact isOpen_ball.mem_nhds (b_mem_rIn s))
    have h2 : ∀ᶠ w in 𝓝 w₀, τ w ≠ s.a := hτc.eventually_ne (by rw [hτ₀]; exact hab.symm)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hOv, h1, h2] with w hw hw1 hw2 hne
    have hwb : τ w ≠ s.b := fun h =>
      hne (trans_injOn v s.p hw hwo (h.trans hτ₀.symm))
    have hslope : τ w - s.b = (w - w₀) * dslope τ w₀ w := by
      rw [← hτ₀, ← smul_eq_mul, sub_smul_dslope]
    have hw2' : (chartAt ℂ v).symm w ∈ (chartAt ℂ s.p).source := hw.2
    rw [hord, rd_apply, E, if_pos hw2']
    change Ep s (τ w) = _
    rw [Ep_eq_ratio s hw1 hw2 hwb, hslope, zpow_one]
    simp only [K]
    have : τ w - s.a ≠ 0 := sub_ne_zero.mpr hw2
    field_simp
  · -- neither end point: `E` is smooth and non-vanishing near `v`
    have hord : ord s v = 0 := by unfold ord; rw [if_neg hvt, if_neg hvs]; norm_num
    have hW : IsOpen ((chartAt ℂ v).target ∩ (chartAt ℂ v).symm ⁻¹' {s.start, s.stop}ᶜ) :=
      (chartAt ℂ v).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ v).open_target
        (Set.Finite.isClosed (by simp)).isOpen_compl
    have hw₀W : w₀ ∈ (chartAt ℂ v).target ∩ (chartAt ℂ v).symm ⁻¹' {s.start, s.stop}ᶜ := by
      refine ⟨hw₀, ?_⟩
      simp only [mem_preimage, hsv, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hvs, hvt⟩
    refine ⟨rd (E s) v, ?_, ?_, Eventually.of_forall fun w => by rw [hord, zpow_zero, one_mul]⟩
    · filter_upwards [hW.mem_nhds hw₀W] with w hw
      obtain ⟨hw1, hw2⟩ := hw
      have h3 : (chartAt ℂ v).symm w ≠ s.start ∧ (chartAt ℂ v).symm w ≠ s.stop := by
        simpa [not_or] using hw2
      exact (E_local s hw1 h3.1 h3.2).1
    · exact E_ne_zero s _

end Seg

end Seg

end JacobianChallenge.Surface
