import Jacobian.Surface.Hodge

/-!
# Hodge decomposition, part 2: the residue is `ν̄`

`E` is the closure in `A.L2` of `{∂̄u : u smooth}`. For a smooth `(0,1)`-form `θ`, the residue
`r = θ - P_E θ` of the orthogonal projection is `ν̄` for a holomorphic 1-form `ν`
(`exists_holo_residue`), so `θ - ν̄ ∈ E`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

theorem dbar_const_mul {f : ℂ → ℂ} {z : ℂ} (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    dbar (fun w => c * f w) z = c * dbar f z := by
  unfold dbar
  rw [fderiv_const_mul hf]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Smooth functions, as a submodule. -/
def smoothSub : Submodule ℂ (X → ℂ) where
  carrier := {u | IsSmooth u}
  add_mem' hu hv := IsSmooth.add hu hv
  zero_mem' := isSmooth_const (X := X) 0
  smul_mem' c _ hu := IsSmooth.smul hu c

/-- `‖g‖² = ∫ ‖g‖²` in `L²`. -/
theorem Lp_integral_norm_sq {μ : Measure ℂ} (g : Lp ℂ 2 μ) :
    ∫ z, ‖g z‖ ^ 2 ∂μ = ‖g‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def]
  have hi := L2.integrable_inner (𝕜 := ℂ) g g
  calc ∫ z, ‖g z‖ ^ 2 ∂μ = ∫ z, RCLike.re ⟪g z, g z⟫_ℂ ∂μ := by
        congr 1; funext z
        exact (inner_self_eq_norm_sq (𝕜 := ℂ) (g z)).symm
    _ = RCLike.re (∫ z, ⟪g z, g z⟫_ℂ ∂μ) := integral_re hi

/-- `L¹` is controlled by `L²` on a finite measure space. -/
theorem Lp_integral_norm_le {μ : Measure ℂ} [IsFiniteMeasure μ] (g : Lp ℂ 2 μ) {ε : ℝ}
    (hε : 0 < ε) : ∫ z, ‖g z‖ ∂μ ≤ ε / 2 * μ.real univ + ‖g‖ ^ 2 / (2 * ε) := by
  have hm : MemLp (g : ℂ → ℂ) 2 μ := Lp.memLp g
  have hi2 : Integrable (fun z => ‖g z‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp hm
  have hi1 : Integrable (fun z => ‖g z‖) μ := (hm.integrable one_le_two).norm
  calc ∫ z, ‖g z‖ ∂μ ≤ ∫ z, (ε / 2 + ‖g z‖ ^ 2 / (2 * ε)) ∂μ :=
        integral_mono hi1 ((integrable_const _).add (hi2.div_const _))
          fun z => le_half_add_sq_div hε
    _ = _ := by
        rw [integral_add (integrable_const _) (hi2.div_const _), integral_const, integral_div,
          Lp_integral_norm_sq, smul_eq_mul, mul_comm]

/-- `L²` convergence implies `L¹` convergence on a finite measure space. -/
theorem Lp_tendsto_integral_norm {μ : Measure ℂ} [IsFiniteMeasure μ] {g : ℕ → Lp ℂ 2 μ}
    (hg : Tendsto (fun n => ‖g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ‖g n z‖ ∂μ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set V := μ.real univ + 1
  have hV : 0 < V := by positivity
  set ε := δ / (2 * V)
  have hε : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hg (Real.sqrt (ε * δ / 2)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := Lp_integral_norm_le (g n) hε
  have h2 : ‖g n‖ ^ 2 < ε * δ / 2 := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    calc ‖g n‖ ^ 2 < Real.sqrt (ε * δ / 2) ^ 2 := by gcongr
      _ = ε * δ / 2 := Real.sq_sqrt (by positivity)
  have h0 : 0 ≤ ∫ z, ‖g n z‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have hvol : μ.real univ ≤ V := by linarith
  calc ∫ z, ‖g n z‖ ∂μ ≤ ε / 2 * μ.real univ + ‖g n‖ ^ 2 / (2 * ε) := h1
    _ ≤ ε / 2 * V + (ε * δ / 2) / (2 * ε) := by gcongr
    _ < δ := by
        have : ε / 2 * V = δ / 4 := by simp only [ε]; field_simp; ring
        rw [this, show ε * δ / 2 / (2 * ε) = δ / 4 by field_simp; ring]
        linarith

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem toL2_congr_target {θ β : X → ℂ → ℂ} (hθ : ContFam θ) (hβ : ContFam β)
    (h : ∀ i : Fin A.N, ∀ w ∈ (chartAt ℂ (A.p i)).target, θ (A.p i) w = β (A.p i) w) :
    A.toL2 θ hθ = A.toL2 β hβ := by
  refine PiLp.ext fun i => ?_
  rw [toL2_apply, toL2_apply]
  refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
  rw [EventuallyEq, ae_restrict_iff' (A.measurableSet_S i)]
  exact ae_of_all _ fun w hw => h i w
    ((A.S_subset_closedBall i).trans (A.closedBall_subset_target i) hw)

/-- `u ↦ ∂̄u`, into `L²`. -/
noncomputable def dbarL : smoothSub (X := X) →ₗ[ℂ] A.L2 where
  toFun u := A.toL2 (dbarF u.1) (smoothFam_dbarF u.2).contFam
  map_add' u v := by
    rw [← A.toL2_add]
    refine A.toL2_congr_target _ _ fun i w hw => ?_
    simp only [dbarF, Pi.add_apply]
    exact dbar_add (u.2.differentiableAt hw) (v.2.differentiableAt hw)
  map_smul' c u := by
    simp only [RingHom.id_apply]
    have hc : ContFam (c • dbarF u.1) := ((smoothFam_dbarF u.2).smul c).contFam
    have e1 : A.toL2 (dbarF (c • u).1) (smoothFam_dbarF (c • u).2).contFam = A.toL2 _ hc :=
      A.toL2_congr_target _ _ fun i w hw => by
        simp only [dbarF, Pi.smul_apply, smul_eq_mul]
        exact dbar_const_mul c (u.2.differentiableAt hw)
    rw [e1]
    refine PiLp.ext fun i => ?_
    rw [PiLp.smul_apply, toL2_apply, toL2_apply]
    exact MemLp.toLp_const_smul c (A.memLp_S i ((smoothFam_dbarF u.2).contFam (A.p i)))

/-- The closure of `{∂̄u}`. -/
noncomputable def E : Submodule ℂ A.L2 := (LinearMap.range A.dbarL).topologicalClosure

theorem dbarL_mem_E {u : X → ℂ} (hu : IsSmooth u) :
    A.toL2 (dbarF u) (smoothFam_dbarF hu).contFam ∈ A.E :=
  Submodule.le_topologicalClosure _ ⟨⟨u, hu⟩, rfl⟩

instance : CompleteSpace A.E :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem U_subset_ball (k : Fin A.N) {x : X} (hx : x ∈ (chartAt ℂ (A.p k)).source)
    (hb : chartAt ℂ (A.p k) x ∈ ball (A.ctr k) (A.r k)) :
    chartAt ℂ (A.p k) x ∈ ball (A.ctr k) (3 / 2 * A.r k) :=
  ball_subset_ball (by linarith [A.r_pos k]) hb

theorem S_subset_ball' (i : Fin A.N) : A.S i ⊆ ball (A.ctr i) (3 / 2 * A.r i) :=
  (A.S_subset_ball i).trans (ball_subset_ball (by linarith [A.r_pos i]))

/-- **The residue of the projection is `ν̄`.** For a smooth `(0,1)`-form `θ` there is a
holomorphic 1-form `ν` with `θ - ν̄ ∈ E`. -/
theorem exists_holo_residue {θ : X → ℂ → ℂ} (hθ : Is01 θ) (hθs : SmoothFam θ) :
    ∃ ν : HolomorphicOneForm ℂ X, ∃ h : ContFam (θ - conjF (holoF ν)),
      A.toL2 (θ - conjF (holoF ν)) h ∈ A.E := by
  set x := A.toL2 θ hθs.contFam
  set e := A.E.starProjection x
  set r := x - e with hrdef
  have hr : r ∈ A.Eᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have he : e ∈ A.E := Submodule.starProjection_apply_mem _ x
  have he' : e ∈ closure (LinearMap.range A.dbarL : Set A.L2) := by
    rw [← Submodule.topologicalClosure_coe]; exact he
  obtain ⟨s, hsmem, hslim⟩ := mem_closure_iff_seq_limit.mp he'
  choose u hu using hsmem
  set β : ℕ → X → ℂ → ℂ := fun n => θ - dbarF (u n).1 with hβdef
  have hβ : ∀ n, Is01 (β n) := fun n => hθ.sub (dbarF_is01 (u n).2)
  have hβs : ∀ n, SmoothFam (β n) := fun n => hθs.sub (smoothFam_dbarF (u n).2)
  have hβc : ∀ n, ContFam (β n) := fun n => (hβs n).contFam
  have hβL : ∀ n, A.toL2 (β n) (hβc n) = x - s n := by
    intro n
    rw [show A.toL2 (β n) (hβc n) = A.toL2 (θ - dbarF (u n).1)
      (hθs.contFam.sub (smoothFam_dbarF (u n).2).contFam) from rfl,
      A.toL2_sub hθs.contFam (smoothFam_dbarF (u n).2).contFam, ← hu n]
    rfl
  have hlim : Tendsto (fun n => A.toL2 (β n) (hβc n)) atTop (𝓝 r) := by
    simp_rw [hβL]; exact tendsto_const_nhds.sub hslim
  have horth : ∀ v (hv : IsSmooth v), ⟪A.toL2 (dbarF v) (smoothFam_dbarF hv).contFam, r⟫_ℂ = 0 :=
    fun v hv => Submodule.inner_right_of_mem_orthogonal (A.dbarL_mem_E hv) hr
  have hd : ∀ n m, IsDensity (fun p w => (starRingEnd ℂ) ((β n - β m) p w) * (β n - β m) p w) :=
    fun n m => isDensity_conj_mul_01 ((hβ n).sub (hβ m)) ((hβ n).sub (hβ m))
  have hR : ∀ k, ∃ R : ℂ → ℂ, IntegrableOn R (A.D k) ∧ L1Conv (fun n => β n (A.p k)) R (A.D k) :=
    fun k => A.exists_chartLimit k hβc hd hlim.cauchySeq
  choose R hRi hRc using hR
  have hG := fun k => A.residue_antiholomorphic k hβ hβc hlim (hRi k) (hRc k) horth
  choose G hGd hGae using hG
  have hβi : ∀ k n, IntegrableOn (β n (A.p k)) (A.D k) := fun k n =>
    ((hβc n (A.p k)).mono (A.D_subset_target k)).integrableOn_compact (isCompact_closedBall _ _)
  have hintk : ∀ k n, IntegrableOn (fun z => ‖β n (A.p k) z - (starRingEnd ℂ) (G k z)‖)
      (ball (A.ctr k) (3 / 2 * A.r k)) := by
    intro k n
    have h0 : IntegrableOn (fun z => ‖β n (A.p k) z - R k z‖) (A.D k) :=
      ((hβi k n).sub (hRi k)).norm
    refine (h0.mono_set (A.ball_subset_D k)).congr_fun_ae ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hGae k] with z hz hzb
    rw [hz hzb]
  have hconvk : ∀ k, L1Conv (fun n => β n (A.p k)) (fun z => (starRingEnd ℂ) (G k z))
      (ball (A.ctr k) (3 / 2 * A.r k)) := fun k =>
    (L1Conv.mono' (A.ball_subset_D k) (fun n => (((hβi k n).sub (hRi k)).norm :
      IntegrableOn (fun z => ‖β n (A.p k) z - R k z‖) (A.D k) volume)) (hRc k)).congr
      measurableSet_ball (fun _ _ _ => rfl) (hGae k)
  obtain ⟨ν, hν⟩ := exists_holoForm_of_local A.p (fun k => ball (A.ctr k) (3 / 2 * A.r k))
    (fun _ => isOpen_ball) (fun k => (A.ball_subset_D k).trans (A.D_subset_target k))
    (fun y => by
      obtain ⟨k, hk1, hk2⟩ := A.cover y
      exact ⟨k, hk1, A.U_subset_ball k hk1 hk2⟩)
    G hGd (fun k l w hw hwo hwl => A.chart_compat k l hβ hβc (hGd k) (hGd l) (hintk k)
      (hintk l) (hconvk k) (hconvk l) hw hwo hwl)
  have hνc : ContFam (conjF (holoF ν)) := (smoothFam_holoF ν).conjF.contFam
  -- identify the residue
  have hrν : r = A.toL2 (conjF (holoF ν)) hνc := by
    refine PiLp.ext fun i => ?_
    rw [toL2_apply]
    symm
    refine (Lp.ext ?_)
    have hS := A.measurableSet_S i
    -- `L¹` convergence of the readings to `r i` on `S i`
    have hc1 : Tendsto (fun n => ‖A.toL2 (β n) (hβc n) i - r i‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
        ((tendsto_iff_norm_sub_tendsto_zero.mp hlim))
      rw [← PiLp.sub_apply]
      exact PiLp.norm_apply_le _ i
    have hL1 := Lp_tendsto_integral_norm hc1
    have hconvr : L1Conv (fun n => β n (A.p i)) (r i) (A.S i) := by
      refine hL1.congr fun n => integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (A.toL2 (β n) (hβc n) i) (r i),
        (A.memLp_S i (hβc n (A.p i))).coeFn_toLp] with z h1 h2
      rw [h1, Pi.sub_apply, toL2_apply, h2]
    have hconvG : L1Conv (fun n => β n (A.p i)) (fun z => (starRingEnd ℂ) (G i z)) (A.S i) :=
      L1Conv.mono' (A.S_subset_ball' i) (hintk i) (hconvk i)
    have hβiS : ∀ n, IntegrableOn (β n (A.p i)) (A.S i) := fun n =>
      (hβi i n).mono_set ((A.S_subset_ball' i).trans (A.ball_subset_D i))
    have hrint : IntegrableOn (r i) (A.S i) :=
      (Lp.memLp (r i)).integrable one_le_two
    have hGint : IntegrableOn (fun z => (starRingEnd ℂ) (G i z)) (A.S i) := by
      have hcb : closedBall (A.ctr i) (A.r i) ⊆ ball (A.ctr i) (3 / 2 * A.r i) :=
        closedBall_subset_ball (by linarith [A.r_pos i])
      exact ((Complex.continuous_conj.comp_continuousOn ((hGd i).continuousOn.mono hcb)).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set (A.S_subset_closedBall i)
    have hae := L1Conv.ae_eq hβiS hrint hGint hconvr hconvG
    filter_upwards [hae, (A.memLp_S i (hνc (A.p i))).coeFn_toLp, ae_restrict_mem hS]
      with z h1 h2 hz
    rw [h2, h1]
    simp only [conjF, holoF]
    rw [hν i z (A.S_subset_ball' i hz)]
  refine ⟨ν, hθs.contFam.sub hνc, ?_⟩
  rw [A.toL2_sub hθs.contFam hνc, ← hrν, hrdef, sub_sub_cancel]
  exact he

end DiscAtlas


end JacobianChallenge.Surface
