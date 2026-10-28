import Jacobian.Surface.SegmentFn

/-!
# Pairing `(0,1)`-forms with holomorphic forms; `∂̄`-solvability

* `DiscAtlas.exists_extend`: a disc atlas containing any finitely many prescribed chart centres.
* `Seg.integral_θ_mul`: `∫_X θ_s ∧ η = π ∫_s η` for the `(0,1)`-form of a chart segment
  (Cauchy–Pompeiu along the segment).
* `eq_zero_of_integral_conj_mul_self`: the `L²` pairing is definite on holomorphic forms.
* `dbar_solvable_of_orthogonal`: a smooth `(0,1)`-form pairing to zero with every holomorphic
  1-form is `∂̄`-exact (Hodge decomposition).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

/-! ### Atlases with prescribed centres -/

theorem exists_disc_radius (x : X) :
    ∃ r : ℝ, 0 < r ∧ closedBall (chartAt ℂ x x) (3 * r) ⊆ (chartAt ℂ x).target := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ (mem_chart_target ℂ x)
  exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩

/-- Adjoin finitely many chart discs to a disc atlas. -/
noncomputable def DiscAtlas.extend (A : DiscAtlas X) {m : ℕ} (e : Fin m → X) : DiscAtlas X where
  N := A.N + m
  p := Fin.append A.p e
  r := Fin.append A.r fun i => (exists_disc_radius (e i)).choose
  r_pos := fun i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact A.r_pos j
    · rw [Fin.append_right]; exact (exists_disc_radius (e j)).choose_spec.1
  ball_subset := fun i => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left]; exact A.ball_subset j
    · rw [Fin.append_right, Fin.append_right]; exact (exists_disc_radius (e j)).choose_spec.2
  cover := fun y => by
    obtain ⟨i, h1, h2⟩ := A.cover y
    exact ⟨Fin.castAdd m i, by rw [Fin.append_left]; exact h1, by
      rw [Fin.append_left, Fin.append_left]; exact h2⟩

theorem DiscAtlas.extend_p (A : DiscAtlas X) {m : ℕ} (e : Fin m → X) (i : Fin m) :
    (A.extend e).p (Fin.natAdd A.N i) = e i := by
  show Fin.append A.p e (Fin.natAdd A.N i) = e i
  rw [Fin.append_right]

/-! ### The pairing of a segment form with a holomorphic form -/

namespace Seg

variable (s : ChartSegment X)

theorem tsupport_cutC_subset : tsupport (cutC (bump s)) ⊆ closedBall s.center (bump s).rOut := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra h
  exact hz (cutC_eq_zero _ fun h' => h (ball_subset_closedBall h'))

theorem cutC_segPt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : cutC (bump s) (segPt s.a s.b t) = 1 :=
  cutC_eq_one _ (closedBall_subset_rIn s (segment_subset_closedBall s (segPt_mem_segment _ _ ht)))

/-- The segment integral of a holomorphic form, as an integral of its chart coefficient. -/
theorem integral_eq (η : HolomorphicOneForm ℂ X) :
    s.integral η = (s.b - s.a) * ∫ t in (0 : ℝ)..1, chartCoeff s.p η (segPt s.a s.b t) := by
  rw [ChartSegment.integral, curveIntegral_segment, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [clm_apply_eq_mul']
  have : AffineMap.lineMap s.a s.b t = segPt s.a s.b t := by
    rw [AffineMap.lineMap_apply_module', segPt, Complex.real_smul]; ring
  rw [this]
  rfl

/-- **The pairing.** `∫_X θ_s · η = π ∫_s η`. -/
theorem integral_θ_mul (A : DiscAtlas X) (k : Fin A.N) (hk : A.p k = s.p)
    (η : HolomorphicOneForm ℂ X) :
    A.integral (fun q w => θ s q w * holoF η q w) = (Real.pi : ℂ) * s.integral η := by
  set h := chartCoeff s.p η
  have hdens : DiscAtlas.IsDensity (fun q w => θ s q w * holoF η q w) :=
    isDensity_mul (θ_is01 s) (holoF_is10 η)
  have hK := closedBall_rOut_subset_target s
  have hhd : DifferentiableOn ℂ h (chartAt ℂ s.p).target := chartCoeff_differentiableOn s.p η
  -- localize to the chart at `s.p`
  have h0 : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target,
      (chartAt ℂ q).symm w ∉ (chartAt ℂ (A.p k)).source → θ s q w * holoF η q w = 0 := by
    intro q w _ hw
    rw [hk] at hw
    simp [θ, ext01, if_neg hw]
  have hcont : ContinuousOn (fun w => ψ s w * h w) (chartAt ℂ s.p).target :=
    (contDiff_ψ s).continuous.continuousOn.mul hhd.continuousOn
  have hint : IntegrableOn (fun w => θ s (A.p k) w * holoF η (A.p k) w)
      (chartAt ℂ (A.p k)).target := by
    rw [hk]
    have hψi : IntegrableOn (fun w => ψ s w * h w) (chartAt ℂ s.p).target := by
      refine ((hcont.mono hK).integrableOn_compact (μ := volume)
        (isCompact_closedBall _ _)).of_forall_diff_eq_zero
        (chartAt ℂ s.p).open_target.measurableSet fun w ⟨_, hwb⟩ => ?_
      rw [image_eq_zero_of_notMem_tsupport fun h' => hwb (tsupport_ψ s h'), zero_mul]
    refine hψi.congr_fun (fun w hw => ?_) (chartAt ℂ s.p).open_target.measurableSet
    simp only [θ, holoF]
    rw [ext01_self hw]
  rw [DiscAtlas.integral_density_eq_chart A hdens k h0 hint, hk]
  -- reduce to a plane integral of `∂̄(χ h) · Log`
  set φ : ℂ → ℂ := fun z => cutC (bump s) z * h z
  have hφ : ContDiff ℝ ∞ φ := contDiff_mul_of_tsupport_subset (chartAt ℂ s.p).open_target
    (contDiff_cutC _) (hhd.contDiffOn (chartAt ℂ s.p).open_target |>.restrict_scalars ℝ)
    ((tsupport_cutC_subset s).trans hK)
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall s.center (bump s).rOut) fun z hz => by
      simp [φ, cutC_eq_zero _ fun h' => hz (ball_subset_closedBall h')]
  have hpt : ∀ w, (chartAt ℂ s.p).target.indicator (fun w => θ s s.p w * holoF η s.p w) w =
      dbar φ w * L s w := by
    intro w
    by_cases hw : w ∈ (chartAt ℂ s.p).target
    · rw [indicator_of_mem hw]
      simp only [θ, holoF]
      rw [ext01_self hw]
      have hdh : DifferentiableAt ℂ h w :=
        hhd.differentiableAt ((chartAt ℂ s.p).open_target.mem_nhds hw)
      rw [show dbar φ w = cutC (bump s) w * dbar h w + h w * dbar (cutC (bump s)) w from
        dbar_mul ((contDiff_cutC _).differentiable (by simp) w) (hdh.restrictScalars ℝ),
        dbar_eq_zero_of_differentiableAt hdh, ψ]
      ring
    · rw [indicator_of_notMem hw]
      have hwK : w ∉ closedBall s.center (bump s).rOut := fun h' => hw (hK h')
      have : dbar φ w = 0 := by
        refine dbar_eq_zero_of_eventuallyEq (c := 0) ?_
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hwK] with v hv
        simp [φ, cutC_eq_zero _ fun h' => hv (ball_subset_closedBall h')]
      rw [this, zero_mul]
  have e1 : ∫ w in (chartAt ℂ s.p).target, θ s s.p w * holoF η s.p w =
      ∫ w, dbar φ w * L s w := by
    rw [← integral_indicator (chartAt ℂ s.p).open_target.measurableSet]
    exact integral_congr_ae (ae_of_all _ hpt)
  rw [e1, show (fun w => dbar φ w * L s w) = fun w => dbar φ w *
      Complex.log ((w - s.b) / (w - s.a)) from rfl,
    integral_dbar_mul_log (hφ.of_le (by simp)) hφs, integral_eq]
  have e2 : ∫ t in (0 : ℝ)..1, φ (segPt s.a s.b t) =
      ∫ t in (0 : ℝ)..1, h (segPt s.a s.b t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [φ, cutC_segPt s ht, one_mul]
  rw [e2]
  ring

end Seg

/-! ### Definiteness and `∂̄`-solvability -/

theorem DiscAtlas.integral_add' (A : DiscAtlas X) {σ τ : X → ℂ → ℂ}
    (hσ : ∀ q, ContinuousOn (σ q) (chartAt ℂ q).target)
    (hτ : ∀ q, ContinuousOn (τ q) (chartAt ℂ q).target) :
    A.integral (fun q w => σ q w + τ q w) = A.integral σ + A.integral τ := by
  unfold DiscAtlas.integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hS := (A.S_subset_closedBall i)
  have hK := A.closedBall_subset_target i
  exact MeasureTheory.integral_add
    ((((hσ _).mono hK).integrableOn_compact (isCompact_closedBall _ _)).mono_set hS)
    ((((hτ _).mono hK).integrableOn_compact (isCompact_closedBall _ _)).mono_set hS)

/-- The `L²` pairing is definite on holomorphic 1-forms. -/
theorem eq_zero_of_integral_conj_mul_self (A : DiscAtlas X) (ν : HolomorphicOneForm ℂ X)
    (h : A.integral (fun p w => (starRingEnd ℂ) (holoF ν p w) * holoF ν p w) = 0) : ν = 0 := by
  have hc : ContFam (holoF ν) := (smoothFam_holoF ν).contFam
  have hn : ‖A.toL2 (holoF ν) hc‖ ^ 2 = 0 := by rw [A.norm_toL2_sq hc, h, Complex.zero_re]
  refine holomorphicOneForm_eq_zero_of_chartCoeff ν fun y => ?_
  obtain ⟨k, hys, hyb⟩ := A.cover y
  refine ⟨A.p k, hys, ?_⟩
  have hle := A.integral_sq_le_norm_toL2 k (isDensity_conj_mul_10 (holoF_is10 ν) (holoF_is10 ν)) hc
  rw [hn] at hle
  have hK : closedBall (A.ctr k) (3 / 2 * A.r k) ⊆ (chartAt ℂ (A.p k)).target :=
    A.ball_subset_target k (by norm_num)
  have hcont : ContinuousOn (fun w => ‖holoF ν (A.p k) w‖ ^ 2) (closedBall (A.ctr k) (3 / 2 * A.r k)) :=
    ((hc (A.p k)).mono hK).norm.pow 2
  have hint := hcont.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)
  have hzero : ∫ w in closedBall (A.ctr k) (3 / 2 * A.r k), ‖holoF ν (A.p k) w‖ ^ 2 = 0 :=
    le_antisymm hle (setIntegral_nonneg measurableSet_closedBall fun _ _ => by positivity)
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => by positivity) hint).mp
    hzero
  have hae' : (fun w => ‖holoF ν (A.p k) w‖ ^ 2) =ᵐ[volume.restrict (ball (A.ctr k) (3 / 2 * A.r k))]
      fun _ => 0 := ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_ball
    (hcont.mono ball_subset_closedBall) continuousOn_const
  have hyb' : chartAt ℂ (A.p k) y ∈ ball (A.ctr k) (3 / 2 * A.r k) :=
    ball_subset_ball (by nlinarith [A.r_pos k]) hyb
  have := heq hyb'
  simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
  exact this

/-- `∫ ∂̄u · η = 0` for `u` smooth and `η` holomorphic (Stokes). -/
theorem integral_dbar_mul_holo (A : DiscAtlas X) {u : X → ℂ} (hu : IsSmooth u)
    (η : HolomorphicOneForm ℂ X) :
    A.integral (fun q w => dbar (rd u q) w * holoF η q w) = 0 := by
  rw [← A.integral_dbarFam_eq_zero ((holoF_is10 η).smulF u) ((smoothFam_holoF η).smulF hu)]
  refine A.integral_congr fun i w hw => ?_
  have hdh : DifferentiableAt ℂ (chartCoeff (A.p i) η) w :=
    (chartCoeff_differentiableOn (A.p i) η).differentiableAt
      ((chartAt ℂ (A.p i)).open_target.mem_nhds hw)
  show _ = dbar (fun v => rd u (A.p i) v * chartCoeff (A.p i) η v) w
  rw [dbar_mul (hu.differentiableAt hw) (hdh.restrictScalars ℝ),
    dbar_eq_zero_of_differentiableAt hdh]
  simp only [holoF]
  ring

/-- **`∂̄`-solvability.** A smooth `(0,1)`-form orthogonal to every holomorphic 1-form is `∂̄u`. -/
theorem dbar_solvable_of_orthogonal [CompactSpace X] [ConnectedSpace X] (A : DiscAtlas X)
    {θ : X → ℂ → ℂ} (hθ : Is01 θ) (hθs : SmoothFam θ)
    (horth : ∀ η : HolomorphicOneForm ℂ X, A.integral (fun q w => θ q w * holoF η q w) = 0) :
    ∃ u : X → ℂ, IsSmooth u ∧ ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, θ q w = dbar (rd u q) w := by
  obtain ⟨u, hu, ν, hν⟩ := hodge_decomp hθ hθs
  suffices hν0 : ν = 0 by
    refine ⟨u, hu, fun q w hw => ?_⟩
    rw [hν q w hw, hν0, chartCoeff_zero, map_zero, add_zero]
  apply eq_zero_of_integral_conj_mul_self A ν
  have h1 := horth ν
  have hsplit : A.integral (fun q w => θ q w * holoF ν q w) =
      A.integral (fun q w => dbar (rd u q) w * holoF ν q w) +
        A.integral (fun p w => (starRingEnd ℂ) (holoF ν p w) * holoF ν p w) := by
    have hc1 : ∀ q, ContinuousOn (fun w => dbar (rd u q) w * holoF ν q w) (chartAt ℂ q).target :=
      fun q => ((contDiffOn_dbar (chartAt ℂ q).open_target (hu q)).continuousOn).mul
        ((smoothFam_holoF ν q).continuousOn)
    have hc2 : ∀ q, ContinuousOn (fun w => (starRingEnd ℂ) (holoF ν q w) * holoF ν q w)
        (chartAt ℂ q).target := fun q =>
      (Complex.continuous_conj.comp_continuousOn (smoothFam_holoF ν q).continuousOn).mul
        (smoothFam_holoF ν q).continuousOn
    rw [← A.integral_add' hc1 hc2]
    refine A.integral_congr fun i w hw => ?_
    rw [hν (A.p i) w hw]
    simp only [holoF]
    ring
  rw [hsplit, integral_dbar_mul_holo A hu ν, zero_add] at h1
  exact h1

end JacobianChallenge.Surface
