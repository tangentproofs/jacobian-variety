import Jacobian.Surface.L2

/-!
# Hodge decomposition of `(0,1)`-forms, part 1: the residue is antiholomorphic

Set-up for `hodge_decomp` (every smooth `(0,1)`-form is `∂̄u + ν̄` with `ν` holomorphic).

* `exists_chartLimit`: an `L²`-Cauchy sequence of continuous forms has chart readings converging
  in `L¹` of the disc of radius `(3/2) r_k`.
* `inner_dbarF_extend`: pairing with `∂̄` of a test function supported in a chart is a plane
  integral.
* `residue_antiholomorphic`: a limit of forms orthogonal to all `∂̄u` reads, in each chart, as the
  conjugate of a holomorphic function.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

/-- `t ≤ ε/2 + t²/(2ε)`. -/
theorem le_half_add_sq_div {t ε : ℝ} (hε : 0 < ε) : t ≤ ε / 2 + t ^ 2 / (2 * ε) := by
  rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t - ε)]

theorem _root_.JacobianChallenge.Analysis.L1Conv.mono' {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    {K K' : Set ℂ} (hK' : K' ⊆ K) (hint : ∀ n, IntegrableOn (fun z => ‖f n z - F z‖) K)
    (h : L1Conv f F K) : L1Conv f F K' := by
  refine squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) h
  exact setIntegral_mono_set (hint n) (ae_of_all _ fun _ => norm_nonneg _)
    (Eventually.of_forall hK')

/-- Change of variables for real integrands under a holomorphic map. -/
theorem integral_image_holo_real {τ : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hτ : ∀ w ∈ s, DifferentiableAt ℂ τ w) (hinj : InjOn τ s) (g : ℂ → ℝ) :
    ∫ v in τ '' s, g v = ∫ w in s, ‖deriv τ w‖ ^ 2 * g (τ w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw => ((hτ w hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  congr 1; funext w
  rw [det_restrictScalars_fderiv, abs_of_nonneg (by positivity), smul_eq_mul]

/-- `L¹` convergence transfers along a holomorphic injective map with nonvanishing derivative. -/
theorem _root_.JacobianChallenge.Analysis.L1Conv.comp_holo {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {τ : ℂ → ℂ} {B K : Set ℂ}
    (hB : IsCompact B) (hBm : MeasurableSet B) (hτd : ∀ w ∈ B, DifferentiableAt ℂ τ w)
    (hτc : ContinuousOn (deriv τ) B) (hinj : InjOn τ B) (hd : ∀ w ∈ B, deriv τ w ≠ 0)
    (hτB : τ '' B ⊆ K) (hfc : ∀ n, ContinuousOn (fun w => f n (τ w) - F (τ w)) B)
    (hint : ∀ n, IntegrableOn (fun z => ‖f n z - F z‖) K) (h : L1Conv f F K) :
    L1Conv (fun n => f n ∘ τ) (F ∘ τ) B := by
  obtain ⟨c, hc, hcB⟩ : ∃ c > 0, ∀ w ∈ B, c ≤ ‖deriv τ w‖ ^ 2 := by
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · exact ⟨1, one_pos, by simp [hBe]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hB.exists_isMinOn hBne (hτc.norm.pow 2)
      exact ⟨‖deriv τ w₀‖ ^ 2, by have := hd w₀ hw₀; positivity, fun w hw => hmin hw⟩
  refine squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using h.const_mul c⁻¹)
  have hi1 : IntegrableOn (fun w => ‖f n (τ w) - F (τ w)‖) B :=
    (hfc n).norm.integrableOn_compact hB
  have hi2 : IntegrableOn (fun w => ‖deriv τ w‖ ^ 2 * ‖f n (τ w) - F (τ w)‖) B :=
    ((hτc.norm.pow 2).mul (hfc n).norm).integrableOn_compact hB
  calc ∫ w in B, ‖(f n ∘ τ) w - (F ∘ τ) w‖
      ≤ ∫ w in B, c⁻¹ * (‖deriv τ w‖ ^ 2 * ‖f n (τ w) - F (τ w)‖) := by
        refine setIntegral_mono_on hi1 (hi2.const_mul _) hBm fun w hw => ?_
        simp only [Function.comp_apply]
        rw [← mul_assoc]
        have : 1 ≤ c⁻¹ * ‖deriv τ w‖ ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact hcB w hw
        nlinarith [norm_nonneg (f n (τ w) - F (τ w))]
    _ = c⁻¹ * ∫ v in τ '' B, ‖f n v - F v‖ := by
        rw [integral_const_mul, integral_image_holo_real hBm hτd hinj]
    _ ≤ c⁻¹ * ∫ z in K, ‖f n z - F z‖ := by
        exact mul_le_mul_of_nonneg_left (setIntegral_mono_set (hint n)
          (ae_of_all _ fun _ => norm_nonneg _) (Eventually.of_forall hτB)) (inv_nonneg.mpr hc.le)

namespace DiscAtlas

variable (A : DiscAtlas X)

/-- The analysis disc of the chart `k`: radius `(3/2) r_k`. -/
abbrev D (k : Fin A.N) : Set ℂ := closedBall (A.ctr k) (3 / 2 * A.r k)

theorem D_subset_target (k : Fin A.N) : A.D k ⊆ (chartAt ℂ (A.p k)).target :=
  A.ball_subset_target k (by norm_num)

theorem volume_D_lt_top (k : Fin A.N) : volume (A.D k) < ⊤ := measure_closedBall_lt_top

/-- `L¹(D)` is controlled by `L²(D)`: `∫ ‖f‖ ≤ ε V/2 + ∫ ‖f‖²/(2ε)`. -/
theorem integral_norm_le_of_sq (k : Fin A.N) {f : ℂ → ℂ}
    (hf : ContinuousOn f (A.D k)) {ε : ℝ} (hε : 0 < ε) :
    ∫ z in A.D k, ‖f z‖ ≤ ε / 2 * volume.real (A.D k) +
      (∫ z in A.D k, ‖f z‖ ^ 2) / (2 * ε) := by
  have hi1 : IntegrableOn (fun z => ‖f z‖) (A.D k) :=
    hf.norm.integrableOn_compact (isCompact_closedBall _ _)
  have hi2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (A.D k) :=
    (hf.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)
  calc ∫ z in A.D k, ‖f z‖ ≤ ∫ z in A.D k, (ε / 2 + ‖f z‖ ^ 2 / (2 * ε)) :=
        setIntegral_mono_on hi1 ((continuous_const.continuousOn.integrableOn_compact
          (isCompact_closedBall _ _)).add (hi2.div_const _)) measurableSet_closedBall
          fun z _ => le_half_add_sq_div hε
    _ = _ := by
        rw [integral_add (continuous_const.continuousOn.integrableOn_compact
          (isCompact_closedBall _ _)) (hi2.div_const _),
          setIntegral_const, integral_div, smul_eq_mul, mul_comm]

/-- **Chart limits.** An `L²`-Cauchy sequence of continuous forms (whose self-pairings are
densities) has chart readings converging in `L¹(D_k)`. -/
theorem exists_chartLimit (k : Fin A.N) {a : ℕ → X → ℂ → ℂ} (hc : ∀ n, ContFam (a n))
    (hd : ∀ n m, IsDensity (fun p w => (starRingEnd ℂ) ((a n - a m) p w) * (a n - a m) p w))
    (hcs : CauchySeq fun n => A.toL2 (a n) (hc n)) :
    ∃ R : ℂ → ℂ, IntegrableOn R (A.D k) ∧ L1Conv (fun n => a n (A.p k)) R (A.D k) := by
  have hint : ∀ n, IntegrableOn (a n (A.p k)) (A.D k) := fun n =>
    ((hc n (A.p k)).mono (A.D_subset_target k)).integrableOn_compact (isCompact_closedBall _ _)
  refine exists_L1Conv hint fun δ hδ => ?_
  set V := volume.real (A.D k) + 1
  have hV : 0 < V := by positivity
  set ε := δ / (2 * V)
  have hε : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hcs (Real.sqrt (ε * δ)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdist := hN n hn m hm
  have hsq : ‖A.toL2 (a n - a m) ((hc n).sub (hc m))‖ ^ 2 < ε * δ := by
    rw [A.toL2_sub (hc n) (hc m), ← dist_eq_norm]
    calc dist _ _ ^ 2 < Real.sqrt (ε * δ) ^ 2 := by gcongr
      _ = ε * δ := Real.sq_sqrt (by positivity)
  have hloc := A.integral_sq_le_norm_toL2 k (hd n m) ((hc n).sub (hc m))
  have hcont : ContinuousOn (fun z => a n (A.p k) z - a m (A.p k) z) (A.D k) :=
    (((hc n).sub (hc m)) (A.p k)).mono (A.D_subset_target k)
  have h1 := A.integral_norm_le_of_sq k hcont hε
  have hvol : volume.real (A.D k) ≤ V := by linarith
  calc ∫ z in A.D k, ‖a n (A.p k) z - a m (A.p k) z‖
      ≤ ε / 2 * volume.real (A.D k) +
          (∫ z in A.D k, ‖a n (A.p k) z - a m (A.p k) z‖ ^ 2) / (2 * ε) := h1
    _ ≤ ε / 2 * V + ε * δ / (2 * ε) := by
        gcongr
        exact hloc.trans hsq.le
    _ < δ := by
        have : ε / 2 * V = δ / 4 := by simp only [ε]; field_simp; ring
        rw [this, show ε * δ / (2 * ε) = δ / 2 by field_simp]
        linarith

/-! ### Test functions supported in a chart -/

theorem tsupport_subset_two (k : Fin A.N) {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ ball (A.ctr k) (3 / 2 * A.r k)) :
    tsupport φ ⊆ closedBall (A.ctr k) (2 * A.r k) :=
  hs.trans (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith [A.r_pos k])))

theorem isSmooth_extend_test (k : Fin A.N) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ ball (A.ctr k) (3 / 2 * A.r k)) : IsSmooth (extend (A.p k) φ) :=
  isSmooth_extend hφ (isCompact_closedBall _ _) (A.ball_subset_target k (by norm_num))
    (A.tsupport_subset_two k hs)

theorem rd_extend_eventuallyEq_zero (k : Fin A.N) {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ ball (A.ctr k) (3 / 2 * A.r k)) {q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) (hx : (chartAt ℂ q).symm w ∉ A.pouSupp k) :
    rd (extend (A.p k) φ) q =ᶠ[𝓝 w] fun _ => 0 :=
  ((chartAt ℂ q).continuousAt_symm hw).preimage_mem_nhds
    (extend_eventuallyEq_zero (isCompact_closedBall _ _) (A.ball_subset_target k (by norm_num))
      (A.tsupport_subset_two k hs) hx)

/-- Pairing `∂̄` of a test function in the chart `k` with a `(0,1)`-form is a plane integral. -/
theorem inner_dbarF_extend (k : Fin A.N) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ ball (A.ctr k) (3 / 2 * A.r k)) {β : X → ℂ → ℂ} (hβ : Is01 β)
    (hβc : ContFam β) :
    ⟪A.toL2 (dbarF (extend (A.p k) φ))
        (smoothFam_dbarF (A.isSmooth_extend_test k hφ hs)).contFam, A.toL2 β hβc⟫_ℂ =
      ∫ w in A.D k, (starRingEnd ℂ) (dbar φ w) * β (A.p k) w := by
  have hu := A.isSmooth_extend_test k hφ hs
  rw [A.inner_toL2]
  have hc : ContinuousOn (fun w => (starRingEnd ℂ) (dbarF (extend (A.p k) φ) (A.p k) w) *
      β (A.p k) w) (chartAt ℂ (A.p k)).target :=
    (Complex.continuous_conj.comp_continuousOn ((smoothFam_dbarF hu).contFam _)).mul (hβc _)
  rw [A.integral_eq_chart_of_supp (isDensity_conj_mul_01 (dbarF_is01 hu) hβ) k
    (fun q w hw hx => by
      simp [dbarF, dbar_eq_zero_of_eventuallyEq (A.rd_extend_eventuallyEq_zero k hs hw hx)]) hc]
  have hDt := A.D_subset_target k
  rw [← setIntegral_eq_of_subset_of_forall_diff_eq_zero
    (chartAt ℂ (A.p k)).open_target.measurableSet hDt]
  · refine setIntegral_congr_fun (chartAt ℂ (A.p k)).open_target.measurableSet fun w hw => ?_
    simp only [dbarF]
    rw [dbar_congr (f := rd (extend (A.p k) φ) (A.p k)) (g := φ) (by
      filter_upwards [(chartAt ℂ (A.p k)).open_target.mem_nhds hw] with v hv
      exact rd_extend_self hv)]
  · intro w ⟨_, hwD⟩
    have hwφ : w ∉ tsupport φ := fun h => hwD (ball_subset_closedBall (hs h))
    rw [dbar_eq_zero_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hwφ)]
    simp

theorem continuous_dbar_of_contDiff {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) : Continuous (dbar φ) :=
  continuous_dbar (hφ.of_le (by simp))

theorem hasCompactSupport_dbar {φ : ℂ → ℂ} (hs : HasCompactSupport φ) :
    HasCompactSupport (dbar φ) :=
  HasCompactSupport.intro hs.isCompact fun z hz =>
    dbar_eq_zero_of_eventuallyEq (c := 0) (notMem_tsupport_iff_eventuallyEq.mp hz)

/-- The pairing of a limit with `∂̄` of a test function, computed from the chart limit. -/
theorem residue_pairing (k : Fin A.N) {β : ℕ → X → ℂ → ℂ} (hβ : ∀ n, Is01 (β n))
    (hβc : ∀ n, ContFam (β n)) {r : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (β n) (hβc n)) atTop (𝓝 r)) {R : ℂ → ℂ}
    (hRi : IntegrableOn R (A.D k)) (hR : L1Conv (fun n => β n (A.p k)) R (A.D k))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ ball (A.ctr k) (3 / 2 * A.r k)) :
    ∫ w in A.D k, (starRingEnd ℂ) (dbar φ w) * R w =
      ⟪A.toL2 (dbarF (extend (A.p k) φ))
        (smoothFam_dbarF (A.isSmooth_extend_test k hφ hs)).contFam, r⟫_ℂ := by
  have hint : ∀ n, IntegrableOn (β n (A.p k)) (A.D k) := fun n =>
    ((hβc n (A.p k)).mono (A.D_subset_target k)).integrableOn_compact (isCompact_closedBall _ _)
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall (A.ctr k) (3 / 2 * A.r k))
      fun _ hz => image_eq_zero_of_notMem_tsupport fun h => hz (ball_subset_closedBall (hs h))
  have hgc : Continuous fun w => (starRingEnd ℂ) (dbar φ w) :=
    Complex.continuous_conj.comp (continuous_dbar_of_contDiff hφ)
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support
    ((hasCompactSupport_dbar hφs).comp_left (map_zero _))
  have h1 := hR.tendsto_integral_mul hint hRi hgc.aestronglyMeasurable hC
  have h2 : Tendsto (fun n => ⟪A.toL2 (dbarF (extend (A.p k) φ))
      (smoothFam_dbarF (A.isSmooth_extend_test k hφ hs)).contFam, A.toL2 (β n) (hβc n)⟫_ℂ)
      atTop (𝓝 ⟪A.toL2 (dbarF (extend (A.p k) φ))
        (smoothFam_dbarF (A.isSmooth_extend_test k hφ hs)).contFam, r⟫_ℂ) :=
    tendsto_const_nhds.inner hlim
  simp_rw [A.inner_dbarF_extend k hφ hs (hβ _) (hβc _)] at h2
  simp_rw [mul_comm ((starRingEnd ℂ) (dbar φ _))] at h2 ⊢
  exact tendsto_nhds_unique h1 h2

theorem ball_subset_D (k : Fin A.N) : ball (A.ctr k) (3 / 2 * A.r k) ⊆ A.D k :=
  ball_subset_closedBall

/-- A sub-ball around a point of an open ball. -/
theorem exists_ball_subset_ball {c x : ℂ} {ρ : ℝ} (hx : x ∈ ball c ρ) :
    ∃ ε > 0, ball x ε ⊆ ball c ρ :=
  Metric.isOpen_iff.mp isOpen_ball x hx

/-- **The residue is antiholomorphic.** If a limit `r` of `(0,1)`-forms is orthogonal to every
`∂̄u`, then its chart reading is the conjugate of a holomorphic function. -/
theorem residue_antiholomorphic (k : Fin A.N) {β : ℕ → X → ℂ → ℂ} (hβ : ∀ n, Is01 (β n))
    (hβc : ∀ n, ContFam (β n)) {r : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (β n) (hβc n)) atTop (𝓝 r)) {R : ℂ → ℂ}
    (hRi : IntegrableOn R (A.D k)) (hR : L1Conv (fun n => β n (A.p k)) R (A.D k))
    (horth : ∀ u (hu : IsSmooth u), ⟪A.toL2 (dbarF u) (smoothFam_dbarF hu).contFam, r⟫_ℂ = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (A.ctr k) (3 / 2 * A.r k)) ∧
      ∀ᵐ w, w ∈ ball (A.ctr k) (3 / 2 * A.r k) → R w = (starRingEnd ℂ) (G w) := by
  set O := ball (A.ctr k) (3 / 2 * A.r k)
  set U : ℂ → ℂ := (A.D k).indicator fun w => (starRingEnd ℂ) (R w)
  have hRc : IntegrableOn (fun w => (starRingEnd ℂ) (R w)) (A.D k) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hRi
  have hUi : Integrable U := (integrable_indicator_iff measurableSet_closedBall).mpr hRc
  have hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ z, U z * dbar φ z = 0 := by
    intro φ hφ _ hs
    have e1 : (fun z => U z * dbar φ z) =
        (A.D k).indicator fun z => (starRingEnd ℂ) (R z) * dbar φ z := by
      funext z
      by_cases hz : z ∈ A.D k
      · simp [U, indicator_of_mem hz]
      · simp [U, indicator_of_notMem hz]
    rw [e1, integral_indicator measurableSet_closedBall]
    have e2 : ∫ z in A.D k, (starRingEnd ℂ) (R z) * dbar φ z =
        (starRingEnd ℂ) (∫ z in A.D k, (starRingEnd ℂ) (dbar φ z) * R z) := by
      rw [← integral_conj]
      congr 1; funext z
      simp [mul_comm]
    rw [e2, A.residue_pairing k hβ hβc hlim hRi hR hφ hs,
      horth _ (A.isSmooth_extend_test k hφ hs), map_zero]
  have hloc : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball x ρ) ∧ ContinuousOn g (ball x ρ) ∧
        ∀ᵐ z, z ∈ ball x ρ → U z = g z := by
    intro x hx
    obtain ⟨ρ₀, hρ₀, hsub⟩ := exists_ball_subset_ball hx
    obtain ⟨h, hh, hae⟩ := weyl_dbar_ball hρ₀ hUi.integrableOn
      fun φ hφ hφs hφt => hweak φ hφ hφs (hφt.trans hsub)
    refine ⟨ρ₀ / 4, by positivity, (ball_subset_ball (by linarith)).trans hsub, h, hh,
      hh.continuousOn, hae⟩
  obtain ⟨G, hGae, hGloc⟩ := exists_glue isOpen_ball
    (Q := fun g x ρ => DifferentiableOn ℂ g (ball x ρ)) fun x hx => by
      obtain ⟨ρ, hρ, hsub, g, hg, hgc, hae⟩ := hloc x hx
      exact ⟨ρ, hρ, hsub, g, hg, hgc, hae⟩
  refine ⟨G, fun x hx => ?_, ?_⟩
  · obtain ⟨ρ, hρ, -, g, hg, hEq⟩ := hGloc x hx
    have hev : G =ᶠ[𝓝 x] g := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy using hEq hy
    exact ((hg x (mem_ball_self hρ)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hρ))).congr_of_eventuallyEq hev |>.differentiableWithinAt
  · filter_upwards [hGae] with w hw hwO
    have := hw hwO
    simp only [U, indicator_of_mem (A.ball_subset_D k hwO)] at this
    rw [← this, Complex.conj_conj]

/-- **Compatibility across charts** of the antiholomorphic chart limits. -/
theorem chart_compat (k l : Fin A.N) {β : ℕ → X → ℂ → ℂ} (hβ : ∀ n, Is01 (β n))
    (hβc : ∀ n, ContFam (β n)) {Gk Gl : ℂ → ℂ}
    (hGk : DifferentiableOn ℂ Gk (ball (A.ctr k) (3 / 2 * A.r k)))
    (hGl : DifferentiableOn ℂ Gl (ball (A.ctr l) (3 / 2 * A.r l)))
    (hik : ∀ n, IntegrableOn (fun z => ‖β n (A.p k) z - (starRingEnd ℂ) (Gk z)‖)
      (ball (A.ctr k) (3 / 2 * A.r k)))
    (hil : ∀ n, IntegrableOn (fun z => ‖β n (A.p l) z - (starRingEnd ℂ) (Gl z)‖)
      (ball (A.ctr l) (3 / 2 * A.r l)))
    (hk : L1Conv (fun n => β n (A.p k)) (fun z => (starRingEnd ℂ) (Gk z))
      (ball (A.ctr k) (3 / 2 * A.r k)))
    (hl : L1Conv (fun n => β n (A.p l)) (fun z => (starRingEnd ℂ) (Gl z))
      (ball (A.ctr l) (3 / 2 * A.r l)))
    {w : ℂ} (hw : w ∈ ball (A.ctr k) (3 / 2 * A.r k)) (hwo : w ∈ overlap (A.p k) (A.p l))
    (hwl : trans (A.p k) (A.p l) w ∈ ball (A.ctr l) (3 / 2 * A.r l)) :
    Gk w = deriv (trans (A.p k) (A.p l)) w * Gl (trans (A.p k) (A.p l) w) := by
  set τ := trans (A.p k) (A.p l)
  set Bk := ball (A.ctr k) (3 / 2 * A.r k)
  set Bl := ball (A.ctr l) (3 / 2 * A.r l)
  have hτco : ContinuousOn τ (overlap (A.p k) (A.p l)) := fun v hv =>
    (trans_differentiableAt hv).continuousAt.continuousWithinAt
  set W := Bk ∩ (overlap (A.p k) (A.p l) ∩ τ ⁻¹' Bl)
  have hWo : IsOpen W := isOpen_ball.inter (hτco.isOpen_inter_preimage (isOpen_overlap _ _)
    isOpen_ball)
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo w ⟨hw, hwo, hwl⟩
  set B := closedBall w (ε / 2)
  have hBW : B ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBo : ∀ v ∈ B, v ∈ overlap (A.p k) (A.p l) := fun v hv => (hBW hv).2.1
  have hτd : ∀ v ∈ B, DifferentiableAt ℂ τ v := fun v hv => trans_differentiableAt (hBo v hv)
  have hτ'c : ContinuousOn (deriv τ) B := fun v hv =>
    (deriv_trans_differentiableAt (hBo v hv)).continuousAt.continuousWithinAt
  have hGlc : ContinuousOn (fun v => (starRingEnd ℂ) (Gl (τ v))) B :=
    Complex.continuous_conj.comp_continuousOn
      (hGl.continuousOn.comp (fun v hv => (hτd v hv).continuousAt.continuousWithinAt)
        fun v hv => (hBW hv).2.2)
  have hβlc : ∀ n, ContinuousOn (fun v => β n (A.p l) (τ v)) B := fun n =>
    (hβc n (A.p l)).comp (fun v hv => (hτd v hv).continuousAt.continuousWithinAt)
      fun v hv => (trans_mem_overlap (hBo v hv)).1
  -- transfer the chart-`l` limit to `B`
  have h2 : L1Conv (fun n => β n (A.p l) ∘ τ) ((fun z => (starRingEnd ℂ) (Gl z)) ∘ τ) B :=
    L1Conv.comp_holo hBc hBm hτd hτ'c ((trans_injOn _ _).mono hBo)
    (fun v hv => deriv_trans_ne_zero (hBo v hv)) (by rintro _ ⟨v, hv, rfl⟩; exact (hBW hv).2.2)
    (fun n => (hβlc n).sub hGlc) hil hl
  -- multiply by `conj τ'`
  obtain ⟨C, hC⟩ := hBc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp_continuousOn hτ'c)
  have h3 := L1Conv.mul_bounded h2 (m := fun v => (starRingEnd ℂ) (deriv τ v)) hC hBm
    fun n => ((hβlc n).sub hGlc).norm.integrableOn_compact hBc
  have h4 : L1Conv (fun n => β n (A.p k)) (fun v => (starRingEnd ℂ) (deriv τ v) *
      (starRingEnd ℂ) (Gl (τ v))) B :=
    h3.congr hBm (fun n v hv => (hβ n (A.p k) (A.p l) v (hBo v hv)).symm)
      (ae_of_all _ fun _ _ => rfl)
  have h1 : L1Conv (fun n => β n (A.p k)) (fun z => (starRingEnd ℂ) (Gk z)) B :=
    L1Conv.mono' (fun v hv => (hBW hv).1) hik hk
  have hGkc : ContinuousOn (fun v => (starRingEnd ℂ) (Gk v)) B :=
    Complex.continuous_conj.comp_continuousOn (hGk.continuousOn.mono fun v hv => (hBW hv).1)
  have hint : ∀ n, IntegrableOn (β n (A.p k)) B := fun n =>
    ((hβc n (A.p k)).mono fun v hv => (hBo v hv).1).integrableOn_compact hBc
  have hae := L1Conv.ae_eq hint (hGkc.integrableOn_compact hBc)
    (((Complex.continuous_conj.comp_continuousOn hτ'c).mul hGlc).integrableOn_compact hBc) h1 h4
  have heq := Measure.eqOn_open_of_ae_eq (μ := volume) (U := ball w (ε / 2))
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae) isOpen_ball
    (hGkc.mono ball_subset_closedBall)
    (((Complex.continuous_conj.comp_continuousOn hτ'c).mul hGlc).mono ball_subset_closedBall)
    (mem_ball_self (by linarith))
  have := congrArg (starRingEnd ℂ) heq
  simpa using this

end DiscAtlas

end JacobianChallenge.Surface
