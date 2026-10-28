import Jacobian.Surface.Hodge6

/-!
# Hodge decomposition, part 7: regularity of the limits

* `reg_weak`: the `L¹` limit `V` of the normalized readings satisfies `∂̄V = e` weakly in the
  open chart square.
* `reg_smooth`: hence (Weyl) `V` agrees a.e. with a smooth `S` with `∂̄S = e` there.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

theorem dbar_sub_const {f : ℂ → ℂ} {z : ℂ} (c : ℂ) :
    dbar (fun w => f w - c) z = dbar f z := by
  unfold dbar; rw [fderiv_sub_const]

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem bounded_of_test {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    ∃ C, ∀ z, ‖φ z‖ ≤ C := hφ.continuous.bounded_above_of_compact_support hs

theorem eq_zero_off {φ : ℂ → ℂ} {K : Set ℂ} (hs : tsupport φ ⊆ K) {z : ℂ} (hz : z ∉ K) :
    φ z = 0 ∧ dbar φ z = 0 := by
  have hz' : z ∉ tsupport φ := fun h => hz (hs h)
  exact ⟨image_eq_zero_of_notMem_tsupport hz',
    dbar_eq_zero_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz')⟩

variable [CompactSpace X]

/-- **The limit solves `∂̄V = e` weakly** in the open chart square. -/
theorem reg_weak (k : Fin A.N) {e : X → ℂ → ℂ} (he : Is01 e) (hes : SmoothFam e)
    {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n))
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 (A.toL2 e hes.contFam))) {c : ℕ → ℂ} {V : ℂ → ℂ} (hVi : IntegrableOn V (A.Q k))
    (hV : L1Conv (fun n w => rd (u n) (A.p k) w - c n) V (A.Q k))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ A.Qo k) :
    ∫ z, (A.Q k).indicator V z * dbar φ z = -∫ z, e (A.p k) z * φ z := by
  have hQ := A.measurableSet_Q k
  have hφQ : tsupport φ ⊆ A.Q k := hφt.trans (A.Qo_subset_Q k)
  have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
  have hdφc : Continuous (dbar φ) := continuous_dbar_of_contDiff hφ
  obtain ⟨Cd, hCd⟩ := hdφc.bounded_above_of_compact_support (hasCompactSupport_dbar hφs)
  obtain ⟨Cφ, hCφ⟩ := bounded_of_test hφ hφs
  -- left side as a limit
  have hint : ∀ n, IntegrableOn (fun w => rd (u n) (A.p k) w - c n) (A.Q k) := fun n =>
    (((hu n) (A.p k)).continuousOn.sub continuousOn_const |>.mono hQt).integrableOn_compact
      (A.isCompact_Q k)
  have hL := hV.tendsto_integral_mul hint hVi hdφc.aestronglyMeasurable hCd
  have eL : ∫ z, (A.Q k).indicator V z * dbar φ z = ∫ z in A.Q k, V z * dbar φ z := by
    rw [← integral_indicator hQ]
    congr 1; funext z
    by_cases hz : z ∈ A.Q k
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz]
  -- each term, by parts
  have hterm : ∀ n, ∫ z in A.Q k, (rd (u n) (A.p k) z - c n) * dbar φ z =
      -∫ z in A.Q k, dbar (rd (u n) (A.p k)) z * φ z := by
    intro n
    set G : ℂ → ℂ := fun w => A.glob k (u n) w - c n
    have hG : ContDiff ℝ 1 G := ((A.contDiff_glob k (hu n)).of_le (by simp)).sub contDiff_const
    have hGQ : ∀ z ∈ A.Q k, G z = rd (u n) (A.p k) z - c n := fun z hz => by
      simp only [G]; rw [(A.glob_eventuallyEq k (u n) (A.Q_subset_ball k hz)).self_of_nhds]
    have hdGQ : ∀ z ∈ A.Q k, dbar G z = dbar (rd (u n) (A.p k)) z := fun z hz => by
      simp only [G]
      rw [dbar_sub_const, dbar_congr (A.glob_eventuallyEq k (u n) (A.Q_subset_ball k hz))]
    have e1 : ∫ z in A.Q k, (rd (u n) (A.p k) z - c n) * dbar φ z = ∫ z, G z * dbar φ z :=
      calc ∫ z in A.Q k, (rd (u n) (A.p k) z - c n) * dbar φ z
          = ∫ z in A.Q k, G z * dbar φ z :=
            setIntegral_congr_fun hQ fun z hz => by rw [hGQ z hz]
        _ = ∫ z, G z * dbar φ z := setIntegral_eq_integral_of_forall_compl_eq_zero
            fun z hz => by rw [(eq_zero_off hφQ hz).2, mul_zero]
    have e2 : ∫ z, dbar G z * φ z = ∫ z in A.Q k, dbar (rd (u n) (A.p k)) z * φ z :=
      calc ∫ z, dbar G z * φ z = ∫ z in A.Q k, dbar G z * φ z :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              fun z hz => by rw [(eq_zero_off hφQ hz).1, mul_zero]).symm
        _ = _ := setIntegral_congr_fun hQ fun z hz => by rw [hdGQ z hz]
    rw [e1, integral_mul_dbar hG (hφ.of_le (by simp)) hφs, e2]
  -- right side as a limit
  have hR1 := A.reg_dbar_conv k he hes hu hlim
  have hint2 : ∀ n, IntegrableOn (fun w => dbar (rd (u n) (A.p k)) w) (A.D k) := fun n =>
    (((smoothFam_dbarF (hu n)).contFam (A.p k)).mono (A.D_subset_target k)).integrableOn_compact
      (isCompact_closedBall _ _)
  have heD : IntegrableOn (e (A.p k)) (A.D k) :=
    ((hes.contFam (A.p k)).mono (A.D_subset_target k)).integrableOn_compact
      (isCompact_closedBall _ _)
  have hR2 : L1Conv (fun n => dbar (rd (u n) (A.p k))) (e (A.p k)) (A.Q k) :=
    hR1.mono (A.Q_subset_D k) hint2 heD
  have hR := hR2.tendsto_integral_mul (fun n => (hint2 n).mono_set (A.Q_subset_D k))
    (heD.mono_set (A.Q_subset_D k)) hφ.continuous.aestronglyMeasurable hCφ
  have eR : ∫ z, e (A.p k) z * φ z = ∫ z in A.Q k, e (A.p k) z * φ z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := A.Q k) fun z hz => by
      rw [(eq_zero_off hφQ hz).1, mul_zero]).symm
  rw [eL, eR]
  have hL' : Tendsto (fun n => -∫ z in A.Q k, dbar (rd (u n) (A.p k)) z * φ z) atTop
      (𝓝 (∫ z in A.Q k, V z * dbar φ z)) := hL.congr hterm
  exact tendsto_nhds_unique hL' hR.neg

/-- **Regularity**: the limit agrees a.e. on the open chart square with a smooth solution of
`∂̄S = e`. -/
theorem reg_smooth (k : Fin A.N) {e : X → ℂ → ℂ} (he : Is01 e) (hes : SmoothFam e)
    {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n))
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 (A.toL2 e hes.contFam))) {c : ℕ → ℂ} {V : ℂ → ℂ} (hVi : IntegrableOn V (A.Q k))
    (hV : L1Conv (fun n w => rd (u n) (A.p k) w - c n) V (A.Q k)) :
    ∃ S : ℂ → ℂ, ContDiffOn ℝ ∞ S (A.Qo k) ∧ (∀ w ∈ A.Qo k, dbar S w = e (A.p k) w) ∧
      ∀ᵐ w, w ∈ A.Qo k → V w = S w := by
  have hQ := A.measurableSet_Q k
  have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
  set U := (A.Q k).indicator V
  have hUi : Integrable U := (integrable_indicator_iff hQ).mpr hVi
  have loc : ∀ x ∈ A.Qo k, ∃ ρ > 0, ball x ρ ⊆ A.Qo k ∧ ∃ g : ℂ → ℂ,
      (ContDiffOn ℝ ∞ g (ball x ρ) ∧ ∀ z ∈ ball x ρ, dbar g z = e (A.p k) z) ∧
      ContinuousOn g (ball x ρ) ∧ ∀ᵐ z, z ∈ ball x ρ → U z = g z := by
    intro x hx
    obtain ⟨ρ₀, hρ₀, hsub⟩ := Metric.isOpen_iff.mp (A.isOpen_Qo k) x hx
    have hft : ball x ρ₀ ⊆ (chartAt ℂ (A.p k)).target :=
      hsub.trans ((A.Qo_subset_Q k).trans hQt)
    obtain ⟨g, hg1, hg2, hg3⟩ := weyl_dbar_inhom hρ₀ hUi.integrableOn ((hes (A.p k)).mono hft)
      fun φ hφ hφs hφt => A.reg_weak k he hes hu hlim hVi hV hφ hφs (hφt.trans hsub)
    exact ⟨ρ₀ / 8, by positivity, (ball_subset_ball (by linarith)).trans hsub, g, ⟨hg1, hg2⟩,
      hg1.continuousOn, hg3⟩
  obtain ⟨S, hSae, hSloc⟩ := exists_glue (A.isOpen_Qo k)
    (Q := fun g x ρ => ContDiffOn ℝ ∞ g (ball x ρ) ∧ ∀ z ∈ ball x ρ, dbar g z = e (A.p k) z) loc
  have hev : ∀ x ∈ A.Qo k, ∃ g : ℂ → ℂ, S =ᶠ[𝓝 x] g ∧ ContDiffAt ℝ ∞ g x ∧
      dbar g x = e (A.p k) x := by
    intro x hx
    obtain ⟨ρ, hρ, -, g, ⟨hg1, hg2⟩, hEq⟩ := hSloc x hx
    refine ⟨g, ?_, hg1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ)),
      hg2 x (mem_ball_self hρ)⟩
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy using hEq hy
  refine ⟨S, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨g, hSg, hg, -⟩ := hev x hx
    exact (hg.congr_of_eventuallyEq hSg).contDiffWithinAt
  · obtain ⟨g, hSg, -, hge⟩ := hev x hx
    rw [dbar_congr hSg, hge]
  · filter_upwards [hSae] with w hw hwQ
    rw [← hw hwQ]
    simp [U, indicator_of_mem (A.Qo_subset_Q k hwQ)]

end DiscAtlas

end JacobianChallenge.Surface
