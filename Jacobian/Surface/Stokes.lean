import Jacobian.Surface.Forms

/-!
# Stokes' theorem on a compact Riemann surface

`integral_dzFam_eq_zero`: `∫_X ∂γ = 0` for a smooth `(0,1)`-form `γ`;
`integral_dbarFam_eq_zero`: `∫_X ∂̄β = 0` for a smooth `(1,0)`-form `β`.

Proof: `γ = ∑ⱼ ρⱼ γ` (partition of unity); each `∂(ρⱼ γ)` is a density supported in the chart
`j`, so its integral is a plane integral (`integral_eq_chart_of_supp`), of the derivative of a
compactly supported function, hence `0`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem rd_pou_eventuallyEq_zero (j : Fin A.N) {q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) (hx : (chartAt ℂ q).symm w ∉ A.pouSupp j) :
    rd (A.pou j) q =ᶠ[𝓝 w] fun _ => 0 :=
  ((chartAt ℂ q).continuousAt_symm hw).preimage_mem_nhds (A.pou_eventuallyEq_zero j hx)

theorem smulF_pou_eventuallyEq_zero (j : Fin A.N) (θ : X → ℂ → ℂ) {q : X} {w : ℂ}
    (hw : w ∈ (chartAt ℂ q).target) (hx : (chartAt ℂ q).symm w ∉ A.pouSupp j) :
    smulF (A.pou j) θ q =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [A.rd_pou_eventuallyEq_zero j hw hx] with v hv
  simp [smulF, hv]

theorem symm_notMem_pouSupp (j : Fin A.N) {w : ℂ} (hw : w ∈ (chartAt ℂ (A.p j)).target)
    (hwb : w ∉ closedBall (A.ctr j) (2 * A.r j)) :
    (chartAt ℂ (A.p j)).symm w ∉ A.pouSupp j := by
  rintro ⟨v, hv, hvw⟩
  have := congrArg (chartAt ℂ (A.p j)) hvw
  rw [(chartAt ℂ (A.p j)).right_inv hw,
    (chartAt ℂ (A.p j)).right_inv (A.ball_subset_target j (by norm_num) hv)] at this
  exact hwb (this ▸ hv)

/-- A density vanishing (in every chart) off `pouSupp j` integrates to its plane integral in
the chart `j`. -/
theorem integral_eq_chart_of_supp {σ : X → ℂ → ℂ} (hσ : IsDensity σ) (j : Fin A.N)
    (h0 : ∀ q : X, ∀ w ∈ (chartAt ℂ q).target, (chartAt ℂ q).symm w ∉ A.pouSupp j → σ q w = 0)
    (hc : ContinuousOn (σ (A.p j)) (chartAt ℂ (A.p j)).target) :
    A.integral σ = ∫ v in (chartAt ℂ (A.p j)).target, σ (A.p j) v := by
  refine A.integral_density_eq_chart hσ j (fun q w hw hs => h0 q w hw fun h =>
    hs (A.pouSupp_subset_source j h)) ?_
  have hK := A.ball_subset_target j (s := 2) (by norm_num)
  refine ((hc.mono hK).integrableOn_compact (isCompact_closedBall _ _)).of_forall_diff_eq_zero
    (chartAt ℂ (A.p j)).open_target.measurableSet fun w ⟨hw, hwb⟩ => ?_
  exact h0 _ w hw (A.symm_notMem_pouSupp j hw hwb)

/-- Extension by zero of a function on the chart target `j` supported in the disc of radius
`2 r_j`. -/
noncomputable def extTarget (j : Fin A.N) (ψ : ℂ → ℂ) : ℂ → ℂ :=
  (chartAt ℂ (A.p j)).target.indicator ψ

theorem extTarget_eventuallyEq (j : Fin A.N) {ψ : ℂ → ℂ} {v : ℂ}
    (hv : v ∈ (chartAt ℂ (A.p j)).target) : A.extTarget j ψ =ᶠ[𝓝 v] ψ := by
  filter_upwards [(chartAt ℂ (A.p j)).open_target.mem_nhds hv] with v' hv'
  simp [extTarget, indicator_of_mem hv']

theorem extTarget_eq_zero (j : Fin A.N) {ψ : ℂ → ℂ}
    (h0 : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) → ψ v = 0)
    {v : ℂ} (hv : v ∉ closedBall (A.ctr j) (2 * A.r j)) : A.extTarget j ψ v = 0 := by
  by_cases hvt : v ∈ (chartAt ℂ (A.p j)).target
  · simp [extTarget, indicator_of_mem hvt, h0 v hvt hv]
  · simp [extTarget, indicator_of_notMem hvt]

theorem contDiff_extTarget (j : Fin A.N) {ψ : ℂ → ℂ}
    (hψ : ContDiffOn ℝ ∞ ψ (chartAt ℂ (A.p j)).target)
    (h0 : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) → ψ v = 0) :
    ContDiff ℝ ∞ (A.extTarget j ψ) := by
  refine contDiff_iff_contDiffAt.mpr fun v => ?_
  by_cases hvt : v ∈ (chartAt ℂ (A.p j)).target
  · exact (hψ.contDiffAt ((chartAt ℂ (A.p j)).open_target.mem_nhds hvt)).congr_of_eventuallyEq
      (A.extTarget_eventuallyEq j hvt)
  · have hv : v ∉ closedBall (A.ctr j) (2 * A.r j) := fun h =>
      hvt (A.ball_subset_target j (by norm_num) h)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hv] with v' hv'
    exact A.extTarget_eq_zero j h0 hv'

theorem hasCompactSupport_extTarget (j : Fin A.N) {ψ : ℂ → ℂ}
    (h0 : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) → ψ v = 0) :
    HasCompactSupport (A.extTarget j ψ) :=
  HasCompactSupport.intro (isCompact_closedBall _ _) fun _ hv => A.extTarget_eq_zero j h0 hv

/-- `∫_{target} ∂ψ = 0` for `ψ` smooth on the chart target `j`, vanishing near the points
outside the disc of radius `2 r_j`. -/
theorem integral_target_dz_eq_zero (j : Fin A.N) {ψ : ℂ → ℂ}
    (hψ : ContDiffOn ℝ ∞ ψ (chartAt ℂ (A.p j)).target)
    (h0 : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) →
      ψ =ᶠ[𝓝 v] fun _ => 0) :
    ∫ v in (chartAt ℂ (A.p j)).target, dz ψ v = 0 := by
  have h0' : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) →
      ψ v = 0 := fun v hv hvb => (h0 v hv hvb).self_of_nhds
  have hc := A.contDiff_extTarget j hψ h0'
  have hcs := A.hasCompactSupport_extTarget j h0'
  have e1 : ∫ v in (chartAt ℂ (A.p j)).target, dz ψ v =
      ∫ v in (chartAt ℂ (A.p j)).target, dz (A.extTarget j ψ) v :=
    setIntegral_congr_fun (chartAt ℂ (A.p j)).open_target.measurableSet fun v hv =>
      (dz_congr (A.extTarget_eventuallyEq j hv)).symm
  rw [e1, setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_,
    integral_dz_eq_zero (hc.of_le (by simp)) hcs]
  have hv' : v ∉ closedBall (A.ctr j) (2 * A.r j) := fun h =>
    hv (A.ball_subset_target j (by norm_num) h)
  exact dz_eq_zero_of_eventuallyEq (c := 0) (by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hv'] with v' hv''
    exact A.extTarget_eq_zero j h0' hv'')

theorem integral_target_dbar_eq_zero (j : Fin A.N) {ψ : ℂ → ℂ}
    (hψ : ContDiffOn ℝ ∞ ψ (chartAt ℂ (A.p j)).target)
    (h0 : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) →
      ψ =ᶠ[𝓝 v] fun _ => 0) :
    ∫ v in (chartAt ℂ (A.p j)).target, dbar ψ v = 0 := by
  have h0' : ∀ v ∈ (chartAt ℂ (A.p j)).target, v ∉ closedBall (A.ctr j) (2 * A.r j) →
      ψ v = 0 := fun v hv hvb => (h0 v hv hvb).self_of_nhds
  have hc := A.contDiff_extTarget j hψ h0'
  have hcs := A.hasCompactSupport_extTarget j h0'
  have e1 : ∫ v in (chartAt ℂ (A.p j)).target, dbar ψ v =
      ∫ v in (chartAt ℂ (A.p j)).target, dbar (A.extTarget j ψ) v :=
    setIntegral_congr_fun (chartAt ℂ (A.p j)).open_target.measurableSet fun v hv =>
      (dbar_congr (A.extTarget_eventuallyEq j hv)).symm
  rw [e1, setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_,
    integral_dbar_eq_zero (hc.of_le (by simp)) hcs]
  have hv' : v ∉ closedBall (A.ctr j) (2 * A.r j) := fun h =>
    hv (A.ball_subset_target j (by norm_num) h)
  exact dbar_eq_zero_of_eventuallyEq (c := 0) (by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hv'] with v' hv''
    exact A.extTarget_eq_zero j h0' hv'')

/-- A family is the sum of its pieces `ρⱼ θ`. -/
theorem sum_smulF_pou (θ : X → ℂ → ℂ) (q : X) :
    (fun w => ∑ j, smulF (A.pou j) θ q w) = θ q := by
  funext w
  simp only [smulF, ← Finset.sum_mul, rd_apply]
  rw [A.sum_pou, one_mul]

/-- The integral of a finite sum of densities, each continuous on the chart targets. -/
theorem integral_sum {ι : Type*} (s : Finset ι) {σ : ι → X → ℂ → ℂ}
    (hc : ∀ k ∈ s, ∀ q : X, ContinuousOn (σ k q) (chartAt ℂ q).target) :
    A.integral (fun q w => ∑ k ∈ s, σ k q w) = ∑ k ∈ s, A.integral (σ k) := by
  unfold integral
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_finsetSum s fun k hk => ?_
  have hK := A.ball_subset_target i (s := 1) (by norm_num)
  rw [one_mul] at hK
  exact (((hc k hk (A.p i)).mono hK).integrableOn_compact (isCompact_closedBall _ _)).mono_set
    ((A.S_subset_ball i).trans ball_subset_closedBall)

theorem integral_congr {σ τ : X → ℂ → ℂ}
    (h : ∀ i : Fin A.N, ∀ w ∈ (chartAt ℂ (A.p i)).target, σ (A.p i) w = τ (A.p i) w) :
    A.integral σ = A.integral τ := by
  unfold integral
  refine Finset.sum_congr rfl fun i _ => setIntegral_congr_fun (A.measurableSet_S i)
    fun w hw => h i w ?_
  exact A.ball_subset_target i (s := 3) le_rfl
    (closedBall_subset_closedBall (by linarith [A.r_pos i])
      (ball_subset_closedBall (A.S_subset_ball i hw)))

/-- **Stokes**: `∫_X ∂γ = 0` for a smooth `(0,1)`-form. -/
theorem integral_dzFam_eq_zero {γ : X → ℂ → ℂ} (hγ : Is01 γ) (hs : SmoothFam γ) :
    A.integral (dzFam γ) = 0 := by
  have hsj : ∀ j, SmoothFam (smulF (A.pou j) γ) := fun j => hs.smulF (A.isSmooth_pou j)
  rw [A.integral_congr (τ := fun q w => ∑ j, dzFam (smulF (A.pou j) γ) q w) fun i w hw => by
    simp only [dzFam]
    conv_lhs => rw [← A.sum_smulF_pou γ (A.p i)]
    exact dz_sum _ fun j _ => (hsj j).differentiableAt hw]
  rw [A.integral_sum (σ := fun j => dzFam (smulF (A.pou j) γ)) Finset.univ
    fun j _ q => (contDiffOn_dz (chartAt ℂ q).open_target (hsj j q)).continuousOn]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [A.integral_eq_chart_of_supp (isDensity_dzFam (hγ.smulF _) (hsj j)) j
    (fun q w hw hx => dz_eq_zero_of_eventuallyEq (A.smulF_pou_eventuallyEq_zero j γ hw hx))
    (contDiffOn_dz (chartAt ℂ _).open_target (hsj j _)).continuousOn]
  exact A.integral_target_dz_eq_zero j (hsj j _) fun v hv hvb =>
    A.smulF_pou_eventuallyEq_zero j γ hv (A.symm_notMem_pouSupp j hv hvb)

/-- **Stokes**: `∫_X ∂̄β = 0` for a smooth `(1,0)`-form. -/
theorem integral_dbarFam_eq_zero {β : X → ℂ → ℂ} (hβ : Is10 β) (hs : SmoothFam β) :
    A.integral (dbarFam β) = 0 := by
  have hsj : ∀ j, SmoothFam (smulF (A.pou j) β) := fun j => hs.smulF (A.isSmooth_pou j)
  rw [A.integral_congr (τ := fun q w => ∑ j, dbarFam (smulF (A.pou j) β) q w) fun i w hw => by
    simp only [dbarFam]
    conv_lhs => rw [← A.sum_smulF_pou β (A.p i)]
    exact dbar_sum _ fun j _ => (hsj j).differentiableAt hw]
  rw [A.integral_sum (σ := fun j => dbarFam (smulF (A.pou j) β)) Finset.univ
    fun j _ q => (contDiffOn_dbar (chartAt ℂ q).open_target (hsj j q)).continuousOn]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [A.integral_eq_chart_of_supp (isDensity_dbarFam (hβ.smulF _) (hsj j)) j
    (fun q w hw hx => dbar_eq_zero_of_eventuallyEq (A.smulF_pou_eventuallyEq_zero j β hw hx))
    (contDiffOn_dbar (chartAt ℂ _).open_target (hsj j _)).continuousOn]
  exact A.integral_target_dbar_eq_zero j (hsj j _) fun v hv hvb =>
    A.smulF_pou_eventuallyEq_zero j β hv (A.symm_notMem_pouSupp j hv hvb)

end DiscAtlas

end JacobianChallenge.Surface
