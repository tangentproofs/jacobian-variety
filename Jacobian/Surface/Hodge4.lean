import Jacobian.Surface.Hodge3

/-!
# Hodge decomposition, part 4: chart squares and the `L¹` bound

For each chart `k`: the closed square `Q k` (side `2 r_k`, centred at `z_k`), its interior
`Qo k ⊇ ball z_k r_k`, and `Q k ⊆ ball z_k ((3/2) r_k)`. `glob k u` is a smooth function on `ℂ`
equal to the reading of `u` near `Q k`. `chart_L1_bound`: the oscillation of a smooth `v` on
`Q k` is controlled by `‖∂̄v‖_{L²(X)}` (Poincaré + `‖∂v‖ = ‖∂̄v‖` + the local `L²` bound).
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

/-- A real-variable lemma: a quantity bounded by `C (ε V + d²/ε)` for every `ε > 0` is small
when `d` is. -/
theorem lt_of_forall_bound {Φ d C V δ : ℝ} (hC : 0 < C) (hV : 0 < V) (hδ : 0 < δ)
    (h : ∀ ε > 0, Φ ≤ C * (ε * V + d ^ 2 / ε)) (hd : d ^ 2 < δ ^ 2 / (4 * C ^ 2 * V)) :
    Φ < δ := by
  set ε := δ / (2 * C * V)
  have hε : 0 < ε := by positivity
  have h1 := h ε hε
  have e1 : C * (ε * V) = δ / 2 := by simp only [ε]; field_simp; try ring
  have h2 : C * (d ^ 2 / ε) < δ / 2 := by
    rw [mul_div_assoc', div_lt_iff₀ hε]
    calc C * d ^ 2 < C * (δ ^ 2 / (4 * C ^ 2 * V)) := by gcongr
      _ = δ / 2 * ε := by simp only [ε]; field_simp; try ring
  linarith [show C * (ε * V + d ^ 2 / ε) = C * (ε * V) + C * (d ^ 2 / ε) by ring]

namespace DiscAtlas

variable (A : DiscAtlas X)

/-- The chart square. -/
def Q (k : Fin A.N) : Set ℂ :=
  cbox ((A.ctr k).re - A.r k) ((A.ctr k).im - A.r k) (2 * A.r k)

/-- Its interior. -/
def Qo (k : Fin A.N) : Set ℂ :=
  {w | |w.re - (A.ctr k).re| < A.r k ∧ |w.im - (A.ctr k).im| < A.r k}

theorem mem_Q {k : Fin A.N} {w : ℂ} :
    w ∈ A.Q k ↔ |w.re - (A.ctr k).re| ≤ A.r k ∧ |w.im - (A.ctr k).im| ≤ A.r k := by
  simp only [Q, mem_cbox, mem_Icc, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem isOpen_Qo (k : Fin A.N) : IsOpen (A.Qo k) := by
  have h1 : Continuous fun w : ℂ => |w.re - (A.ctr k).re| := by fun_prop
  have h2 : Continuous fun w : ℂ => |w.im - (A.ctr k).im| := by fun_prop
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

theorem Qo_subset_Q (k : Fin A.N) : A.Qo k ⊆ A.Q k := fun w hw =>
  A.mem_Q.mpr ⟨hw.1.le, hw.2.le⟩

theorem ball_subset_Qo (k : Fin A.N) : ball (A.ctr k) (A.r k) ⊆ A.Qo k := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  exact ⟨lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - A.ctr k)) hw,
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - A.ctr k)) hw⟩

theorem Q_subset_ball (k : Fin A.N) : A.Q k ⊆ ball (A.ctr k) (3 / 2 * A.r k) := by
  intro w hw
  obtain ⟨h1, h2⟩ := A.mem_Q.mp hw
  have hr := A.r_pos k
  rw [mem_ball, dist_eq_norm]
  have hn : ‖w - A.ctr k‖ ^ 2 ≤ 2 * A.r k ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, sub_im]
    nlinarith [abs_le.mp h1, abs_le.mp h2, sq_abs ((w - A.ctr k).re)]
  nlinarith [norm_nonneg (w - A.ctr k)]

theorem Q_subset_D (k : Fin A.N) : A.Q k ⊆ A.D k :=
  (A.Q_subset_ball k).trans ball_subset_closedBall

theorem isCompact_Q (k : Fin A.N) : IsCompact (A.Q k) := by
  have : A.Q k = Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      box ((A.ctr k).re - A.r k) ((A.ctr k).im - A.r k) (2 * A.r k) := rfl
  rw [this]
  exact (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).mpr (isCompact_box _ _ _)

theorem measurableSet_Q (k : Fin A.N) : MeasurableSet (A.Q k) := measurableSet_cbox _ _ _

/-- A smooth function on `ℂ` equal to the reading of `u` near `Q k`. -/
noncomputable def glob (k : Fin A.N) (u : X → ℂ) : ℂ → ℂ :=
  A.extTarget k (rd (A.cut k * u) (A.p k))

theorem contDiff_glob (k : Fin A.N) {u : X → ℂ} (hu : IsSmooth u) :
    ContDiff ℝ ∞ (A.glob k u) := by
  refine A.contDiff_extTarget k (((A.isSmooth_cut k).mul hu) (A.p k)) fun v hv hvb => ?_
  have := A.cut_eq_zero k (A.symm_notMem_pouSupp k hv hvb)
  simp [rd_apply, this]

theorem glob_eventuallyEq (k : Fin A.N) (u : X → ℂ) {w : ℂ}
    (hw : w ∈ ball (A.ctr k) (3 / 2 * A.r k)) : A.glob k u =ᶠ[𝓝 w] rd u (A.p k) := by
  filter_upwards [isOpen_ball.mem_nhds hw] with v hv
  have hvt : v ∈ (chartAt ℂ (A.p k)).target := A.D_subset_target k (ball_subset_closedBall hv)
  have h1 : rd (A.cut k) (A.p k) v = 1 := A.rd_cut_self k hvt (ball_subset_closedBall hv)
  simp only [glob, extTarget, indicator_of_mem hvt]
  show rd (A.cut k) (A.p k) v * rd u (A.p k) v = rd u (A.p k) v
  rw [h1, one_mul]

/-- The mean of the reading of `u` over `Q k`. -/
noncomputable def mean (k : Fin A.N) (u : X → ℂ) : ℂ :=
  ((2 * A.r k) ^ 2)⁻¹ • ∫ w in A.Q k, rd u (A.p k) w

theorem norm_fderiv_le (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖ ≤ 2 * (‖dz f z‖ + ‖dbar f z‖) := by
  rw [fderiv_apply_eq_dz_add_dbar, fderiv_apply_I_eq, norm_mul, Complex.norm_I, one_mul]
  linarith [norm_add_le (dz f z) (dbar f z), norm_sub_le (dz f z) (dbar f z)]

/-- **Poincaré in a chart square.** -/
theorem chart_poincare (k : Fin A.N) {u : X → ℂ} (hu : IsSmooth u) :
    ∫ w in A.Q k, ‖rd u (A.p k) w - A.mean k u‖ ≤
      2 * A.r k * ∫ w in A.Q k, 2 * (‖dz (rd u (A.p k)) w‖ + ‖dbar (rd u (A.p k)) w‖) := by
  have hr := A.r_pos k
  have hP := poincare_cbox ((A.contDiff_glob k hu).of_le (by simp))
    ((A.ctr k).re - A.r k) ((A.ctr k).im - A.r k) (L := 2 * A.r k) (by positivity)
  have hQ := A.measurableSet_Q k
  have hg : ∀ w ∈ A.Q k, A.glob k u w = rd u (A.p k) w := fun w hw =>
    (A.glob_eventuallyEq k u (A.Q_subset_ball k hw)).self_of_nhds
  have hgd : ∀ w ∈ A.Q k, fderiv ℝ (A.glob k u) w = fderiv ℝ (rd u (A.p k)) w := fun w hw =>
    (A.glob_eventuallyEq k u (A.Q_subset_ball k hw)).fderiv_eq
  have hmean : ∫ v in A.Q k, A.glob k u v = ∫ v in A.Q k, rd u (A.p k) v :=
    setIntegral_congr_fun hQ hg
  change ∫ w in A.Q k, ‖A.glob k u w - ((2 * A.r k) ^ 2)⁻¹ • ∫ v in A.Q k, A.glob k u v‖ ≤
    2 * A.r k * ∫ w in A.Q k, (‖fderiv ℝ (A.glob k u) w 1‖ + ‖fderiv ℝ (A.glob k u) w I‖) at hP
  have e1 : ∫ w in A.Q k, ‖A.glob k u w - ((2 * A.r k) ^ 2)⁻¹ • ∫ v in A.Q k, A.glob k u v‖ =
      ∫ w in A.Q k, ‖rd u (A.p k) w - A.mean k u‖ := by
    rw [hmean]
    exact setIntegral_congr_fun hQ fun w hw => by rw [hg w hw]; rfl
  have e2 : ∫ w in A.Q k, (‖fderiv ℝ (A.glob k u) w 1‖ + ‖fderiv ℝ (A.glob k u) w I‖) =
      ∫ w in A.Q k, (‖fderiv ℝ (rd u (A.p k)) w 1‖ + ‖fderiv ℝ (rd u (A.p k)) w I‖) :=
    setIntegral_congr_fun hQ fun w hw => by rw [hgd w hw]
  rw [e1, e2] at hP
  refine hP.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hc : ContinuousOn (fun w => ‖dz (rd u (A.p k)) w‖ + ‖dbar (rd u (A.p k)) w‖) (A.Q k) := by
    have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
    exact ((contDiffOn_dz (chartAt ℂ _).open_target (hu _)).continuousOn.norm.add
      (contDiffOn_dbar (chartAt ℂ _).open_target (hu _)).continuousOn.norm).mono hQt
  have hc' : ContinuousOn (fun w => ‖fderiv ℝ (rd u (A.p k)) w 1‖ +
      ‖fderiv ℝ (rd u (A.p k)) w I‖) (A.Q k) := by
    have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
    have hf := (hu (A.p k)).fderiv_of_isOpen (chartAt ℂ _).open_target (m := ∞) (by simp)
    exact ((hf.continuousOn.clm_apply continuousOn_const).norm.add
      (hf.continuousOn.clm_apply continuousOn_const).norm).mono hQt
  exact setIntegral_mono_on (hc'.integrableOn_compact (A.isCompact_Q k))
    ((hc.integrableOn_compact (A.isCompact_Q k)).const_mul 2) hQ fun w _ => norm_fderiv_le _ _

/-- `L¹(D_k)` of a chart reading, controlled by the global `L²` norm. -/
theorem integral_D_le (k : Fin A.N) {α : X → ℂ → ℂ}
    (hd : IsDensity (fun p w => (starRingEnd ℂ) (α p w) * α p w)) (hc : ContFam α) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ w in A.D k, ‖α (A.p k) w‖ ≤ ε / 2 * volume.real (A.D k) + ‖A.toL2 α hc‖ ^ 2 / (2 * ε) :=
  (A.integral_norm_le_of_sq k ((hc (A.p k)).mono (A.D_subset_target k)) hε).trans
    (by gcongr; exact A.integral_sq_le_norm_toL2 k hd hc)

/-- **The oscillation on a chart square is controlled by `‖∂̄v‖`.** -/
theorem chart_L1_bound [CompactSpace X] (k : Fin A.N) {v : X → ℂ} (hv : IsSmooth v) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ w in A.Q k, ‖rd v (A.p k) w - A.mean k v‖ ≤
      8 * A.r k * (ε / 2 * volume.real (A.D k) +
        ‖A.toL2 (dbarF v) (smoothFam_dbarF hv).contFam‖ ^ 2 / (2 * ε)) := by
  have hr := A.r_pos k
  have hQD := A.Q_subset_D k
  have hDt := A.D_subset_target k
  have hdz := (smoothFam_dzF hv).contFam (A.p k)
  have hdb := (smoothFam_dbarF hv).contFam (A.p k)
  have i1 : IntegrableOn (fun w => ‖dz (rd v (A.p k)) w‖) (A.D k) :=
    (hdz.mono hDt).norm.integrableOn_compact (isCompact_closedBall _ _)
  have i2 : IntegrableOn (fun w => ‖dbar (rd v (A.p k)) w‖) (A.D k) :=
    (hdb.mono hDt).norm.integrableOn_compact (isCompact_closedBall _ _)
  have h1 := A.integral_D_le k (isDensity_conj_mul_10 (dzF_is10 hv) (dzF_is10 hv))
    (smoothFam_dzF hv).contFam hε
  have h2 := A.integral_D_le k (isDensity_conj_mul_01 (dbarF_is01 hv) (dbarF_is01 hv))
    (smoothFam_dbarF hv).contFam hε
  rw [A.norm_toL2_dzF_eq hv] at h1
  have hsplit : ∫ w in A.Q k, 2 * (‖dz (rd v (A.p k)) w‖ + ‖dbar (rd v (A.p k)) w‖) ≤
      2 * ((∫ w in A.D k, ‖dz (rd v (A.p k)) w‖) + ∫ w in A.D k, ‖dbar (rd v (A.p k)) w‖) := by
    rw [integral_const_mul, ← integral_add i1 i2]
    exact mul_le_mul_of_nonneg_left (setIntegral_mono_set (i1.add i2)
      (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Eventually.of_forall hQD)) (by norm_num)
  calc ∫ w in A.Q k, ‖rd v (A.p k) w - A.mean k v‖
      ≤ 2 * A.r k * ∫ w in A.Q k, 2 * (‖dz (rd v (A.p k)) w‖ + ‖dbar (rd v (A.p k)) w‖) :=
        A.chart_poincare k hv
    _ ≤ 2 * A.r k * (2 * ((∫ w in A.D k, ‖dz (rd v (A.p k)) w‖) +
          ∫ w in A.D k, ‖dbar (rd v (A.p k)) w‖)) := by gcongr
    _ ≤ _ := by
        simp only [dzF, dbarF] at h1 h2
        nlinarith [h1, h2]

end DiscAtlas

end JacobianChallenge.Surface
