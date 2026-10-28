import Jacobian.Surface.Hodge5

/-!
# Hodge decomposition, part 6: regularity, the limits

Setting: `e` a smooth `(0,1)`-form and smooth `u n` with `∂̄u n → e` in `L²(X)`.

* `reg_dbar_conv`: in each chart, `∂̄ (u n) → e` in `L¹(D_k)`.
* `reg_osc_cauchy`: `u n - (mean over Q k)` is `L¹(Q k)`-Cauchy.
* `reg_edge`, `reg_chain`: the chart means differ by Cauchy sequences (chaining over the
  connected surface).
* `reg_limit`: after subtracting the mean over one fixed square, the readings of `u n`
  converge in `L¹(Q k)` for every chart `k` meeting `X`.
-/

set_option linter.unusedSectionVars false

namespace JacobianChallenge.Surface

open JacobianChallenge.Analysis JacobianChallenge.Periods JacobianChallenge.HolomorphicForms
  MeasureTheory Set Metric Filter Topology Complex
open scoped Manifold ContDiff InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] [T2Space X]

theorem L1Cauchy.congr {f g : ℕ → ℂ → ℂ} {K : Set ℂ} (hK : MeasurableSet K)
    (hfg : ∀ n, ∀ z ∈ K, f n z = g n z) (h : L1Cauchy f K) : L1Cauchy g K := fun δ hδ => by
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun m hm n hn => ?_⟩
  have e : ∫ z in K, ‖f n z - f m z‖ = ∫ z in K, ‖g n z - g m z‖ :=
    setIntegral_congr_fun hK fun z hz => by simp only [hfg n z hz, hfg m z hz]
  rw [← e]
  exact hN m hm n hn

namespace DiscAtlas

variable (A : DiscAtlas X)

theorem toL2_dbarF_sub {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) :
    A.toL2 (dbarF (u - v)) (smoothFam_dbarF (hu.sub hv)).contFam =
      A.toL2 (dbarF u) (smoothFam_dbarF hu).contFam -
        A.toL2 (dbarF v) (smoothFam_dbarF hv).contFam := by
  rw [← A.toL2_sub]
  refine A.toL2_congr_target _ _ fun i w hw => ?_
  simp only [dbarF, Pi.sub_apply]
  have : rd (u - v) (A.p i) = fun w => rd u (A.p i) w - rd v (A.p i) w := rfl
  rw [this]
  unfold dbar
  rw [fderiv_fun_sub (hu.differentiableAt hw) (hv.differentiableAt hw)]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem mean_sub (k : Fin A.N) {u v : X → ℂ} (hu : IsSmooth u) (hv : IsSmooth v) :
    A.mean k (u - v) = A.mean k u - A.mean k v := by
  have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
  have i1 : IntegrableOn (rd u (A.p k)) (A.Q k) :=
    ((hu (A.p k)).continuousOn.mono hQt).integrableOn_compact (A.isCompact_Q k)
  have i2 : IntegrableOn (rd v (A.p k)) (A.Q k) :=
    ((hv (A.p k)).continuousOn.mono hQt).integrableOn_compact (A.isCompact_Q k)
  simp only [mean]
  rw [← smul_sub, ← MeasureTheory.integral_sub i1 i2]
  rfl

variable [CompactSpace X]

/-- In each chart, `∂̄ (u n) → e` in `L¹(D_k)`. -/
theorem reg_dbar_conv (k : Fin A.N) {e : X → ℂ → ℂ} (he : Is01 e) (hes : SmoothFam e)
    {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n))
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 (A.toL2 e hes.contFam))) :
    L1Conv (fun n => dbar (rd (u n) (A.p k))) (e (A.p k)) (A.D k) := by
  set α : ℕ → X → ℂ → ℂ := fun n => dbarF (u n) - e
  have hαc : ∀ n, ContFam (α n) := fun n => (smoothFam_dbarF (hu n)).contFam.sub hes.contFam
  have hαd : ∀ n, IsDensity (fun p w => (starRingEnd ℂ) (α n p w) * α n p w) := fun n =>
    isDensity_conj_mul_01 ((dbarF_is01 (hu n)).sub he) ((dbarF_is01 (hu n)).sub he)
  have hnorm : Tendsto (fun n => ‖A.toL2 (α n) (hαc n)‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hlim
    refine this.congr fun n => ?_
    rw [A.toL2_sub (smoothFam_dbarF (hu n)).contFam hes.contFam]
  set V := volume.real (A.D k) + 1
  have hV : 0 < V := by positivity
  unfold L1Conv
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm (Real.sqrt (δ ^ 2 / (4 * (1 / 2) ^ 2 * V)))
    (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h0 : 0 ≤ ∫ w in A.D k, ‖dbar (rd (u n) (A.p k)) w - e (A.p k) w‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  refine lt_of_forall_bound (C := 1 / 2) (V := V) (d := ‖A.toL2 (α n) (hαc n)‖) (by norm_num)
    hV hδ (fun ε hε => ?_) ?_
  · have := A.integral_D_le k (hαd n) (hαc n) hε
    have hvol : volume.real (A.D k) ≤ V := by simp [V]
    calc ∫ w in A.D k, ‖dbar (rd (u n) (A.p k)) w - e (A.p k) w‖
        = ∫ w in A.D k, ‖α n (A.p k) w‖ := rfl
      _ ≤ ε / 2 * volume.real (A.D k) + ‖A.toL2 (α n) (hαc n)‖ ^ 2 / (2 * ε) := this
      _ ≤ 1 / 2 * (ε * V + ‖A.toL2 (α n) (hαc n)‖ ^ 2 / ε) := by
          have : ε / 2 * volume.real (A.D k) ≤ ε / 2 * V := by gcongr
          have e2 : ‖A.toL2 (α n) (hαc n)‖ ^ 2 / (2 * ε) =
              1 / 2 * (‖A.toL2 (α n) (hαc n)‖ ^ 2 / ε) := by field_simp
          rw [e2]; linarith
  · have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    calc ‖A.toL2 (α n) (hαc n)‖ ^ 2 < Real.sqrt (δ ^ 2 / (4 * (1 / 2) ^ 2 * V)) ^ 2 := by
          gcongr
      _ = _ := Real.sq_sqrt (by positivity)

/-- The oscillation of `u n` on `Q k` is `L¹`-Cauchy. -/
theorem reg_osc_cauchy (k : Fin A.N) {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n)) {T : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 T)) :
    L1Cauchy (fun n w => rd (u n) (A.p k) w - A.mean k (u n)) (A.Q k) := by
  intro δ hδ
  have hr := A.r_pos k
  set V := volume.real (A.D k) + 1
  have hV : 0 < V := by positivity
  set C := 4 * A.r k
  have hC : 0 < C := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq
    (Real.sqrt (δ ^ 2 / (4 * C ^ 2 * V))) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hv := (hu n).sub (hu m)
  have heq : ∀ w, rd (u n) (A.p k) w - A.mean k (u n) - (rd (u m) (A.p k) w - A.mean k (u m)) =
      rd (u n - u m) (A.p k) w - A.mean k (u n - u m) := fun w => by
    rw [A.mean_sub k (hu n) (hu m)]; simp only [rd_apply, Pi.sub_apply]; ring
  simp_rw [heq]
  set d := ‖A.toL2 (dbarF (u n - u m)) (smoothFam_dbarF hv).contFam‖
  refine lt_of_forall_bound (C := C) (V := V) (d := d) hC hV hδ (fun ε hε => ?_) ?_
  · have := A.chart_L1_bound k hv hε
    have hvol : volume.real (A.D k) ≤ V := by simp [V]
    refine this.trans ?_
    have : ε / 2 * volume.real (A.D k) ≤ ε / 2 * V := by gcongr
    have e2 : d ^ 2 / (2 * ε) = 1 / 2 * (d ^ 2 / ε) := by field_simp
    simp only [C]
    rw [e2]
    nlinarith [sq_nonneg d, div_nonneg (sq_nonneg d) hε.le]
  · have := hN n hn m hm
    rw [dist_eq_norm, ← A.toL2_dbarF_sub (hu n) (hu m)] at this
    calc d ^ 2 < Real.sqrt (δ ^ 2 / (4 * C ^ 2 * V)) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (by positivity)

theorem Q_integrable_sub (k : Fin A.N) {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n)) (c : ℕ → ℂ)
    (n m : ℕ) : IntegrableOn (fun w => ‖(rd (u n) (A.p k) w - c n) -
      (rd (u m) (A.p k) w - c m)‖) (A.Q k) := by
  have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
  exact ((((hu n) (A.p k)).continuousOn.sub continuousOn_const).sub
    (((hu m) (A.p k)).continuousOn.sub continuousOn_const)).norm.mono hQt
    |>.integrableOn_compact (A.isCompact_Q k)

/-- **Edges**: on overlapping chart squares the means differ by a Cauchy sequence. -/
theorem reg_edge (k l : Fin A.N) (hkl : (A.U k ∩ A.U l).Nonempty) {u : ℕ → X → ℂ}
    (hu : ∀ n, IsSmooth (u n)) {T : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 T)) :
    CauchySeq fun n => A.mean l (u n) - A.mean k (u n) := by
  obtain ⟨x, hxk, hxl⟩ := hkl
  set τ := trans (A.p k) (A.p l)
  set v₀ := chartAt ℂ (A.p k) x
  have hv₀o : v₀ ∈ overlap (A.p k) (A.p l) :=
    ⟨(chartAt ℂ (A.p k)).map_source hxk.1, by
      show (chartAt ℂ (A.p k)).symm (chartAt ℂ (A.p k) x) ∈ (chartAt ℂ (A.p l)).source
      rw [(chartAt ℂ (A.p k)).left_inv hxk.1]; exact hxl.1⟩
  have hτv₀ : τ v₀ = chartAt ℂ (A.p l) x := by
    show chartAt ℂ (A.p l) ((chartAt ℂ (A.p k)).symm (chartAt ℂ (A.p k) x)) = _
    rw [(chartAt ℂ (A.p k)).left_inv hxk.1]
  have hτco : ContinuousOn τ (overlap (A.p k) (A.p l)) := fun v hv =>
    (trans_differentiableAt hv).continuousAt.continuousWithinAt
  set W := ball (A.ctr k) (A.r k) ∩ (overlap (A.p k) (A.p l) ∩ τ ⁻¹' ball (A.ctr l) (A.r l))
  have hWo : IsOpen W := isOpen_ball.inter (hτco.isOpen_inter_preimage (isOpen_overlap _ _)
    isOpen_ball)
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo v₀ ⟨hxk.2, hv₀o, by rw [mem_preimage, hτv₀]; exact hxl.2⟩
  set B := closedBall v₀ (ε / 2)
  have hBW : B ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBo : ∀ v ∈ B, v ∈ overlap (A.p k) (A.p l) := fun v hv => (hBW hv).2.1
  have hBQ : B ⊆ A.Q k := fun v hv => A.Qo_subset_Q k (A.ball_subset_Qo k (hBW hv).1)
  have hτBQ : τ '' B ⊆ A.Q l := by
    rintro _ ⟨v, hv, rfl⟩; exact A.Qo_subset_Q l (A.ball_subset_Qo l (hBW hv).2.2)
  have hτd : ∀ v ∈ B, DifferentiableAt ℂ τ v := fun v hv => trans_differentiableAt (hBo v hv)
  have hτ'c : ContinuousOn (deriv τ) B := fun v hv =>
    (deriv_trans_differentiableAt (hBo v hv)).continuousAt.continuousWithinAt
  set g : ℕ → ℂ → ℂ := fun n w => rd (u n) (A.p k) w - A.mean k (u n)
  set h : ℕ → ℂ → ℂ := fun n w => rd (u n) (A.p l) w - A.mean l (u n)
  have hg := (A.reg_osc_cauchy k hu hlim).mono hBQ (A.Q_integrable_sub k hu _)
  have hlt : ∀ n, ContinuousOn (fun v => rd (u n) (A.p l) (τ v)) B := fun n =>
    ((hu n) (A.p l)).continuousOn.comp (fun v hv => (hτd v hv).continuousAt.continuousWithinAt)
      fun v hv => (trans_mem_overlap (hBo v hv)).1
  have hh := (A.reg_osc_cauchy l hu hlim).comp_holo (τ := τ) hBc hBm hτd hτ'c
    ((trans_injOn _ _).mono hBo) (fun v hv => deriv_trans_ne_zero (hBo v hv)) hτBQ
    (fun n m => ((hlt n).sub continuousOn_const).sub ((hlt m).sub continuousOn_const))
    (A.Q_integrable_sub l hu _)
  have hgi : ∀ n m, IntegrableOn (fun z => ‖g n z - g m z‖) B := fun n m =>
    (A.Q_integrable_sub k hu (fun n => A.mean k (u n)) n m).mono_set hBQ
  have hhi : ∀ n m, IntegrableOn (fun z => ‖-(h n ∘ τ) z - -(h m ∘ τ) z‖) B := fun n m => by
    have hc : ContinuousOn (fun z => ‖-(h n ∘ τ) z - -(h m ∘ τ) z‖) B :=
      (((hlt n).sub continuousOn_const).neg.sub ((hlt m).sub continuousOn_const).neg).norm
    exact hc.integrableOn_compact hBc
  have hsum := hg.add hgi hhi hh.neg
  have hconst : L1Cauchy (fun n _ => A.mean l (u n) - A.mean k (u n)) B := by
    refine hsum.congr hBm fun n w hw => ?_
    simp only [g, h, Function.comp_apply]
    rw [show rd (u n) (A.p l) (τ w) = rd (u n) (A.p k) w from rd_trans (hBo w hw)]
    ring
  exact cauchySeq_of_L1Cauchy_const (by
    rw [measureReal_def]; exact ENNReal.toReal_pos (measure_closedBall_pos _ _ (by linarith)).ne'
      measure_closedBall_lt_top.ne) hconst

/-- **Chaining**: the means over all chart squares meeting `X` differ from a fixed one by
Cauchy sequences. -/
theorem reg_chain [ConnectedSpace X] (k₀ : Fin A.N) (hk₀ : (A.U k₀).Nonempty)
    {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n)) {T : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 T)) :
    ∀ k, (A.U k).Nonempty → CauchySeq fun n => A.mean k (u n) - A.mean k₀ (u n) := by
  refine index_connected A.U A.isOpen_U (fun y => ?_) _ k₀ ?_ hk₀ fun k l hk hkl => ?_
  · obtain ⟨i, h1, h2⟩ := A.cover y; exact ⟨i, h1, h2⟩
  · simp only [sub_self]; exact cauchySeq_const 0
  · have := (A.reg_edge k l hkl hu hlim).add hk
    convert this using 1
    funext n; simp only [Pi.add_apply]; ring

/-- **Limits**: normalized by one fixed mean, the readings converge in `L¹(Q k)`. -/
theorem reg_limit [ConnectedSpace X] (k₀ : Fin A.N) (hk₀ : (A.U k₀).Nonempty) (k : Fin A.N)
    (hk : (A.U k).Nonempty) {u : ℕ → X → ℂ} (hu : ∀ n, IsSmooth (u n)) {T : A.L2}
    (hlim : Tendsto (fun n => A.toL2 (dbarF (u n)) (smoothFam_dbarF (hu n)).contFam) atTop
      (𝓝 T)) :
    ∃ V : ℂ → ℂ, IntegrableOn V (A.Q k) ∧
      L1Conv (fun n w => rd (u n) (A.p k) w - A.mean k₀ (u n)) V (A.Q k) := by
  have hc := L1Cauchy.const (A.reg_chain k₀ hk₀ hu hlim k hk) (K := A.Q k)
    (measure_mono (A.Q_subset_D k) |>.trans_lt (A.volume_D_lt_top k))
  have hcs := (A.reg_osc_cauchy k hu hlim).add (A.Q_integrable_sub k hu _)
    (g := fun n _ => A.mean k (u n) - A.mean k₀ (u n))
    (fun n m => continuous_const.continuousOn.integrableOn_compact (A.isCompact_Q k)) hc
  have hQt : A.Q k ⊆ (chartAt ℂ (A.p k)).target := (A.Q_subset_D k).trans (A.D_subset_target k)
  refine L1Cauchy.exists_lim (fun n => ?_) (hcs.congr (A.measurableSet_Q k) fun n w _ => by ring)
  exact ((((hu n) (A.p k)).continuousOn.sub continuousOn_const).mono hQt).integrableOn_compact
    (A.isCompact_Q k)

end DiscAtlas

end JacobianChallenge.Surface
