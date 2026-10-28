/-!
# RETIRED — not built, not imported

Declarations moved verbatim out of `Jacobian/TraceDegree/TraceDefinition.lean` on branch `independent-repair`
(goal (a), removal of `StableChartAt`).

Every declaration here depended — directly or through other declarations in this
file — on the refuted chart-stability property (`chartAt` locally constant), either
as the old typeclass `StableChartAt` or through the eval-at-`1` global-frame reading
of cotangent vectors that it justified. `Jacobian/Periods/ChartStabilityRefutation.lean`
proves that property false for every compact connected Riemann surface, so on the
spaces this project is about these proofs were vacuous.

The file is kept only as a record and as raw material: it does **not** compile
(the binders and the class it used are gone), and nothing may import it. The true
statements these helpers served are now explicit, labelled gaps in the live tree:

* `compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier` (classical input),
* `traceForm_extension_per_BCD` (TraceSpec),
* `meromorphic_no_poles_holomorphic_representative` (MeromorphicToBranchedCover).

See `ref/stablechart-uses.md` and `ref/independent-repair-progress.md`.
-/

/--
**Chart-local analyticity of `ω.toFun · 1`.**
For a holomorphic 1-form `ω` on `X` and base point `x₀`, the function
`ε ↦ (ω.toFun ((chartAt ℂ x₀).symm ε)) 1` is analytic at `chartAt ℂ x₀ x₀`.
-/
theorem etaTimesOne_chart_local_analytic
    (ω : HolomorphicOneForm ℂ X) (x₀ : X) :
    AnalyticAt ℂ (fun ε : ℂ => (ω.toFun ((chartAt ℂ x₀).symm ε)) (1 : ℂ))
      (chartAt ℂ x₀ x₀) := by
  have h1 : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        (show (Bundle.Trivial X ℂ) x from (ω.toFun x) (1 : ℂ))) :=
    ω.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
  have hsrc : (fun x : X => Bundle.TotalSpace.mk' ℂ
      (E := Bundle.Trivial X ℂ) x ((ω.toFun x) (1 : ℂ))) x₀
        ∈ (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).source := by
    rw [(trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have h_iff :=
    (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).contMDiffAt_iff
      (IB := 𝓘(ℂ, ℂ)) (IM := 𝓘(ℂ, ℂ)) (n := (⊤ : WithTop ℕ∞))
      (f := fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        ((ω.toFun x) (1 : ℂ)))
      hsrc
  have h_evalOne : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤
      (fun x : X => (ω.toFun x) (1 : ℂ)) x₀ :=
    (h_iff.mp h1.contMDiffAt).2
  rw [contMDiffAt_iff] at h_evalOne
  obtain ⟨_h_cont, h_cdwithin⟩ := h_evalOne
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h_cdwithin
  exact h_cdwithin.analyticAt

/--
Pullback of a holomorphic form along a local inverse branch is holomorphic.

This is the **discharge** of the former axiom `localPullbackAt_holomorphic`
(formerly at this site as an `axiom`). The proof passes through the singleton
chart on `CotangentModelFiber ℂ` (`cotangentFiberIso`), reducing to analyticity
of a ℂ-valued chart-local function. Under `StableChartAt`, the chart-local
form collapses to `z ↦ (deriv F (r z))⁻¹ * Θ(r z)` where `F := chartLocalAt f x`,
`r : ℂ → ℂ` is the analytic local inverse from `HasStrictDerivAt.localInverse`,
and `Θ` is the eta-times-one function (analytic by `etaTimesOne_chart_local_analytic`).
-/
theorem localPullbackAt_holomorphic
    [T2Space X] [T2Space Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x) := by
  classical
  set z₀ : ℂ := chartAt ℂ x x with hz₀_def
  set w₀ : ℂ := chartAt ℂ (f x) (f x) with hw₀_def
  set F : ℂ → ℂ := chartLocalAt f x with hF_def
  have hfHolAt : IsHolomorphicAt f x := hf.holomorphicAt x
  have hF_an : AnalyticAt ℂ F z₀ := hfHolAt
  have hFz₀ : F z₀ = w₀ := by simp [F, z₀, w₀, chartLocalAt]
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat hfHolAt]; exact hx
  have hderiv : deriv F z₀ ≠ 0 := by
    have h_order : analyticOrderAt
        (fun t => F t - F z₀) z₀ = 1 := by
      convert hramAt using 1
      unfold mapAnalyticOrderAt
      simp +decide [analyticOrderNatAt, F, z₀]
    have h_an : AnalyticAt ℂ (fun t => F t - F z₀) z₀ := hF_an.sub analyticAt_const
    have h_deriv_order : analyticOrderAt
        (deriv (fun t => F t - F z₀)) z₀ = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one h_an
      aesop
    rw [analyticOrderAt_eq_zero] at h_deriv_order
    rcases h_deriv_order with hzero | hnezero
    · exfalso; exact hzero (AnalyticAt.deriv h_an)
    · simpa [deriv_sub_const] using hnezero
  have hSD : HasStrictDerivAt F (deriv F z₀) z₀ := hF_an.hasStrictDerivAt
  set r : ℂ → ℂ := hSD.localInverse F (deriv F z₀) z₀ hderiv with hr_def
  have hr_an_at_w₀ : AnalyticAt ℂ r w₀ := by
    rw [← hFz₀]
    simpa [r, hr_def] using hF_an.analyticAt_localInverse hderiv
  have hr_w₀ : r w₀ = z₀ := by
    have h_left : ∀ᶠ z in 𝓝 z₀, r (F z) = z := by
      simpa [r, hr_def] using hSD.eventually_left_inverse hderiv
    have := h_left.self_of_nhds
    rwa [hFz₀] at this
  have h_right_inv_F : ∀ᶠ z in 𝓝 w₀, F (r z) = z := by
    have h := hSD.eventually_right_inverse hderiv
    rw [hFz₀] at h
    simpa [r, hr_def] using h
  have hr_tendsto : Filter.Tendsto r (𝓝 w₀) (𝓝 z₀) := by
    have := hr_an_at_w₀.continuousAt
    rwa [ContinuousAt, hr_w₀] at this
  have h_chartXsymm_z₀ : (chartAt ℂ x).symm z₀ = x := by
    simp [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have h_chartYsymm_w₀ : (chartAt ℂ (f x)).symm w₀ = f x := by
    simp [w₀, (chartAt ℂ (f x)).left_inv (mem_chart_source ℂ (f x))]
  have h_chartXsymm_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ x).symm z)
      (𝓝 z₀) (𝓝 x) := by
    have hcont := (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    change Filter.Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
      (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
    rwa [h_chartXsymm_z₀] at hcont
  have h_chartYsymm_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ (f x)).symm z)
      (𝓝 w₀) (𝓝 (f x)) := by
    have hcont := (chartAt ℂ (f x)).continuousAt_symm
      ((chartAt ℂ (f x)).map_source (mem_chart_source ℂ (f x)))
    change Filter.Tendsto (fun z => (chartAt ℂ (f x)).symm z) (𝓝 w₀)
      (𝓝 ((chartAt ℂ (f x)).symm w₀)) at hcont
    rwa [h_chartYsymm_w₀] at hcont
  have h_anal_inv_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ x).symm (r z))
      (𝓝 w₀) (𝓝 x) := h_chartXsymm_tendsto.comp hr_tendsto
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  have h_y'_in_V : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ (f x)).symm z ∈ V :=
    h_chartYsymm_tendsto.eventually (hVopen.mem_nhds hfxV)
  have h_anal_inv_in_U : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ x).symm (r z) ∈ U :=
    h_anal_inv_tendsto.eventually (hUopen.mem_nhds hxU)
  have h_anal_inv_in_chart_source : ∀ᶠ z in 𝓝 w₀,
      (chartAt ℂ x).symm (r z) ∈ (chartAt ℂ x).source :=
    h_anal_inv_tendsto.eventually
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  have h_localInv_eq : ∀ᶠ z in 𝓝 w₀,
      h.localInverseAt x hx ((chartAt ℂ (f x)).symm z) =
        (chartAt ℂ x).symm (r z) := by
    have h_f_anal_inv_in_src : ∀ᶠ z in 𝓝 w₀,
        f ((chartAt ℂ x).symm (r z)) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Filter.Tendsto (fun z => f ((chartAt ℂ x).symm (r z))) (𝓝 w₀)
          (𝓝 (f x)) := (hf.continuous.continuousAt (x := x)).tendsto.comp h_anal_inv_tendsto
      exact htendsto.eventually
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have h_z_in_target : ∀ᶠ z in 𝓝 w₀, z ∈ (chartAt ℂ (f x)).target :=
      chart_target_mem_nhds ℂ (f x)
    have h_f_eq : ∀ᶠ z in 𝓝 w₀,
        f ((chartAt ℂ x).symm (r z)) = (chartAt ℂ (f x)).symm z := by
      filter_upwards [h_right_inv_F, h_anal_inv_in_chart_source, h_z_in_target,
        h_f_anal_inv_in_src]
        with z h_FrZ h_anal_in_src h_z_target h_f_anal_in_src
      have hF_unfold : F (r z) = chartAt ℂ (f x) (f ((chartAt ℂ x).symm (r z))) := by
        simp [F, chartLocalAt, Function.comp_apply]
      rw [hF_unfold] at h_FrZ
      have h_apply : (chartAt ℂ (f x)).symm
          (chartAt ℂ (f x) (f ((chartAt ℂ x).symm (r z)))) =
          (chartAt ℂ (f x)).symm z := by rw [h_FrZ]
      rw [(chartAt ℂ (f x)).left_inv h_f_anal_in_src] at h_apply
      exact h_apply
    filter_upwards [h_f_eq, h_anal_inv_in_U] with z h_f_eq h_anal_in_U
    have h_lb := hleft_branch ((chartAt ℂ x).symm (r z)) h_anal_in_U
    rw [h_f_eq] at h_lb
    exact h_lb
  set Θ : ℂ → ℂ := fun ε => (ω.toFun ((chartAt ℂ x).symm ε)) (1 : ℂ) with hΘ_def
  have hΘ_an : AnalyticAt ℂ Θ z₀ := by
    simpa [Θ, z₀] using etaTimesOne_chart_local_analytic ω x
  have h_derivF_an : AnalyticAt ℂ (deriv F) z₀ := hF_an.deriv
  have h_derivF_circ_r_an : AnalyticAt ℂ (fun z => deriv F (r z)) w₀ := by
    have h_derivF_an' : AnalyticAt ℂ (deriv F) (r w₀) := by rw [hr_w₀]; exact h_derivF_an
    exact h_derivF_an'.comp hr_an_at_w₀
  have h_derivF_circ_r_ne : (fun z => deriv F (r z)) w₀ ≠ 0 := by
    show deriv F (r w₀) ≠ 0; rw [hr_w₀]; exact hderiv
  have h_inv_an : AnalyticAt ℂ (fun z => (deriv F (r z))⁻¹) w₀ :=
    h_derivF_circ_r_an.inv h_derivF_circ_r_ne
  have hΘ_circ_r_an : AnalyticAt ℂ (fun z => Θ (r z)) w₀ := by
    have hΘ_an' : AnalyticAt ℂ Θ (r w₀) := by rw [hr_w₀]; exact hΘ_an
    exact hΘ_an'.comp hr_an_at_w₀
  have h_chartCand_an : AnalyticAt ℂ
      (fun z => (deriv F (r z))⁻¹ * Θ (r z)) w₀ :=
    h_inv_an.mul hΘ_circ_r_an
  unfold IsHolomorphicAt chartLocalAt
  refine h_chartCand_an.congr ?_
  have h_evt_unram : ∀ᶠ z in 𝓝 w₀,
      h.ramificationIndex (h.localInverseAt x hx ((chartAt ℂ (f x)).symm z)) = 1 :=
    h_chartYsymm_tendsto.eventually
      (h.localInverseAt_eventually_unramified x hx)
  have h_z_in_target_evt : ∀ᶠ z in 𝓝 w₀, z ∈ (chartAt ℂ (f x)).target :=
    chart_target_mem_nhds ℂ (f x)
  have h_rz_in_target_evt : ∀ᶠ z in 𝓝 w₀, r z ∈ (chartAt ℂ x).target := by
    have h_z₀_in_target : z₀ ∈ (chartAt ℂ x).target := by
      show chartAt ℂ x x ∈ (chartAt ℂ x).target
      exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    exact hr_tendsto.eventually ((chartAt ℂ x).open_target.mem_nhds h_z₀_in_target)
  filter_upwards [h_localInv_eq, h_evt_unram, h_anal_inv_in_chart_source,
    h_y'_in_V, h_z_in_target_evt, h_rz_in_target_evt]
    with z h_loc_eq h_unram h_anal_in_src h_y_in_V h_z_in_target h_rz_in_target
  set y' : Y := (chartAt ℂ (f x)).symm z with hy'_def
  set x' : X := h.localInverseAt x hx y' with hx'_def
  have hx'_alt : x' = (chartAt ℂ x).symm (r z) := h_loc_eq
  have h_chart_eq : chartAt ℂ x' = chartAt ℂ x :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      x x' (by rw [hx'_alt]; exact h_anal_in_src)
  have h_chartAt_x'_x' : chartAt ℂ x' x' = r z := by
    rw [h_chart_eq, hx'_alt]
    exact (chartAt ℂ x).right_inv h_rz_in_target
  have hfx'_eq_y' : f x' = (chartAt ℂ (f x)).symm z := by
    show f (h.localInverseAt x hx y') = (chartAt ℂ (f x)).symm z
    exact hright_branch y' h_y_in_V
  have h_fx'_in_chartY_source : f x' ∈ (chartAt ℂ (f x)).source := by
    rw [hfx'_eq_y']
    exact (chartAt ℂ (f x)).map_target h_z_in_target
  have h_chartY_eq : chartAt ℂ (f x') = chartAt ℂ (f x) :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      (f x) (f x') h_fx'_in_chartY_source
  have h_chartLocalAt_eq : chartLocalAt f x' = F := by
    show chartAt ℂ (f x') ∘ f ∘ (chartAt ℂ x').symm = chartLocalAt f x
    rw [h_chartY_eq, h_chart_eq]
    rfl
  have h_cp_apply :=
    cotangentPushforward_apply_one (f := f) h hcompat hf (x := x') h_unram (ω.toFun x')
  have h_eta_eq : (ω.toFun x') (1 : ℂ) = Θ (r z) := by
    show (ω.toFun x') (1 : ℂ) = (ω.toFun ((chartAt ℂ x).symm (r z))) (1 : ℂ)
    rw [hx'_alt]
  symm
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (localPullbackAt h hf ω x hx ((chartAt ℂ (f x)).symm z)))
    = (deriv F (r z))⁻¹ * Θ (r z)
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (deriv F (r z))⁻¹ * Θ (r z)
  have h_chart_eq_iso : (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (cotangentPushforward f x' (ω.toFun x')) (1 : ℂ) := rfl
  rw [h_chart_eq_iso, h_cp_apply, h_chartLocalAt_eq, h_chartAt_x'_x', h_eta_eq]
  rfl

/-- The local trace is holomorphic at regular values. -/
theorem localTraceAtRegularValue_holomorphic
    [T2Space X] [T2Space Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  unfold localTraceAtRegularValue
  refine IsHolomorphicAt.sum_cotangentModelFiber ?_
  rintro ⟨x, hx_mem⟩ _mem_attach
  have hx_fiber : x ∈ f ⁻¹' {y} := (Set.Finite.mem_toFinset _).mp hx_mem
  have hfx : f x = y := hx_fiber
  simpa [hfx] using
    (localPullbackAt_holomorphic h hcompat hf ω x (hy x hx_fiber))
