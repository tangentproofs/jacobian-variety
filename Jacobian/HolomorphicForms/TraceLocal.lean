import Jacobian.TraceDegree.TraceDefinition
import Jacobian.Periods.ChainPushforward
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Local structure of the trace of a holomorphic 1-form

For a nonconstant holomorphic map `f : X → Y` of compact Riemann surfaces and a holomorphic
1-form `η` on `X`, the trace `Tr η` — at a regular value `y`, the sum over the fibre of the
pushed-forward covectors `η_x ∘ (df_x)⁻¹` — extends to a holomorphic 1-form on `Y`. This file
proves it with no chart-stability assumption, by the classical local argument:

near any `y₀ ∈ Y`, in the chart `c_q` at `y₀`, write `Tr η = d(Tr H)` where `H` are local
primitives of `η` on small coordinate balls around the fibre points of `y₀` and
`Tr H (w) = Σ_{x ∈ f⁻¹(c_q⁻¹ w)} H(x)` (with multiplicity). `Tr H` is holomorphic off `y₀`
(inverse branches at unramified points) and continuous at `y₀` (the fibre collapses onto
the fibre of `y₀`), hence holomorphic at `y₀` by Riemann's removable-singularity theorem.

Contents: inverse branches at unramified points (`exists_local_branch`); the local trace
data `TraceChartData` (`exists_traceChartData`); `Tr H` and its holomorphy on the ball
(`TraceChartData.trH_differentiableOn`); the chart reading of a pushed-forward covector
(`cotangentPushforward_chart`) and of the fibre-sum trace (`TraceChartData.fiberTrace_read`);
the global form `traceHolomorphicForm` (fibre sum at unramified values, `d(Tr H)` at branch
values) and its local primitives `Tr H` in any chart (`traceHolomorphicForm_segment_eq`).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods Set Metric Filter
open scoped Manifold Topology ContDiff

universe u v

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]
  {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]
  {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)

include hf in
/-- The chart expression of `f` is analytic at every point where it is defined. -/
theorem chartMap_analyticAt {x₀ : X} {y₀ : Y} {z : ℂ} (hz : z ∈ (chartAt ℂ x₀).target)
    (hfz : f ((chartAt ℂ x₀).symm z) ∈ (chartAt ℂ y₀).source) :
    AnalyticAt ℂ (chartMap f x₀ y₀) z := by
  set N : Set ℂ := (chartAt ℂ x₀).target ∩
    ((chartAt ℂ x₀).symm ⁻¹' (f ⁻¹' (chartAt ℂ y₀).source))
  have hN : N ∈ 𝓝 z := by
    refine inter_mem ((chartAt ℂ x₀).open_target.mem_nhds hz) ?_
    exact ((hf.continuous.continuousAt).comp ((chartAt ℂ x₀).continuousAt_symm hz)).preimage_mem_nhds
      ((chartAt ℂ y₀).open_source.mem_nhds hfz)
  refine DifferentiableOn.analyticAt (s := N) (fun w hw => ?_) hN
  exact (chartMap_differentiableAt hf hw.1 hw.2).differentiableWithinAt

include hf in
/-- At an unramified point the chart expression of `f` has nonzero derivative. -/
theorem chartMap_deriv_ne_zero_of_unramified {x₀ : X} {y₀ : Y} {x' : X}
    (hx' : x' ∈ (chartAt ℂ x₀).source) (hfx' : f x' ∈ (chartAt ℂ y₀).source)
    (hram : mapAnalyticOrderAt f x' = 1) :
    deriv (chartMap f x₀ y₀) (chartAt ℂ x₀ x') ≠ 0 := by
  set c := chartAt ℂ x₀
  set φ := chartMap f x₀ y₀
  set z' := c x'
  have hz' : z' ∈ c.target := c.map_source hx'
  have hsymm : c.symm z' = x' := c.left_inv hx'
  have hφan : AnalyticAt ℂ φ z' := chartMap_analyticAt hf hz' (by rwa [hsymm])
  have hord : analyticOrderNatAt (fun t => (chartAt ℂ y₀) (f (c.symm t)) - (chartAt ℂ y₀) (f x'))
      (c x') = 1 := by
    rw [mapAnalyticOrderAt_congr_of_maximalAtlas ((isHolomorphicBasic_of_contMDiff hf).holomorphicAt x')
      hf.continuous.continuousAt (IsManifold.chart_mem_maximalAtlas x₀) hx'
      (IsManifold.chart_mem_maximalAtlas y₀) hfx', hram]
  have hfun : (fun t => (chartAt ℂ y₀) (f (c.symm t)) - (chartAt ℂ y₀) (f x')) =
      fun t => φ t - φ z' := by
    funext t
    show _ = (chartAt ℂ y₀) (f (c.symm t)) - (chartAt ℂ y₀) (f (c.symm z'))
    rw [hsymm]
  rw [hfun] at hord
  have hord' : analyticOrderAt (fun t => φ t - φ z') z' = 1 := by
    unfold analyticOrderNatAt at hord
    exact (ENat.toNat_eq_iff one_ne_zero).mp hord
  have hd := hφan.analyticOrderAt_deriv_add_one
  rw [hord'] at hd
  have hd0 : analyticOrderAt (deriv φ) z' = 0 := by
    by_cases htop : analyticOrderAt (deriv φ) z' = ⊤
    · rw [htop] at hd; simp at hd
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn] at hd ⊢
      have h1 : n + 1 = 1 := by exact_mod_cast hd
      have h2 : n = 0 := by omega
      rw [h2]; rfl
  rw [analyticOrderAt_eq_zero] at hd0
  exact hd0.resolve_left (fun h => h hφan.deriv)

include hf in
/-- **Inverse branch at an unramified point**, in charts. -/
theorem exists_local_branch {x₀ : X} {y₀ : Y} {x' : X}
    (hx' : x' ∈ (chartAt ℂ x₀).source) (hfx' : f x' ∈ (chartAt ℂ y₀).source)
    (hram : mapAnalyticOrderAt f x' = 1) :
    ∃ g : ℂ → ℂ,
      g (chartMap f x₀ y₀ (chartAt ℂ x₀ x')) = chartAt ℂ x₀ x' ∧
      AnalyticAt ℂ g (chartMap f x₀ y₀ (chartAt ℂ x₀ x')) ∧
      HasDerivAt g (deriv (chartMap f x₀ y₀) (chartAt ℂ x₀ x'))⁻¹
        (chartMap f x₀ y₀ (chartAt ℂ x₀ x')) ∧
      (∀ᶠ w in 𝓝 (chartMap f x₀ y₀ (chartAt ℂ x₀ x')), chartMap f x₀ y₀ (g w) = w) ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ x₀ x'), g (chartMap f x₀ y₀ z) = z) := by
  set c := chartAt ℂ x₀
  set φ := chartMap f x₀ y₀
  set z' := c x'
  have hz' : z' ∈ c.target := c.map_source hx'
  have hsymm : c.symm z' = x' := c.left_inv hx'
  have hφan : AnalyticAt ℂ φ z' := chartMap_analyticAt hf hz' (by rwa [hsymm])
  have hd := chartMap_deriv_ne_zero_of_unramified hf hx' hfx' hram
  set hS := hφan.hasStrictDerivAt
  refine ⟨hS.localInverse φ (deriv φ z') z' hd, ?_, hφan.analyticAt_localInverse hd,
    (hS.to_localInverse hd).hasDerivAt, hS.eventually_right_inverse hd,
    hS.eventually_left_inverse hd⟩
  exact (hS.eventually_left_inverse hd).self_of_nhds

section LocalData

attribute [local instance] Classical.propDecidable

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y]
  (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite)

open Classical in
/-- The fibre of `f` over `y`, as a finset. -/
noncomputable def fiberFin (y : Y) : Finset X := (hfin y).toFinset

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [T2Space Y] in
@[simp] theorem mem_fiberFin {y : Y} {x : X} : x ∈ fiberFin hfin y ↔ f x = y := by
  simp [fiberFin]

/--
**Local trace data at `y₀`.** Disjoint chart neighbourhoods `U x` of the fibre points `x`
of `y₀`, each inside a coordinate ball of the chart at `x`, and a ball around `c_q y₀` in
the chart at `y₀`, over which every fibre lies in `⋃ U x` and (away from `y₀`) meets each
`U x` in exactly `m(x)` unramified points (`m` = local analytic order).
-/
structure TraceChartData (y₀ : Y) where
  ρ : ℝ
  ρ_pos : 0 < ρ
  ball_sub : ball (chartAt ℂ y₀ y₀) ρ ⊆ (chartAt ℂ y₀).target
  U : X → Set X
  r : X → ℝ
  U_open : ∀ x, IsOpen (U x)
  mem_U : ∀ x ∈ fiberFin hfin y₀, x ∈ U x
  U_sub_source : ∀ x ∈ fiberFin hfin y₀, U x ⊆ (chartAt ℂ x).source
  U_sub_ball : ∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ U x, chartAt ℂ x x' ∈ ball (chartAt ℂ x x) (r x)
  ballX_sub : ∀ x ∈ fiberFin hfin y₀, ball (chartAt ℂ x x) (r x) ⊆ (chartAt ℂ x).target
  disj : ∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ fiberFin hfin y₀, x ≠ x' → Disjoint (U x) (U x')
  cover : ∀ w ∈ ball (chartAt ℂ y₀ y₀) ρ, ∀ x', f x' = (chartAt ℂ y₀).symm w →
    ∃ x ∈ fiberFin hfin y₀, x' ∈ U x
  kfold : ∀ w ∈ ball (chartAt ℂ y₀ y₀) ρ, w ≠ chartAt ℂ y₀ y₀ → ∀ x ∈ fiberFin hfin y₀,
    ((fiberFin hfin ((chartAt ℂ y₀).symm w)).filter (· ∈ U x)).card = mapAnalyticOrderAt f x ∧
    ∀ x' ∈ (fiberFin hfin ((chartAt ℂ y₀).symm w)).filter (· ∈ U x),
      mapAnalyticOrderAt f x' = 1

include hf in
theorem exists_traceChartData (hnc : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₀ : Y) :
    Nonempty (TraceChartData (f := f) hfin y₀) := by
  classical
  set cq := chartAt ℂ y₀
  set F0 := fiberFin hfin y₀
  -- disjoint neighbourhoods of the fibre points
  obtain ⟨T, hT, hTdisj⟩ := (hfin y₀).t2_separation
  -- chart balls
  have hball : ∀ x : X, ∃ r > 0, ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target := fun x =>
    Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  choose r hr hrsub using hball
  let O : X → Set X := fun x => T x ∩ ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (r x))
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (hT x).2.inter ((chartAt ℂ x).isOpen_inter_preimage isOpen_ball)
  have hxO : ∀ x, x ∈ O x := fun x =>
    ⟨(hT x).1, mem_chart_source ℂ x, mem_ball_self (hr x)⟩
  have hk := fun x => local_kfold_ramified_of_contMDiff_within hf (hO x) (hxO x)
    (mapAnalyticOrderAt_pos_of_contMDiff hf hnc x) rfl
  choose U hUopen hxU hUO V hVopen hfxV hV using hk
  -- the image of the complement of `⋃ U` is closed and misses `y₀`
  let K : Set X := (⋃ x ∈ F0, U x)ᶜ
  have hKc : IsCompact K :=
    (isOpen_biUnion fun x _ => hUopen x).isClosed_compl.isCompact
  have hfK : IsClosed (f '' K) := (hKc.image hf.continuous).isClosed
  let VY : Set Y := (⋂ x ∈ F0, V x) ∩ (f '' K)ᶜ ∩ cq.source
  have hVYo : IsOpen VY :=
    ((isOpen_biInter_finset fun x _ => hVopen x).inter hfK.isOpen_compl).inter cq.open_source
  have hy₀ : y₀ ∈ VY := by
    refine ⟨⟨?_, ?_⟩, mem_chart_source ℂ y₀⟩
    · refine Set.mem_iInter₂.mpr fun x hx => ?_
      have : f x = y₀ := (mem_fiberFin hfin).mp hx
      rw [← this]; exact hfxV x
    · rintro ⟨x', hx'K, hx'⟩
      exact hx'K (Set.mem_biUnion ((mem_fiberFin hfin).mpr hx') (hxU x'))
  have hNo : IsOpen (cq.target ∩ cq.symm ⁻¹' VY) := cq.isOpen_inter_preimage_symm hVYo
  have hcy : cq y₀ ∈ cq.target ∩ cq.symm ⁻¹' VY :=
    ⟨cq.map_source (mem_chart_source ℂ y₀), by
      show cq.symm (cq y₀) ∈ VY
      rw [cq.left_inv (mem_chart_source ℂ y₀)]; exact hy₀⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hNo _ hcy
  refine ⟨{
    ρ := ρ
    ρ_pos := hρ
    ball_sub := fun w hw => (hρsub hw).1
    U := U
    r := r
    U_open := hUopen
    mem_U := fun x _ => hxU x
    U_sub_source := fun x _ x' hx' => (hUO x hx').2.1
    U_sub_ball := fun x _ x' hx' => (hUO x hx').2.2
    ballX_sub := fun x _ => hrsub x
    disj := fun x hx x' hx' hne =>
      (hTdisj ((mem_fiberFin hfin).mp hx) ((mem_fiberFin hfin).mp hx') hne).mono
        (fun z hz => (hUO x hz).1) (fun z hz => (hUO x' hz).1)
    cover := ?_
    kfold := ?_ }⟩
  · intro w hw x' hx'
    have hVY := (hρsub hw).2
    by_contra hnot
    refine hVY.1.2 ⟨x', fun hmem => ?_, hx'⟩
    obtain ⟨x, hx, hxU'⟩ := Set.mem_iUnion₂.mp hmem
    exact hnot ⟨x, hx, hxU'⟩
  · intro w hw hne x hx
    set y := cq.symm w
    have hwt : w ∈ cq.target := (hρsub hw).1
    have hyne : y ≠ f x := by
      rw [(mem_fiberFin hfin).mp hx]
      intro h
      apply hne
      rw [← cq.right_inv hwt]
      show cq y = cq y₀
      rw [h]
    have hyV : y ∈ V x := by
      exact Set.mem_iInter₂.mp (hρsub hw).2.1.1 x hx
    obtain ⟨t, htcard, htU, htprop, htall⟩ := hV x y hyV hyne
    have hfilter : (fiberFin hfin y).filter (· ∈ U x) = t := by
      ext x'
      simp only [Finset.mem_filter, mem_fiberFin]
      constructor
      · rintro ⟨h1, h2⟩; exact htall x' h2 h1
      · intro h; exact ⟨(htprop x' h).1, htU h⟩
    rw [hfilter]
    exact ⟨htcard, fun x' h => (htprop x' h).2⟩

end LocalData

section ChartReading

/-- A `ℂ`-linear map `ℂ → ℂ` is multiplication by its value at `1`. -/
theorem clm_apply_eq_mul (L : ℂ →L[ℂ] ℂ) (v : ℂ) : L v = v * L 1 := by
  have h := L.map_smul v (1 : ℂ)
  simpa [smul_eq_mul] using h

/-- View a linear map between tangent lines as a map `ℂ →L[ℂ] ℂ` (definitional). -/
abbrev toL {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] {x : M} {y : N}
    (L : TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) : ℂ →L[ℂ] ℂ := L

/-- View a cotangent vector as a map `ℂ →L[ℂ] ℂ` (definitional). -/
abbrev toLc {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M}
    (ωx : CotangentSpace ℂ M x) : ℂ →L[ℂ] ℂ := ωx

include hf in
/-- **Chart reading of a pushed-forward covector.** At an unramified point `p` (in the chart at
`x`, with `f p` in the chart at `y₀`), pushing `ω_p` forward and reading it in the chart at `y₀`
is reading `ω_p` in the chart at `x` and dividing by the derivative of the chart expression
of `f`. -/
theorem cotangentPushforward_chart (x : X) (y₀ : Y) {p : X} (h1 : p ∈ (chartAt ℂ x).source)
    (h2 : f p ∈ (chartAt ℂ y₀).source)
    (hd : deriv (chartMap f x y₀) (chartAt ℂ x p) ≠ 0) (ωp : CotangentSpace ℂ X p) :
    toLc (cotangentPushforward f p ωp)
        (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y₀).symm (chartAt ℂ y₀ (f p))) 1) =
      toLc ωp (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm (chartAt ℂ x p))
        ((deriv (chartMap f x y₀) (chartAt ℂ x p))⁻¹)) := by
  set cx := chartAt ℂ x
  set cq := chartAt ℂ y₀
  set z := cx p
  have hz : z ∈ cx.target := cx.map_source h1
  have hsymm : cx.symm z = p := cx.left_inv h1
  have hfz : f (cx.symm z) ∈ cq.source := by rw [hsymm]; exact h2
  set A := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f p)
  set B := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cx.symm z)
  set C := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq (f p))
  set C' := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq.symm (cq (f p)))
  have hderiv : deriv (chartMap f x y₀) z = C (A (B 1)) := by
    rw [← fderiv_apply_one_eq_deriv, chartMap_fderiv hf hz hfz]
    show (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq (f (cx.symm z)))
      ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f (cx.symm z)) (B 1)) = _
    rw [hsymm]
    rfl
  have hCC' : C' (C 1) = 1 := congrArg (fun L => L (1 : ℂ)) (mfderiv_chartAt_symm_comp_self y₀ h2)
  set a := A 1
  set b := B 1
  set c := C 1
  set c' := C' 1
  have hdv : deriv (chartMap f x y₀) z = c * (a * b) := by
    rw [hderiv, clm_apply_eq_mul C, clm_apply_eq_mul A]; ring
  have hne : c * (a * b) ≠ 0 := hdv ▸ hd
  have ha : a ≠ 0 := fun h => hne (by rw [h]; ring)
  have hb : b ≠ 0 := fun h => hne (by rw [h]; ring)
  have hc : c ≠ 0 := fun h => hne (by rw [h]; ring)
  have hc' : c' = c⁻¹ := by
    have h := hCC'
    rw [clm_apply_eq_mul C'] at h
    field_simp
    linear_combination h
  -- `df_p` is invertible
  have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f p)) := ⟨{
    inv := (a⁻¹ • ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ)
    left_inv := by
      refine ContinuousLinearMap.ext fun v => ?_
      show a⁻¹ * A v = v
      rw [clm_apply_eq_mul A v]; field_simp; ring
    right_inv := by
      refine ContinuousLinearMap.ext fun v => ?_
      show A (a⁻¹ * (show ℂ from v)) = v
      rw [clm_apply_eq_mul A]; field_simp; exact mul_comm _ _ }⟩
  have hinv : ∀ u : ℂ, toL (Classical.choice hiso).inv u = u / a := by
    intro u
    have hr := congrArg (fun L => toL L u) (Classical.choice hiso).right_inv
    have hr' : A (toL (Classical.choice hiso).inv u) = u := hr
    rw [clm_apply_eq_mul A] at hr'
    field_simp
    linear_combination hr'
  unfold cotangentPushforward
  rw [dif_pos hiso]
  show toLc ωp (toL (Classical.choice hiso).inv c') = toLc ωp (B (deriv (chartMap f x y₀) z)⁻¹)
  rw [hinv, clm_apply_eq_mul (toLc ωp), clm_apply_eq_mul (toLc ωp) (B _), clm_apply_eq_mul B,
    hdv, hc']
  field_simp
  rfl

end ChartReading

section TraceH

attribute [local instance] Classical.propDecidable

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y]
  {hfin : ∀ y : Y, (f ⁻¹' {y}).Finite}

/-- The chosen inverse branch (in the chart at `x`) at a point `x'` where it exists. -/
noncomputable def localBranch (y₀ : Y) (x x' : X) : ℂ → ℂ :=
  if h : x' ∈ (chartAt ℂ x).source ∧ f x' ∈ (chartAt ℂ y₀).source ∧ mapAnalyticOrderAt f x' = 1
  then (exists_local_branch hf h.1 h.2.1 h.2.2).choose else id

include hf in
theorem localBranch_spec {y₀ : Y} {x x' : X} (h1 : x' ∈ (chartAt ℂ x).source)
    (h2 : f x' ∈ (chartAt ℂ y₀).source) (h3 : mapAnalyticOrderAt f x' = 1) :
    localBranch hf y₀ x x' (chartMap f x y₀ (chartAt ℂ x x')) = chartAt ℂ x x' ∧
      AnalyticAt ℂ (localBranch hf y₀ x x') (chartMap f x y₀ (chartAt ℂ x x')) ∧
      HasDerivAt (localBranch hf y₀ x x') (deriv (chartMap f x y₀) (chartAt ℂ x x'))⁻¹
        (chartMap f x y₀ (chartAt ℂ x x')) ∧
      (∀ᶠ w in 𝓝 (chartMap f x y₀ (chartAt ℂ x x')),
        chartMap f x y₀ (localBranch hf y₀ x x' w) = w) := by
  have h : x' ∈ (chartAt ℂ x).source ∧ f x' ∈ (chartAt ℂ y₀).source ∧
      mapAnalyticOrderAt f x' = 1 := ⟨h1, h2, h3⟩
  unfold localBranch
  rw [dif_pos h]
  obtain ⟨a, b, c, d, -⟩ := (exists_local_branch hf h.1 h.2.1 h.2.2).choose_spec
  exact ⟨a, b, c, d⟩

namespace TraceChartData

variable {y₀ : Y} (D : TraceChartData (f := f) hfin y₀) (η : HolomorphicOneForm ℂ X)

/-- Local primitive of `η` in the chart at `x`, based at the chart image of `x`. -/
noncomputable def H (x : X) : ℂ → ℂ :=
  fun z => ∫ᶜ t in Path.segment (chartAt ℂ x x) z, chartForm x η t

/-- The part of the fibre over `c_q⁻¹ w` lying in `U x`. -/
noncomputable def S (w : ℂ) (x : X) : Finset X :=
  (fiberFin hfin ((chartAt ℂ y₀).symm w)).filter (· ∈ D.U x)

/-- **The local trace of the primitives**, in the chart at `y₀`. -/
noncomputable def trH (w : ℂ) : ℂ :=
  ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w x, (mapAnalyticOrderAt f x' : ℂ) * H η x (chartAt ℂ x x')

/-- A point is *good* if, near it, every fibre meets each `U x` in `m(x)` unramified points. -/
def Good (w : ℂ) : Prop :=
  ∀ x ∈ fiberFin hfin y₀, (D.S w x).card = mapAnalyticOrderAt f x ∧
    ∀ x' ∈ D.S w x, mapAnalyticOrderAt f x' = 1

include hf in
/-- **Near a good point, `Tr H` is a sum of primitives composed with inverse branches.** -/
theorem trH_eventuallyEq {w₁ : ℂ} (hw₁ : w₁ ∈ ball (chartAt ℂ y₀ y₀) D.ρ)
    (hgood : ∀ᶠ w in 𝓝 w₁, D.Good w) :
    D.trH η =ᶠ[𝓝 w₁] fun w => ∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w₁ x,
      H η x (localBranch hf y₀ x x' w) := by
  set cq := chartAt ℂ y₀
  have hw₁t : w₁ ∈ cq.target := D.ball_sub hw₁
  -- facts about each branch, eventually in `w`
  have hpair : ∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ D.S w₁ x,
      (∀ᶠ w in 𝓝 w₁,
        chartMap f x y₀ (localBranch hf y₀ x x' w) = w ∧
        localBranch hf y₀ x x' w ∈ (chartAt ℂ x).target ∧
        (chartAt ℂ x).symm (localBranch hf y₀ x x' w) ∈ D.U x ∧
        f ((chartAt ℂ x).symm (localBranch hf y₀ x x' w)) ∈ cq.source) ∧
      Filter.Tendsto (fun w => (chartAt ℂ x).symm (localBranch hf y₀ x x' w)) (𝓝 w₁) (𝓝 x') := by
    intro x hx x' hx'
    have hx'f : f x' = cq.symm w₁ := ((mem_fiberFin hfin).mp (Finset.mem_filter.mp hx').1)
    have hx'U : x' ∈ D.U x := (Finset.mem_filter.mp hx').2
    have h1 : x' ∈ (chartAt ℂ x).source := D.U_sub_source x hx hx'U
    have h2 : f x' ∈ cq.source := by rw [hx'f]; exact cq.map_target hw₁t
    have h3 : mapAnalyticOrderAt f x' = 1 := (hgood.self_of_nhds x hx).2 x' hx'
    obtain ⟨hg0, hgan, -, hgright⟩ := localBranch_spec hf h1 h2 h3
    have hφ : chartMap f x y₀ (chartAt ℂ x x') = w₁ := by
      show cq (f ((chartAt ℂ x).symm (chartAt ℂ x x'))) = w₁
      rw [(chartAt ℂ x).left_inv h1, hx'f, cq.right_inv hw₁t]
    rw [hφ] at hg0 hgan hgright
    have hgcont : Filter.Tendsto (localBranch hf y₀ x x') (𝓝 w₁) (𝓝 (chartAt ℂ x x')) := by
      have := hgan.continuousAt.tendsto; rwa [hg0] at this
    have hsymm : Filter.Tendsto (fun w => (chartAt ℂ x).symm (localBranch hf y₀ x x' w)) (𝓝 w₁)
        (𝓝 x') := by
      have := ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source h1)).tendsto.comp hgcont
      rwa [(chartAt ℂ x).left_inv h1] at this
    refine ⟨?_, hsymm⟩
    filter_upwards [hgright, hgcont.eventually ((chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source h1)), hsymm.eventually ((D.U_open x).mem_nhds hx'U),
      (hf.continuous.tendsto x' |>.comp hsymm).eventually (cq.open_source.mem_nhds h2)]
      with w ha hb hc hd
    exact ⟨ha, hb, hc, hd⟩
  -- distinct fibre points have eventually distinct branches
  have hdist : ∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ D.S w₁ x, ∀ x'' ∈ D.S w₁ x, x' ≠ x'' →
      ∀ᶠ w in 𝓝 w₁, (chartAt ℂ x).symm (localBranch hf y₀ x x' w) ≠
        (chartAt ℂ x).symm (localBranch hf y₀ x x'' w) := by
    intro x hx x' hx' x'' hx'' hne
    obtain ⟨N₁, N₂, hN₁, hN₂, h₁, h₂, hdisj⟩ := t2_separation hne
    filter_upwards [(hpair x hx x' hx').2.eventually (hN₁.mem_nhds h₁),
      (hpair x hx x'' hx'').2.eventually (hN₂.mem_nhds h₂)] with w ha hb heq
    exact Set.disjoint_left.mp hdisj ha (heq ▸ hb)
  have hall : ∀ᶠ w in 𝓝 w₁, D.Good w ∧
      (∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ D.S w₁ x,
        chartMap f x y₀ (localBranch hf y₀ x x' w) = w ∧
        localBranch hf y₀ x x' w ∈ (chartAt ℂ x).target ∧
        (chartAt ℂ x).symm (localBranch hf y₀ x x' w) ∈ D.U x ∧
        f ((chartAt ℂ x).symm (localBranch hf y₀ x x' w)) ∈ cq.source) ∧
      (∀ x ∈ fiberFin hfin y₀, ∀ x' ∈ D.S w₁ x, ∀ x'' ∈ D.S w₁ x, x' ≠ x'' →
        (chartAt ℂ x).symm (localBranch hf y₀ x x' w) ≠
          (chartAt ℂ x).symm (localBranch hf y₀ x x'' w)) := by
    refine hgood.and (Filter.Eventually.and ?_ ?_)
    · rw [Finset.eventually_all]; intro x hx
      rw [Finset.eventually_all]; intro x' hx'
      exact (hpair x hx x' hx').1
    · rw [Finset.eventually_all]; intro x hx
      rw [Finset.eventually_all]; intro x' hx'
      rw [Finset.eventually_all]; intro x'' hx''
      by_cases hne : x' = x''
      · exact Filter.Eventually.of_forall fun _ h => absurd hne h
      · exact (hdist x hx x' hx' x'' hx'' hne).mono fun _ h _ => h
  filter_upwards [hall, isOpen_ball.mem_nhds hw₁] with w ⟨hG, hP, hD⟩ hwball
  have hwt : w ∈ cq.target := D.ball_sub hwball
  unfold trH
  refine Finset.sum_congr rfl fun x hx => ?_
  set P : X → X := fun x' => (chartAt ℂ x).symm (localBranch hf y₀ x x' w)
  have hPmem : ∀ x' ∈ D.S w₁ x, P x' ∈ D.S w x := by
    intro x' hx'
    obtain ⟨ha, -, hc, hd⟩ := hP x hx x' hx'
    refine Finset.mem_filter.mpr ⟨(mem_fiberFin hfin).mpr ?_, hc⟩
    have : cq (f (P x')) = w := ha
    rw [← this, cq.left_inv hd]
  have hinj : Set.InjOn P (D.S w₁ x) := by
    intro x' hx' x'' hx'' heq
    by_contra hne
    exact hD x hx x' hx' x'' hx'' hne heq
  have himage : (D.S w₁ x).image P = D.S w x := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hz
      exact hPmem x' hx'
    · rw [Finset.card_image_of_injOn hinj, (hG x hx).1,
        ((hgood.self_of_nhds) x hx).1]
  rw [← himage, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun x' hx' => ?_
  have hm : mapAnalyticOrderAt f (P x') = 1 := (hG x hx).2 _ (hPmem x' hx')
  rw [hm, Nat.cast_one, one_mul]
  show H η x (chartAt ℂ x ((chartAt ℂ x).symm (localBranch hf y₀ x x' w))) = _
  rw [(chartAt ℂ x).right_inv (hP x hx x' hx').2.1]

include hf in
/-- The derivative of `Tr H` at a good point. -/
theorem trH_hasDerivAt {w₁ : ℂ} (hw₁ : w₁ ∈ ball (chartAt ℂ y₀ y₀) D.ρ)
    (hgood : ∀ᶠ w in 𝓝 w₁, D.Good w) :
    HasDerivAt (D.trH η) (∑ x ∈ fiberFin hfin y₀, ∑ x' ∈ D.S w₁ x,
      chartForm x η (chartAt ℂ x x') ((deriv (chartMap f x y₀) (chartAt ℂ x x'))⁻¹)) w₁ := by
  set cq := chartAt ℂ y₀
  have hw₁t : w₁ ∈ cq.target := D.ball_sub hw₁
  refine HasDerivAt.congr_of_eventuallyEq ?_ (D.trH_eventuallyEq hf η hw₁ hgood)
  refine HasDerivAt.fun_sum fun x hx => HasDerivAt.fun_sum fun x' hx' => ?_
  have hx'f : f x' = cq.symm w₁ := ((mem_fiberFin hfin).mp (Finset.mem_filter.mp hx').1)
  have hx'U : x' ∈ D.U x := (Finset.mem_filter.mp hx').2
  have h1 : x' ∈ (chartAt ℂ x).source := D.U_sub_source x hx hx'U
  have h2 : f x' ∈ cq.source := by rw [hx'f]; exact cq.map_target hw₁t
  have h3 : mapAnalyticOrderAt f x' = 1 := (hgood.self_of_nhds x hx).2 x' hx'
  obtain ⟨hg0, -, hgd, -⟩ := localBranch_spec hf h1 h2 h3
  have hφ : chartMap f x y₀ (chartAt ℂ x x') = w₁ := by
    show cq (f ((chartAt ℂ x).symm (chartAt ℂ x x'))) = w₁
    rw [(chartAt ℂ x).left_inv h1, hx'f, cq.right_inv hw₁t]
  rw [hφ] at hg0 hgd
  have hball : chartAt ℂ x x' ∈ ball (chartAt ℂ x x) (D.r x) := D.U_sub_ball x hx x' hx'U
  have hH : HasFDerivAt (H η x) (chartForm x η (chartAt ℂ x x'))
      (localBranch hf y₀ x x' w₁) := by
    rw [hg0]; exact chartForm_hasFDerivAt_primitive x η (D.ballX_sub x hx) hball
  exact hH.comp_hasDerivAt w₁ hgd

/-- Every point of the punctured ball is good. -/
theorem good_of_ne {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ) (hne : w ≠ chartAt ℂ y₀ y₀) :
    D.Good w := fun x hx => D.kfold w hw hne x hx

theorem eventually_good_of_ne {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ)
    (hne : w ≠ chartAt ℂ y₀ y₀) : ∀ᶠ w' in 𝓝 w, D.Good w' := by
  filter_upwards [isOpen_ball.mem_nhds hw, isOpen_compl_singleton.mem_nhds hne] with w' h1 h2
  exact D.good_of_ne h1 h2

/-- Over the centre, `U x` meets the fibre only in `x`. -/
theorem S_center (x : X) (hx : x ∈ fiberFin hfin y₀) :
    D.S (chartAt ℂ y₀ y₀) x = {x} := by
  ext x'
  simp only [S, Finset.mem_filter, mem_fiberFin, Finset.mem_singleton,
    (chartAt ℂ y₀).left_inv (mem_chart_source ℂ y₀)]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have hx' : x' ∈ fiberFin hfin y₀ := (mem_fiberFin hfin).mpr h1
    exact Set.disjoint_left.mp (D.disj x hx x' hx' (Ne.symm hne)) h2 (D.mem_U x' hx')
  · rintro rfl
    exact ⟨(mem_fiberFin hfin).mp hx, D.mem_U _ hx⟩

theorem r_pos {x : X} (hx : x ∈ fiberFin hfin y₀) : 0 < D.r x :=
  pos_of_mem_ball (D.U_sub_ball x hx x (D.mem_U x hx))

/-- The value of `Tr H` at the centre: `Σ_x m(x) H_x(c_x x)`. -/
theorem trH_center :
    D.trH η (chartAt ℂ y₀ y₀) =
      ∑ x ∈ fiberFin hfin y₀, (mapAnalyticOrderAt f x : ℂ) * H η x (chartAt ℂ x x) := by
  unfold trH
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [D.S_center x hx, Finset.sum_singleton]

include hf in
/-- **Continuity of `Tr H` at the centre**: as `w → c_q y₀`, the fibre points in `U x`
collapse onto `x`. -/
theorem trH_continuousAt_center (hnc : ¬ ∃ y₁ : Y, ∀ x, f x = y₁) :
    ContinuousAt (D.trH η) (chartAt ℂ y₀ y₀) := by
  set cq := chartAt ℂ y₀
  set w₀ := cq y₀
  set F0 := fiberFin hfin y₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set d : ℕ := ∑ x ∈ F0, mapAnalyticOrderAt f x
  set ε' : ℝ := ε / (d + 1)
  have hε' : 0 < ε' := by positivity
  have hcont : ∀ x ∈ F0, ContinuousAt (fun x' => H η x (chartAt ℂ x x')) x := by
    intro x hx
    have hc : chartAt ℂ x x ∈ ball (chartAt ℂ x x) (D.r x) := mem_ball_self (D.r_pos hx)
    exact (chartForm_hasFDerivAt_primitive x η (D.ballX_sub x hx) hc).continuousAt.comp
      ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  have hloc : ∀ x ∈ F0, ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
      ∀ y ∈ V, y ≠ y₀ → ∃ t : Finset X, t.card = mapAnalyticOrderAt f x ∧ ↑t ⊆ D.U x ∧
        (∀ x' ∈ t, f x' = y ∧ dist (H η x (chartAt ℂ x x')) (H η x (chartAt ℂ x x)) < ε') := by
    intro x hx
    obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp
      ((hcont x hx).preimage_mem_nhds (ball_mem_nhds (H η x (chartAt ℂ x x)) hε'))
    obtain ⟨U', -, hxU', hU'sub, V, hVopen, hfxV, hV⟩ :=
      local_kfold_ramified_of_contMDiff_within hf (hOopen.inter (D.U_open x)) ⟨hxO, D.mem_U x hx⟩
        (mapAnalyticOrderAt_pos_of_contMDiff hf hnc x) rfl
    have hfx : f x = y₀ := (mem_fiberFin hfin).mp hx
    refine ⟨V, hVopen, hfx ▸ hfxV, fun y hy hne => ?_⟩
    obtain ⟨t, htc, htU, htp, -⟩ := hV y hy (hfx ▸ hne)
    exact ⟨t, htc, fun z hz => (hU'sub (htU hz)).2, fun x' hx' =>
      ⟨(htp x' hx').1, hOsub (hU'sub (htU hx')).1⟩⟩
  choose V hVo hy₀V hVprop using hloc
  have hw₀t : w₀ ∈ cq.target := cq.map_source (mem_chart_source ℂ y₀)
  have hsymm_w₀ : cq.symm w₀ = y₀ := cq.left_inv (mem_chart_source ℂ y₀)
  have hev : ∀ᶠ w in 𝓝 w₀, ∀ x ∈ F0, ∀ hx : x ∈ F0, cq.symm w ∈ V x hx := by
    rw [Finset.eventually_all]
    intro x hx
    have := (cq.continuousAt_symm hw₀t).preimage_mem_nhds
      ((hVo x hx).mem_nhds (hsymm_w₀ ▸ hy₀V x hx))
    filter_upwards [this] with w hw _
    exact hw
  filter_upwards [hev, isOpen_ball.mem_nhds (mem_ball_self D.ρ_pos)] with w hw hwball
  by_cases hww : w = w₀
  · rw [hww, dist_self]; exact hε
  have hwt : w ∈ cq.target := D.ball_sub hwball
  have hyne : cq.symm w ≠ y₀ := by
    intro h; apply hww
    rw [← cq.right_inv hwt, h]
  have hgood := D.good_of_ne hwball hww
  -- each `S w x` is the small finset `t`
  have hS : ∀ x (hx : x ∈ F0), ∀ x' ∈ D.S w x,
      dist (H η x (chartAt ℂ x x')) (H η x (chartAt ℂ x x)) < ε' := by
    intro x hx
    obtain ⟨t, htc, htU, htp⟩ := hVprop x hx (cq.symm w) (hw x hx hx) hyne
    have htS : t ⊆ D.S w x := fun z hz =>
      Finset.mem_filter.mpr ⟨(mem_fiberFin hfin).mpr (htp z hz).1, htU hz⟩
    have heq : t = D.S w x := Finset.eq_of_subset_of_card_le htS (by rw [htc, (hgood x hx).1])
    intro x' hx'
    exact (htp x' (heq ▸ hx')).2
  rw [D.trH_center, dist_eq_norm]
  unfold trH
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ x ∈ F0, ‖∑ x' ∈ D.S w x, (mapAnalyticOrderAt f x' : ℂ) * H η x (chartAt ℂ x x') -
      (mapAnalyticOrderAt f x : ℂ) * H η x (chartAt ℂ x x)‖ ≤ mapAnalyticOrderAt f x * ε' := by
    intro x hx
    have hm : ∀ x' ∈ D.S w x, (mapAnalyticOrderAt f x' : ℂ) = 1 := fun x' hx' => by
      rw [(hgood x hx).2 x' hx']; simp
    rw [Finset.sum_congr rfl (fun x' hx' => by rw [hm x' hx', one_mul])]
    have hcard : (mapAnalyticOrderAt f x : ℂ) = ((D.S w x).card : ℂ) := by rw [(hgood x hx).1]
    rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
    calc ‖∑ x' ∈ D.S w x, (H η x (chartAt ℂ x x') - H η x (chartAt ℂ x x))‖
        ≤ ∑ x' ∈ D.S w x, ‖H η x (chartAt ℂ x x') - H η x (chartAt ℂ x x)‖ := norm_sum_le _ _
      _ ≤ ∑ x' ∈ D.S w x, ε' := Finset.sum_le_sum fun x' hx' => by
          rw [← dist_eq_norm]; exact (hS x hx x' hx').le
      _ = mapAnalyticOrderAt f x * ε' := by rw [Finset.sum_const, nsmul_eq_mul, (hgood x hx).1]
  calc ‖∑ x ∈ F0, (∑ x' ∈ D.S w x, (mapAnalyticOrderAt f x' : ℂ) * H η x (chartAt ℂ x x') -
        (mapAnalyticOrderAt f x : ℂ) * H η x (chartAt ℂ x x))‖
      ≤ ∑ x ∈ F0, ‖∑ x' ∈ D.S w x, (mapAnalyticOrderAt f x' : ℂ) * H η x (chartAt ℂ x x') -
        (mapAnalyticOrderAt f x : ℂ) * H η x (chartAt ℂ x x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ F0, (mapAnalyticOrderAt f x : ℝ) * ε' := Finset.sum_le_sum hterm
    _ = d * ε' := by rw [← Finset.sum_mul]; push_cast [d]; ring
    _ < ε := by
      have : (d : ℝ) * ε' = ε * (d / (d + 1)) := by simp only [ε']; field_simp
      rw [this]
      have h1 : (d : ℝ) / (d + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith

include hf in
/-- **`Tr H` is holomorphic on the whole ball** (removable singularity at the centre). -/
theorem trH_differentiableOn (hnc : ¬ ∃ y₁ : Y, ∀ x, f x = y₁) :
    DifferentiableOn ℂ (D.trH η) (ball (chartAt ℂ y₀ y₀) D.ρ) := by
  have hoff : ∀ w ∈ ball (chartAt ℂ y₀ y₀) D.ρ, w ≠ chartAt ℂ y₀ y₀ →
      DifferentiableAt ℂ (D.trH η) w := fun w hw hne =>
    (D.trH_hasDerivAt hf η hw (D.eventually_good_of_ne hw hne)).differentiableAt
  intro w hw
  by_cases hne : w = chartAt ℂ y₀ y₀
  · subst hne
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
      (D.trH_continuousAt_center hf η hnc)).differentiableAt.differentiableWithinAt
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hw), self_mem_nhdsWithin]
      with w' h1 h2
    exact hoff w' h1 h2
  · exact (hoff w hw hne).differentiableWithinAt

end TraceChartData

end TraceH

section Global

attribute [local instance] Classical.propDecidable

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y]
  (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hnc : ¬ ∃ y₁ : Y, ∀ x, f x = y₁)
  (η : HolomorphicOneForm ℂ X)

/-- The chosen local trace data at `y`. -/
noncomputable def chosenData (y : Y) : TraceChartData (f := f) hfin y :=
  Classical.choice (exists_traceChartData hf hfin hnc y)

variable (f) in
/-- `y` is unramified: every fibre point has local order `1`. -/
def Unram (y : Y) : Prop := ∀ x, f x = y → mapAnalyticOrderAt f x = 1

/-- The fibre-sum trace `Σ_{f x = y} η_x ∘ (df_x)⁻¹` at `y`. -/
noncomputable def fiberTrace (y : Y) : CotangentSpace ℂ Y y :=
  ∑ x ∈ fiberFin hfin y, (cotangentPushforward f x (η.toFun x) : CotangentSpace ℂ Y y)

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem toLc_sum {ι : Type*} {y : Y} (s : Finset ι) (g : ι → CotangentSpace ℂ Y y) (v : ℂ) :
    toLc (∑ i ∈ s, g i) v = ∑ i ∈ s, toLc (g i) v :=
  ContinuousLinearMap.sum_apply s g v

/-- The covector at `y` whose reading in the chart at `y` is `a`. -/
noncomputable def coordCovector (y : Y) (a : ℂ) : CotangentSpace ℂ Y y :=
  (a • ContinuousLinearMap.id ℂ ℂ).comp (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y) y))

/--
**The trace of `η`**: the fibre sum at unramified values; at the (finitely many) branch
values, the derivative of the local trace of primitives `Tr H` in the chart at that value.
-/
noncomputable def traceSection (y : Y) : CotangentSpace ℂ Y y :=
  if Unram f y then fiberTrace hfin η y
  else coordCovector y (deriv ((chosenData hf hfin hnc y).trH η) (chartAt ℂ y y))

omit [IsManifold 𝓘(ℂ) ω X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] in
theorem coordCovector_read (y : Y) (a : ℂ) :
    toLc (coordCovector y a)
      (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y).symm (chartAt ℂ y y)) 1) = a := by
  set C := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y) y)
  set C' := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y).symm (chartAt ℂ y y))
  have hCC' : C' (C 1) = 1 :=
    congrArg (fun L => L (1 : ℂ)) (mfderiv_chartAt_symm_comp_self y (mem_chart_source ℂ y))
  show a • C (C' 1) = a
  rw [clm_apply_eq_mul C, smul_eq_mul]
  rw [clm_apply_eq_mul C'] at hCC'
  rw [mul_comm (C' 1), hCC', mul_one]

namespace TraceChartData

variable {hfin} {y₀ : Y} (D : TraceChartData (f := f) hfin y₀)

theorem unram_of_ne {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ) (hne : w ≠ chartAt ℂ y₀ y₀) :
    Unram f ((chartAt ℂ y₀).symm w) := by
  intro x' hx'
  obtain ⟨x, hx, hU⟩ := D.cover w hw x' hx'
  exact (D.kfold w hw hne x hx).2 x' (Finset.mem_filter.mpr ⟨(mem_fiberFin hfin).mpr hx', hU⟩)

theorem good_center (hu : Unram f y₀) : D.Good (chartAt ℂ y₀ y₀) := by
  intro x hx
  have h1 : mapAnalyticOrderAt f x = 1 := hu x ((mem_fiberFin hfin).mp hx)
  rw [D.S_center x hx]
  refine ⟨by rw [Finset.card_singleton, h1], fun x' hx' => ?_⟩
  rw [Finset.mem_singleton.mp hx']; exact h1

include hf in
/-- **Chart reading of the fibre-sum trace** at a good point: it is the derivative of
`Tr H`. -/
theorem fiberTrace_read {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ)
    (hgood : ∀ᶠ w' in 𝓝 w, D.Good w') :
    toLc (fiberTrace hfin η ((chartAt ℂ y₀).symm w))
        (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y₀).symm w) 1) = deriv (D.trH η) w := by
  set cq := chartAt ℂ y₀
  have hwt : w ∈ cq.target := D.ball_sub hw
  rw [(D.trH_hasDerivAt hf η hw hgood).deriv]
  have hdecomp : fiberFin hfin (cq.symm w) = (fiberFin hfin y₀).biUnion (D.S w) := by
    ext x'
    simp only [S, Finset.mem_biUnion, Finset.mem_filter, mem_fiberFin]
    constructor
    · intro h
      obtain ⟨x, hx, hU⟩ := D.cover w hw x' h
      exact ⟨x, (mem_fiberFin hfin).mp hx, h, hU⟩
    · rintro ⟨x, -, h, -⟩; exact h
  have hdisj : (fiberFin hfin y₀ : Set X).PairwiseDisjoint (D.S w) := by
    intro x hx x₂ hx₂ hne
    refine Finset.disjoint_left.mpr fun x' h1 h2 => ?_
    exact Set.disjoint_left.mp (D.disj x hx x₂ hx₂ hne) (Finset.mem_filter.mp h1).2
      (Finset.mem_filter.mp h2).2
  unfold fiberTrace
  rw [toLc_sum, hdecomp, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun x' hx' => ?_
  have hx'f : f x' = cq.symm w := ((mem_fiberFin hfin).mp (Finset.mem_filter.mp hx').1)
  have hx'U : x' ∈ D.U x := (Finset.mem_filter.mp hx').2
  have h1 : x' ∈ (chartAt ℂ x).source := D.U_sub_source x hx hx'U
  have h2 : f x' ∈ cq.source := by rw [hx'f]; exact cq.map_target hwt
  have h3 : mapAnalyticOrderAt f x' = 1 := (hgood.self_of_nhds x hx).2 x' hx'
  have hd := chartMap_deriv_ne_zero_of_unramified hf h1 h2 h3
  have key := cotangentPushforward_chart hf x y₀ h1 h2 hd (η.toFun x')
  have hw' : cq (f x') = w := by rw [hx'f, cq.right_inv hwt]
  rw [hw'] at key
  refine key.trans ?_
  have aux : ∀ p : X, p = x' → ∀ v : ℂ,
      toLc (η.toFun x') (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm (chartAt ℂ x x')) v) =
        toLc (η.toFun p) (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ x).symm (chartAt ℂ x x')) v) := by
    rintro p rfl v; rfl
  exact aux _ ((chartAt ℂ x).left_inv h1) _

/-- Over the ball, the fibre is the disjoint union of its pieces `S w x`. -/
theorem fiberFin_eq_biUnion {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ) :
    fiberFin hfin ((chartAt ℂ y₀).symm w) = (fiberFin hfin y₀).biUnion (D.S w) := by
  ext x'
  simp only [S, Finset.mem_biUnion, Finset.mem_filter, mem_fiberFin]
  constructor
  · intro h
    obtain ⟨x, hx, hU⟩ := D.cover w hw x' h
    exact ⟨x, (mem_fiberFin hfin).mp hx, h, hU⟩
  · rintro ⟨x, -, h, -⟩; exact h

theorem S_pairwiseDisjoint (w : ℂ) : (fiberFin hfin y₀ : Set X).PairwiseDisjoint (D.S w) := by
  intro x hx x₂ hx₂ hne
  refine Finset.disjoint_left.mpr fun x' h1 h2 => ?_
  exact Set.disjoint_left.mp (D.disj x hx x₂ hx₂ hne) (Finset.mem_filter.mp h1).2
    (Finset.mem_filter.mp h2).2

/-- **Local degree is constant**: over every point of the ball, the fibre points in `U x`,
counted with multiplicity, number `m(x)`. -/
theorem sum_order_S {w : ℂ} (hw : w ∈ ball (chartAt ℂ y₀ y₀) D.ρ) {x : X}
    (hx : x ∈ fiberFin hfin y₀) :
    ∑ x' ∈ D.S w x, mapAnalyticOrderAt f x' = mapAnalyticOrderAt f x := by
  by_cases hne : w = chartAt ℂ y₀ y₀
  · subst hne
    rw [D.S_center x hx, Finset.sum_singleton]
  · obtain ⟨hcard, hone⟩ := D.kfold w hw hne x hx
    have h1 : ∑ x' ∈ D.S w x, mapAnalyticOrderAt f x' = ∑ _x' ∈ D.S w x, 1 :=
      Finset.sum_congr rfl hone
    rw [h1, Finset.sum_const, smul_eq_mul, mul_one]
    exact hcard

end TraceChartData

include hf in
/-- **Chart reading of the trace** near `y₀`, in the chart at `y₀`: it is the derivative of
the local trace of primitives `Tr H` for the chosen data at `y₀`. -/
theorem traceSection_read (y₀ : Y) {w : ℂ}
    (hw : w ∈ ball (chartAt ℂ y₀ y₀) (chosenData hf hfin hnc y₀).ρ) :
    toLc (traceSection hf hfin hnc η ((chartAt ℂ y₀).symm w))
        (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ y₀).symm w) 1) =
      deriv ((chosenData hf hfin hnc y₀).trH η) w := by
  set D := chosenData hf hfin hnc y₀
  set cq := chartAt ℂ y₀
  by_cases hu : Unram f (cq.symm w)
  · unfold traceSection
    rw [if_pos hu]
    refine D.fiberTrace_read hf η hw ?_
    by_cases hne : w = cq y₀
    · subst hne
      have hu₀ : Unram f y₀ := by rwa [cq.left_inv (mem_chart_source ℂ y₀)] at hu
      filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
      by_cases h : w' = cq y₀
      · rw [h]; exact D.good_center hu₀
      · exact D.good_of_ne hw' h
    · exact D.eventually_good_of_ne hw hne
  · have hne : w = cq y₀ := by
      by_contra hne; exact hu (D.unram_of_ne hw hne)
    subst hne
    have hu₀ : ¬ Unram f y₀ := by rwa [cq.left_inv (mem_chart_source ℂ y₀)] at hu
    have aux : ∀ y : Y, y = y₀ →
        toLc (traceSection hf hfin hnc η y) (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq.symm (cq y₀)) 1) =
          deriv (D.trH η) (cq y₀) := by
      rintro y rfl
      unfold traceSection
      rw [if_neg hu₀]
      exact coordCovector_read y _
    exact aux _ (cq.left_inv (mem_chart_source ℂ y₀))

/-- The cotangent trivialization at `p₀` reads a covector `s b` as `s b ∘ symmL`. -/
theorem trivCT_read_eq_comp_symmL (s : ∀ y : Y, CotangentSpace ℂ Y y) (p₀ b : Y) :
    ((trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ Y) p₀) ⟨b, s b⟩).snd =
      (s b).comp ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) p₀).symmL ℂ b) := by
  rw [show (trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ Y) p₀) =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) p₀).continuousLinearMap
          (RingHom.id ℂ) (trivializationAt ℂ (Bundle.Trivial Y ℂ) p₀) from rfl,
      Bundle.Trivialization.continuousLinearMap_apply]
  have hTrivial :
      (trivializationAt ℂ (Bundle.Trivial Y ℂ) p₀).continuousLinearMapAt ℂ b =
        ContinuousLinearMap.id ℂ ℂ := by
    have heq : trivializationAt ℂ (Bundle.Trivial Y ℂ) p₀ = Bundle.Trivial.trivialization Y ℂ :=
      Bundle.Trivial.eq_trivialization Y ℂ (trivializationAt ℂ (Bundle.Trivial Y ℂ) p₀)
    have h₀ : (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ b =
        ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ Y ℂ b
    have hbridge : (trivializationAt ℂ (Bundle.Trivial Y ℂ) p₀).continuousLinearMapAt ℂ b =
        (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ b := by
      congr 1
    exact hbridge.trans h₀
  rw [hTrivial]
  rfl

include hf in
/-- **The trace is a holomorphic section of the cotangent bundle.** -/
theorem traceSection_contMDiff :
    ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) (⊤ : WithTop ℕ∞)
      (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (traceSection hf hfin hnc η y)) := by
  intro y₀
  set D := chosenData hf hfin hnc y₀
  set cq := chartAt ℂ y₀
  set triv := trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace ℂ Y) y₀
  have hb : y₀ ∈ triv.baseSet := FiberBundle.mem_baseSet_trivializationAt' y₀
  rw [triv.contMDiffAt_section_iff hb]
  have hc : cq y₀ ∈ ball (cq y₀) D.ρ := mem_ball_self D.ρ_pos
  have hdiff := D.trH_differentiableOn hf η hnc
  have han : AnalyticAt ℂ (deriv (D.trH η)) (cq y₀) :=
    ((hdiff.analyticOnNhd isOpen_ball) _ hc).deriv
  have hG : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun a : ℂ => deriv (D.trH η) a • ContinuousLinearMap.id ℂ ℂ) (cq y₀) :=
    (han.smul analyticAt_const).contDiffAt
  have hF : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y => deriv (D.trH η) (cq y) • ContinuousLinearMap.id ℂ ℂ) y₀ :=
    hG.comp_contMDiffAt ((contMDiffOn_chart (I := 𝓘(ℂ, ℂ)) (x := y₀)).contMDiffAt
      (cq.open_source.mem_nhds (mem_chart_source ℂ y₀)))
  have hread : ∀ e ∈ ball (cq y₀) D.ρ,
      (triv ⟨cq.symm e, traceSection hf hfin hnc η (cq.symm e)⟩).2 =
        deriv (D.trH η) e • ContinuousLinearMap.id ℂ ℂ := by
    intro e he
    have het : e ∈ cq.target := D.ball_sub he
    rw [trivCT_read_eq_comp_symmL, ← Periods.ChartedFormPullbackContinuous.mfderiv_chartSymm_eq_symmL y₀ het]
    refine ContinuousLinearMap.ext fun v => ?_
    have h := clm_apply_eq_mul ((toLc (traceSection hf hfin hnc η (cq.symm e))).comp
      (toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq.symm e))) v
    refine h.trans ?_
    rw [ContinuousLinearMap.comp_apply, traceSection_read hf hfin hnc η y₀ he]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm _ _
  have heq : (fun y => (triv ⟨y, traceSection hf hfin hnc η y⟩).2) =ᶠ[𝓝 y₀]
      (fun y => deriv (D.trH η) (cq y) • ContinuousLinearMap.id ℂ ℂ) := by
    filter_upwards [cq.open_source.mem_nhds (mem_chart_source ℂ y₀),
      (cq.continuousAt (mem_chart_source ℂ y₀)).preimage_mem_nhds (isOpen_ball.mem_nhds hc)]
      with y hy hyb
    have h := hread (cq y) hyb
    rw [cq.left_inv hy] at h
    exact h
  exact hF.congr_of_eventuallyEq heq

/-- **The trace of a holomorphic 1-form, as a holomorphic 1-form on `Y`.** -/
noncomputable def traceHolomorphicForm : HolomorphicOneForm ℂ Y :=
  ⟨traceSection hf hfin hnc η, traceSection_contMDiff hf hfin hnc η⟩

/-- At an unramified value the trace form is the fibre sum. -/
theorem traceHolomorphicForm_apply_of_unram {y : Y} (hy : Unram f y) :
    (traceHolomorphicForm hf hfin hnc η).toFun y = fiberTrace hfin η y := by
  show traceSection hf hfin hnc η y = _
  unfold traceSection
  rw [if_pos hy]

include hf in
/-- **`Tr H` is a local primitive of the trace form**, read in any chart `p` of `Y`. -/
theorem traceHolomorphicForm_hasFDerivAt (y₀ p : Y) {z : ℂ} (hz : z ∈ (chartAt ℂ p).target)
    (h1 : (chartAt ℂ p).symm z ∈ (chartAt ℂ y₀).source)
    (h2 : chartAt ℂ y₀ ((chartAt ℂ p).symm z) ∈
      ball (chartAt ℂ y₀ y₀) (chosenData hf hfin hnc y₀).ρ) :
    HasFDerivAt (fun z => (chosenData hf hfin hnc y₀).trH η (chartAt ℂ y₀ ((chartAt ℂ p).symm z)))
      (chartForm p (traceHolomorphicForm hf hfin hnc η) z) z := by
  set D := chosenData hf hfin hnc y₀
  set cp := chartAt ℂ p
  set cq := chartAt ℂ y₀
  set y := cp.symm z
  set w := cq y
  have hid : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (id : Y → Y) := contMDiff_id
  have hφd : HasFDerivAt (chartMap (id : Y → Y) p y₀) (fderiv ℂ (chartMap (id : Y → Y) p y₀) z) z :=
    (chartMap_differentiableAt hid hz h1).hasFDerivAt
  have hT : HasDerivAt (D.trH η) (deriv (D.trH η) w) w :=
    (((D.trH_differentiableOn hf η hnc) w h2).differentiableAt
      (isOpen_ball.mem_nhds h2)).hasDerivAt
  have hcomp := hT.hasFDerivAt.comp z hφd
  refine hcomp.congr_fderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  set B := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cp.symm z)
  set C := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq y)
  set C' := toL (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) cq.symm w)
  have hCC' : C' (C 1) = 1 :=
    congrArg (fun L => L (1 : ℂ)) (mfderiv_chartAt_symm_comp_self y₀ h1)
  have hfd : fderiv ℂ (chartMap (id : Y → Y) p y₀) z 1 = C (B 1) := by
    rw [chartMap_fderiv hid hz h1, mfderiv_id]; rfl
  rw [ContinuousLinearMap.comp_apply, hfd, ContinuousLinearMap.toSpanSingleton_apply]
  have hread := traceSection_read hf hfin hnc η y₀ h2
  have aux : ∀ y' : Y, y' = y → ∀ v : ℂ,
      toLc (traceSection hf hfin hnc η y') v = toLc (traceSection hf hfin hnc η y) v := by
    rintro y' rfl v; rfl
  rw [aux _ (cq.left_inv h1)] at hread
  set T := toLc (traceSection hf hfin hnc η y)
  show C (B 1) • deriv (D.trH η) w = T (B 1)
  rw [← hread, smul_eq_mul,
    clm_apply_eq_mul T (C' 1), clm_apply_eq_mul T (B 1), clm_apply_eq_mul C]
  rw [clm_apply_eq_mul C'] at hCC'
  linear_combination (B 1 * T 1) * hCC'

include hf in
/-- **Integral of the trace over a chart segment** of `Y` lying in the domain of `Tr H`:
the difference of `Tr H` at the endpoints. -/
theorem traceHolomorphicForm_segment_eq (y₀ p : Y) {c : ℂ} {ρB : ℝ}
    (hB : ball c ρB ⊆ (chartAt ℂ p).target)
    (hBy : ∀ z ∈ ball c ρB, (chartAt ℂ p).symm z ∈ (chartAt ℂ y₀).source ∧
      chartAt ℂ y₀ ((chartAt ℂ p).symm z) ∈
        ball (chartAt ℂ y₀ y₀) (chosenData hf hfin hnc y₀).ρ)
    {a b : ℂ} (ha : a ∈ ball c ρB) (hb : b ∈ ball c ρB) :
    (∫ᶜ x in Path.segment a b, chartForm p (traceHolomorphicForm hf hfin hnc η) x) =
      (chosenData hf hfin hnc y₀).trH η (chartAt ℂ y₀ ((chartAt ℂ p).symm b)) -
        (chosenData hf hfin hnc y₀).trH η (chartAt ℂ y₀ ((chartAt ℂ p).symm a)) := by
  set τ := traceHolomorphicForm hf hfin hnc η
  set G : ℂ → ℂ := fun z =>
    (chosenData hf hfin hnc y₀).trH η (chartAt ℂ y₀ ((chartAt ℂ p).symm z))
  rw [chartForm_segment_eq_sub p τ hB ha hb]
  set H : ℂ → ℂ := fun w => ∫ᶜ x in Path.segment c w, chartForm p τ x
  have hD : ∀ w ∈ ball c ρB, HasFDerivAt (fun w => H w - G w) (0 : ℂ →L[ℂ] ℂ) w := by
    intro w hw
    have hH : HasFDerivAt H (chartForm p τ w) w := chartForm_hasFDerivAt_primitive p τ hB hw
    have hG : HasFDerivAt G (chartForm p τ w) w :=
      traceHolomorphicForm_hasFDerivAt hf hfin hnc η y₀ p (hB hw) (hBy w hw).1 (hBy w hw).2
    have h := hH.sub hG
    rwa [sub_self] at h
  have hconst := (convex_ball c ρB).is_const_of_fderivWithin_eq_zero
    (f := fun w => H w - G w) (𝕜 := ℂ)
    (fun w hw => (hD w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by
      rw [fderivWithin_of_isOpen isOpen_ball hw]
      exact (hD w hw).fderiv) hb ha
  show H b - H a = G b - G a
  linear_combination hconst

end Global

end JacobianChallenge.HolomorphicForms
