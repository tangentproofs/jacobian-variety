/-!
# RETIRED — not built, not imported

Declarations moved verbatim out of `Jacobian/HolomorphicForms/TraceSpec.lean` on branch `independent-repair`
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

omit [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Provider (1).** *Trace holomorphic on the regular locus.* At
every regular value `y` of `hbc`, the local trace function
`localTraceAtRegularValue` (a chart-local realization of the finite
fibre sum, defined in a neighbourhood of `y`) is holomorphic at `y`.

Mathematically: at a regular value `y`, every preimage `x ∈ f⁻¹(y)`
is unramified, so `f` has a holomorphic local inverse near `y`, and
the cotangent pushforward of `η` along this inverse is locally
holomorphic. Summing finitely many holomorphic functions gives a
holomorphic function.
-/
theorem traceAtRegularValue_locally_holomorphic_on_regular_locus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y : Y) (hy : isRegularValue hbc y) :
    IsHolomorphicAt (localTraceAtRegularValue hbc
      (isHolomorphic_of_contMDiff hf
        (hasLocalKfoldRamification_of_contMDiff hf)) η y hy) y :=
  localTraceAtRegularValue_holomorphic hbc hcompat
    (isHolomorphic_of_contMDiff hf
      (hasLocalKfoldRamification_of_contMDiff hf)) η y hy

omit [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Strictly narrower fiber-point helper (Provider 2 internal),
unramified leaf.** When `x₀` is unramified (ramification index 1),
the local inverse of `f` near `x₀` makes the partial sum over
preimages of `y` in `W₀ ∩ U₀` a single term, equal to the
holomorphic function `localPullbackAt hbc hHol η x₀ hx₀_ram y`.
Boundedness on a small `Y`-nhd of `y₀` follows from
continuity at `y₀`.
-/
private theorem unramifiedFiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (hx₀_ram : hbc.ramificationIndex x₀ = 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  classical
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  -- Step 1: extract local bijection (U₀, V₀).
  obtain ⟨U₀, V₀, hU₀_open, hV₀_open, hxU₀, hfxV₀, hbij, hright, hleft⟩ :=
    hbc.localInverse_is_inverse hx₀_ram
  -- Step 2: W := W₀ ∩ U₀: open, x₀ ∈ W, W ⊆ W₀ and W ⊆ U₀.
  set W : Set X := W₀ ∩ U₀ with hW_def
  have hW_open : IsOpen W := hW₀_open.inter hU₀_open
  have hxW : x₀ ∈ W := ⟨hxW₀, hxU₀⟩
  have hW_sub_W₀ : W ⊆ W₀ := fun _ h => h.1
  have hW_sub_U₀ : W ⊆ U₀ := fun _ h => h.2
  -- Step 3: localInverseAt preimage of W is a Y-nhd of f x₀ = y₀.
  have hWpre_nhd : hbc.localInverseAt x₀ hx₀_ram ⁻¹' W ∈ 𝓝 (f x₀) :=
    localInverseAt_preimage_mem_nhds hbc hcompat hHol x₀ hx₀_ram hW_open hxW
  obtain ⟨V₁, hV₁_sub, hV₁_open, hV₁_mem⟩ := mem_nhds_iff.mp hWpre_nhd
  -- V₁ is open Y-set, f x₀ ∈ V₁, V₁ ⊆ preimage of W.
  -- Step 4: the localPullbackAt is continuous at y₀ = f x₀.
  have h_pullbackHol : IsHolomorphicAt
      (localPullbackAt hbc hHol η x₀ hx₀_ram) (f x₀) :=
    localPullbackAt_holomorphic hbc hcompat hHol η x₀ hx₀_ram
  have h_pullbackCont : ContinuousAt
      (localPullbackAt hbc hHol η x₀ hx₀_ram) (f x₀) :=
    h_pullbackHol.continuousAt_cotangentModelFiber
  -- Step 5: define M as ‖value at y₀‖ + 1 and extract bound.
  set M : ℝ := ‖localPullbackAt hbc hHol η x₀ hx₀_ram (f x₀)‖ + 1 with hM_def
  have hM_nhd : ∀ᶠ y in 𝓝 (f x₀),
      ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖ ≤ M := by
    have h_norm_cont : ContinuousAt
        (fun y => ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖) (f x₀) :=
      continuous_norm.continuousAt.comp h_pullbackCont
    have h_lt : (fun y => ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖) (f x₀) < M := by
      simp [hM_def]
    exact h_norm_cont.eventually_lt_const h_lt |>.mono (fun y => le_of_lt)
  obtain ⟨V₂, hV₂_sub, hV₂_open, hV₂_mem⟩ := mem_nhds_iff.mp hM_nhd
  -- Step 6: assemble V := V₀ ∩ V₁ ∩ V₂.
  set V : Set Y := V₀ ∩ V₁ ∩ V₂ with hV_def
  have hV_open : IsOpen V := (hV₀_open.inter hV₁_open).inter hV₂_open
  have hy₀_V : y₀ ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hx₀_fiber]; exact hfxV₀
    · rw [← hx₀_fiber]; exact hV₁_mem
    · rw [← hx₀_fiber]; exact hV₂_mem
  refine ⟨V, W, M, hV_open, hy₀_V, hW_open, hxW, hW_sub_W₀, ?_⟩
  intro y hy_V hy_reg
  -- The single-summand reduction: T.filter (· ∈ W) = {localInverseAt x₀ hx₀_ram y}.
  set T : Finset X := (hbc.finite_fiber y).toFinset with hT_def
  set xy : X := hbc.localInverseAt x₀ hx₀_ram y with hxy_def
  have hy_V₀ : y ∈ V₀ := hy_V.1.1
  have hy_V₁ : y ∈ V₁ := hy_V.1.2
  have hy_V₂ : y ∈ V₂ := hy_V.2
  -- f xy = y (since y ∈ V₀ and `hright`).
  have hfxy : f xy = y := hright y hy_V₀
  -- xy ∈ W (since y ∈ V₁ ⊆ preimage of W).
  have hxyW : xy ∈ W := hV₁_sub hy_V₁
  -- xy ∈ T (since f xy = y means xy ∈ f ⁻¹' {y}).
  have hxyT : xy ∈ T := by
    rw [hT_def, Set.Finite.mem_toFinset]
    exact hfxy
  -- T.filter (· ∈ W) = {xy} as a Finset.
  have hfilter_eq : T.filter (· ∈ W) = ({xy} : Finset X) := by
    apply Finset.ext
    intro x'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx'T, hx'W⟩
      have hfx' : f x' = y := by
        rw [hT_def, Set.Finite.mem_toFinset] at hx'T
        exact hx'T
      have hx'U₀ : x' ∈ U₀ := hW_sub_U₀ hx'W
      have hLI : hbc.localInverseAt x₀ hx₀_ram (f x') = x' := hleft x' hx'U₀
      rw [hfx'] at hLI
      exact hLI.symm
    · intro hx'_eq
      refine ⟨?_, ?_⟩
      · rw [hx'_eq]; exact hxyT
      · rw [hx'_eq]; exact hxyW
  -- Compute the sum: it's a single summand, equal to
  -- localPullbackAt h hHol η x₀ hx₀_ram y.
  have hM_bound : ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖ ≤ M :=
    hV₂_sub hy_V₂
  -- Type-stable summand using CotangentModelFiber ℂ (avoid dependent types).
  let v : X → CotangentModelFiber ℂ := fun x =>
    cotangentPushforward f x (η.toFun x)
  -- The v-sum equals localPullbackAt.
  have hv_sum_eq :
      ((T.filter (· ∈ W)).attach.sum (fun x => v x.1) :
        CotangentModelFiber ℂ) =
        localPullbackAt hbc hHol η x₀ hx₀_ram y := by
    rw [show (T.filter (· ∈ W)).attach.sum (fun x => v x.1) =
          (T.filter (· ∈ W)).sum v from Finset.sum_attach _ v]
    rw [hfilter_eq, Finset.sum_singleton]
    rfl
  have hbound_v : ‖((T.filter (· ∈ W)).attach.sum (fun x => v x.1) :
        CotangentModelFiber ℂ)‖ ≤ M :=
    (congrArg norm hv_sum_eq).le.trans hM_bound
  -- Convert the goal to the v-sum form.
  convert hbound_v

/--
**Chart-stability rewrite of the per-summand derivative factor
(Commit C3c.1 — sorry-free helper).**

When `x` lies in the chart source of `chartAt ℂ x₀` and `f x` lies in
the chart source of `chartAt ℂ (f x₀)`, the `StableChartAt` typeclasses
identify both `chartAt ℂ x = chartAt ℂ x₀` (on `X`) and
`chartAt ℂ (f x) = chartAt ℂ (f x₀)` (on `Y`). Hence
`chartLocalAt f x = chartLocalAt f x₀` as functions `ℂ → ℂ`, and the
chart-evaluation `chartAt ℂ x x = chartAt ℂ x₀ x`, so the per-summand
derivative factor rewrites uniformly.

After C3c every per-summand factor in the scalar Finset sum refers to
the SAME `chartLocalAt f x₀` evaluated at chart coordinates
`chart x₀ x_j`, which is exactly the form Commits A/B
(`chartLocal_zPow_form_of_ramified`, `chartLocal_deriv_of_zPow_form`)
give explicit `φ`/`φ'` formulas for. This unblocks the C3d substitution.
-/
private theorem chartLocalAt_deriv_eq_of_chart_source
    {f : X → Y} {x₀ : X} {x : X}
    (hx_source : x ∈ (chartAt ℂ x₀).source)
    (hfx_source : f x ∈ (chartAt ℂ (f x₀)).source) :
    deriv (chartLocalAt f x) (chartAt ℂ x x) =
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) := by
  -- Both chart-stability identifications.
  have hchartX : chartAt ℂ x = chartAt ℂ x₀ :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source x₀ x hx_source
  have hchartY : chartAt ℂ (f x) = chartAt ℂ (f x₀) :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source (f x₀) (f x) hfx_source
  -- chartLocalAt f x = chartLocalAt f x₀ as functions (both sides unfold to the same composition).
  have hfun : chartLocalAt f x = chartLocalAt f x₀ := by
    unfold chartLocalAt
    rw [hchartX, hchartY]
  -- Evaluation point: chartAt ℂ x x = chartAt ℂ x₀ x.
  have hpt : (chartAt ℂ x) x = (chartAt ℂ x₀) x := by rw [hchartX]
  rw [hfun, hpt]

/--
**Lift the chart-stability rewrite to the full scalar Finset sum
(Commit C3c.2 — sorry-free corollary).**

Under the per-summand chart-source-membership hypotheses, the explicit
ℂ-scalar Finset sum (from C3a's `norm_traceSum_eq_abs_scalarSum`) is
unchanged when each per-summand factor `deriv (chartLocalAt f x.1)(chart x.1 x.1)`
is replaced by `deriv (chartLocalAt f x₀)(chart x₀ x.1)`. This puts the
sum in the form needed to apply Commits A/B in C3d.
-/
private theorem scalarSum_factor_eq_x0_chart_form
    {f : X → Y} (x₀ : X) (η : HolomorphicOneForm ℂ X)
    (s : Finset X)
    (hs_source : ∀ x ∈ s, x ∈ (chartAt ℂ x₀).source)
    (hs_fsource : ∀ x ∈ s, f x ∈ (chartAt ℂ (f x₀)).source) :
    s.attach.sum (fun x =>
      ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) =
    s.attach.sum (fun x =>
      ((deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) := by
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, hx_mem⟩ _
  rw [chartLocalAt_deriv_eq_of_chart_source
    (hs_source x hx_mem) (hs_fsource x hx_mem)]

/--
**End-to-end bridging corollary: filter-CLM-norm = `φ`/`φ'`-form
scalar magnitude (Commit C3d.2 — sorry-free corollary).**

Chains C3b.2 (`norm_filterSum_eq_norm_kfoldScalarSum`) → C3c.2
(`scalarSum_factor_eq_x0_chart_form`) → C3d.1 (`scalarSum_in_phi_form`)
into a single norm equality. After this corollary the
`ramifiedKfoldSum_locally_bounded` LHS norm has the literal `φ`/`φ'`
rational form, ready for C4's analytic cancellation argument.
-/
private theorem norm_filterSum_eq_norm_phiForm
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f) (η : HolomorphicOneForm ℂ X)
    (x₀ : X) (k : ℕ) (φ : ℂ → ℂ)
    {U_kfold : Set X} (W : Set X) (hW_sub_U : W ⊆ U_kfold)
    {y : Y} (s : Finset X)
    (hs_unram : ∀ x ∈ s, hbc.ramificationIndex x = 1)
    (hs_fiber : ∀ x ∈ s, f x = y)
    (hs_exhaust : ∀ x ∈ U_kfold, f x = y → x ∈ s)
    (hs_sub_W : (↑s : Set X) ⊆ W)
    (hs_source : ∀ x ∈ s, x ∈ (chartAt ℂ x₀).source)
    (hs_fsource : ∀ x ∈ s, f x ∈ (chartAt ℂ (f x₀)).source)
    (h_deriv_formula : ∀ x ∈ s,
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) =
        (k : ℂ) * φ (chartAt ℂ x₀ x) ^ (k - 1) * deriv φ (chartAt ℂ x₀ x)) :
    ‖(((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
        (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖ =
    ‖s.attach.sum (fun x =>
      (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
          deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
  -- Chain the three equalities transitively.
  calc ‖(((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
        (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖
      = ‖s.attach.sum (fun x =>
          ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ :=
        norm_filterSum_eq_norm_kfoldScalarSum hbc hcompat hHol η W hW_sub_U s
          hs_unram hs_fiber hs_exhaust hs_sub_W
    _ = ‖s.attach.sum (fun x =>
          ((deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
        rw [scalarSum_factor_eq_x0_chart_form x₀ η s hs_source hs_fsource]
    _ = ‖s.attach.sum (fun x =>
          (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
              deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
        congr 1
        exact scalarSum_in_phi_form x₀ η k φ s h_deriv_formula

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Pure `k`-element-sum boundedness helper for the ramified leaf.**

Given the kfold-ramification chart-local data (a chart-nhd `U_kfold`
of `x₀` and Y-nhd `V_kfold` of `y₀` such that every `y ∈ V_kfold`
with `y ≠ y₀` has a Finset `s_y` of exactly `k` unramified
preimages of `y` in `U_kfold`, exhausting all preimages of `y` in
`U_kfold`), this provides an open `Y`-nhd `V`, an open `X`-nhd
`W ⊆ W₀ ∩ U_kfold` of `x₀`, and a uniform bound `M` on the partial
sum over preimages in `W` for regular `y ∈ V, y ≠ y₀`.

The hypothesis explicitly carries the kfold-ramification structure,
making the obligation strictly chart-local: it only depends on the
kfold chart data and the input form `η`, not on the global properties
of `f` or `hbc`.

This is the genuinely deep roots-of-unity cancellation step. The
chart-local form `w = z^k + …` makes the `k` preimages
`z_j ≈ w^{1/k} ζ^j` (with `ζ = e^{2πi/k}`), each contributing a
cotangent pushforward whose leading term has fractional `w`-power
`w^{(1-k)/k}` that individually blows up as `y → y₀`. Summing over
the `k` preimages cancels these fractional powers (roots-of-unity
summing to 0 except in multiples of `k`), leaving a clean power
series in `w` whose leading coefficient provides the bound.

This is the sole remaining sorry for the ramified leaf, isolated
as a single chart-local analytic statement.
-/
private theorem ramifiedKfoldSum_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (k : ℕ) (hk_pos : 0 < k) (hk_ram : k = hbc.ramificationIndex x₀)
    (U_kfold : Set X) (hU_kfold_open : IsOpen U_kfold) (hxU_kfold : x₀ ∈ U_kfold)
    (V_kfold : Set Y) (hV_kfold_open : IsOpen V_kfold) (hy₀V_kfold : y₀ ∈ V_kfold)
    (h_kfold_data : ∀ y ∈ V_kfold, y ≠ y₀ →
      ∃ s : Finset X, s.card = k ∧ (↑s : Set X) ⊆ U_kfold ∧
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) ∧
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s))
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, y ≠ y₀ → ∀ (_hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  classical
  -- ============================================================
  -- Step 1: Extract DB-A primitives + eventually bijection.
  -- ============================================================
  obtain ⟨φ, r, kthRoot, ζ, hφ_an, hφ_z₀, hφ_deriv, hφ_eq,
      h_right_inv, h_left_inv, hr_at_0, h_kthRoot_pow, h_kthRoot_zero,
      h_kthRoot_cont, hζ_pr, h_evt_bij⟩ :=
    ramified_kfold_chart_bijection f hf hbc hcompat y₀ x₀ hx₀_fiber k hk_pos hk_ram
      U_kfold hU_kfold_open hxU_kfold
  -- Abbreviations.
  set z₀ : ℂ := chartAt ℂ x₀ x₀ with hz₀_def
  set c₀ : ℂ := chartAt ℂ (f x₀) (f x₀) with hc₀_def
  -- ============================================================
  -- Step 2: Layer B — chart-local derivative formula.
  -- ============================================================
  have h_deriv_evt : ∀ᶠ z in 𝓝 z₀,
      deriv (chartLocalAt f x₀) z =
        (k : ℂ) * φ z ^ (k - 1) * deriv φ z :=
    chartLocal_deriv_of_zPow_form (f := f) (x₀ := x₀) (k := k) hk_pos hφ_an hφ_eq
  -- ============================================================
  -- Step 3: η.toFun · 1 chart-local analyticity (§8-internal helper).
  -- ============================================================
  -- The composition `ε ↦ (η.toFun (chart.symm ε)) 1` is analytic at z₀.
  -- This is `etaTimesOne_chart_local_analytic` inlined as §8-internal `have`s.
  have h_etaOne_an : AnalyticAt ℂ
      (fun ε : ℂ => (η.toFun ((chartAt ℂ x₀).symm ε)) (1 : ℂ)) z₀ := by
    -- ContMDiff of trivial-bundle section via clm_bundle_apply.
    have h1 : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
        (fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
          (show (Bundle.Trivial X ℂ) x from (η.toFun x) (1 : ℂ))) :=
      η.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
    -- Extract ContMDiffAt of the underlying eval-at-1 function via trivialization-iff.
    have hsrc : (fun x : X => Bundle.TotalSpace.mk' ℂ
        (E := Bundle.Trivial X ℂ) x ((η.toFun x) (1 : ℂ))) x₀
          ∈ (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).source := by
      rw [Bundle.Trivialization.mem_source]
      exact FiberBundle.mem_baseSet_trivializationAt' x₀
    have h_iff :=
      (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).contMDiffAt_iff
        (IB := 𝓘(ℂ, ℂ)) (IM := 𝓘(ℂ, ℂ)) (n := (⊤ : WithTop ℕ∞))
        (f := fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
          ((η.toFun x) (1 : ℂ)))
        hsrc
    have h_evalOne : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤
        (fun x : X => (η.toFun x) (1 : ℂ)) x₀ :=
      (h_iff.mp h1.contMDiffAt).2
    -- Translate ContMDiffAt → ContDiffAt of the chart-local composition.
    rw [contMDiffAt_iff] at h_evalOne
    obtain ⟨_h_cont, h_cdwithin⟩ := h_evalOne
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h_cdwithin
    -- Self-model: extChartAt = chartAt, codomain extChart = id.
    exact h_cdwithin.analyticAt
  -- ============================================================
  -- Step 4: Build h_DA and apply DA.
  -- ============================================================
  -- Analyticity of `r` at 0 via the analytic inverse function theorem.
  have hSD : HasStrictDerivAt φ (deriv φ z₀) z₀ := hφ_an.hasStrictDerivAt
  -- Build the canonical analytic local inverse `r'` and prove `r =ᶠ[𝓝 0] r'`,
  -- then transport analyticity.
  set r' : ℂ → ℂ := hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv with hr'_def
  have hr'_an_at_φz₀ : AnalyticAt ℂ r' (φ z₀) := by
    simpa [r', hr'_def] using hφ_an.analyticAt_localInverse hφ_deriv
  have hr'_at_0 : r' 0 = z₀ := by
    have h_left : ∀ᶠ z in 𝓝 z₀, r' (φ z) = z := by
      simpa [r', hr'_def] using hSD.eventually_left_inverse hφ_deriv
    have := h_left.self_of_nhds
    rwa [hφ_z₀] at this
  have hr'_cont_at_0 : ContinuousAt r' 0 := by
    have hr'_an_at_0 : AnalyticAt ℂ r' 0 := by rw [← hφ_z₀]; exact hr'_an_at_φz₀
    exact hr'_an_at_0.continuousAt
  have hr'_tendsto_z₀ : Filter.Tendsto r' (𝓝 (0 : ℂ)) (𝓝 z₀) := by
    have h := hr'_cont_at_0.tendsto
    rwa [hr'_at_0] at h
  -- Uniqueness of right inverse: r = r' eventually near 0.
  -- Strategy: apply `h_left_inv : ∀ᶠ z in 𝓝 z₀, r (φ z) = z` at `z = r' ε` (which lies near `z₀`).
  -- Then `r (φ (r' ε)) = r' ε`. Combined with `φ (r' ε) = ε` (right inverse of r'), we get `r ε = r' ε`.
  have h_right_inv' : ∀ᶠ ε in 𝓝 (0 : ℂ), φ (r' ε) = ε := by
    have h := hSD.eventually_right_inverse hφ_deriv
    rw [hφ_z₀] at h
    simpa [r', hr'_def] using h
  have h_r_eq_r' : ∀ᶠ ε in 𝓝 (0 : ℂ), r ε = r' ε := by
    have h_left_at_r' : ∀ᶠ ε in 𝓝 (0 : ℂ), r (φ (r' ε)) = r' ε :=
      hr'_tendsto_z₀.eventually h_left_inv
    filter_upwards [h_left_at_r', h_right_inv'] with ε h1 h2
    rw [h2] at h1; exact h1
  have hr_an_at_0 : AnalyticAt ℂ r 0 := by
    have hr'_an_at_0 : AnalyticAt ℂ r' 0 := by rw [← hφ_z₀]; exact hr'_an_at_φz₀
    exact hr'_an_at_0.congr (h_r_eq_r'.mono (fun _ h => h.symm))
  -- Continuity of r at 0 (will need for various Tendsto compositions).
  have hr_cont_at_0 : ContinuousAt r 0 := hr_an_at_0.continuousAt
  have hr_tendsto_z₀ : Filter.Tendsto r (𝓝 (0 : ℂ)) (𝓝 z₀) := by
    have := hr_cont_at_0.tendsto
    rwa [hr_at_0] at this
  -- Build `h_DA` and prove analyticity at 0.
  -- h_DA(ε) := (η.toFun ((chart x₀).symm (r ε))) 1 / deriv φ (r ε)
  set h_DA : ℂ → ℂ :=
    fun ε => (η.toFun ((chartAt ℂ x₀).symm (r ε))) (1 : ℂ) / deriv φ (r ε) with hh_DA_def
  have h_DA_an : AnalyticAt ℂ h_DA 0 := by
    -- Numerator: (η.toFun (chart.symm (r ε))) 1, analytic at 0.
    -- Decompose: (h_etaOne_an ∘ r), where h_etaOne_an analytic at z₀ = r 0.
    have h_num_an : AnalyticAt ℂ
        (fun ε : ℂ => (η.toFun ((chartAt ℂ x₀).symm (r ε))) (1 : ℂ)) 0 := by
      have h_comp : AnalyticAt ℂ
          ((fun z : ℂ => (η.toFun ((chartAt ℂ x₀).symm z)) (1 : ℂ)) ∘ r) 0 := by
        have h_at : (fun z : ℂ => (η.toFun ((chartAt ℂ x₀).symm z)) (1 : ℂ)) (r 0) =
            (η.toFun ((chartAt ℂ x₀).symm z₀)) (1 : ℂ) := by rw [hr_at_0]
        have h_left : AnalyticAt ℂ
            (fun z : ℂ => (η.toFun ((chartAt ℂ x₀).symm z)) (1 : ℂ)) (r 0) := by
          rw [hr_at_0]; exact h_etaOne_an
        exact h_left.comp hr_an_at_0
      exact h_comp
    -- Denominator: deriv φ (r ε), analytic at 0, nonzero at 0.
    have h_dφ_an_at_z₀ : AnalyticAt ℂ (deriv φ) z₀ := hφ_an.deriv
    have h_denom_an : AnalyticAt ℂ (fun ε : ℂ => deriv φ (r ε)) 0 := by
      have h_left : AnalyticAt ℂ (deriv φ) (r 0) := by rw [hr_at_0]; exact h_dφ_an_at_z₀
      exact h_left.comp hr_an_at_0
    have h_denom_ne : (fun ε : ℂ => deriv φ (r ε)) 0 ≠ 0 := by
      show deriv φ (r 0) ≠ 0
      rw [hr_at_0]; exact hφ_deriv
    exact h_num_an.div h_denom_an h_denom_ne
  -- Apply DA.
  obtain ⟨g, hg_an, h_avg_eq⟩ := rotation_avg_eq_g_pow_k h_DA_an hk_pos hζ_pr
  -- Bound g locally near 0: from AnalyticAt ⇒ ContinuousAt.
  have hg_cont_at_0 : ContinuousAt g 0 := hg_an.continuousAt
  set M : ℝ := ‖g 0‖ + 1 with hM_def
  -- Eventually ‖g t‖ ≤ M for t near 0.
  have hg_evt_bound : ∀ᶠ t in 𝓝 (0 : ℂ), ‖g t‖ ≤ M := by
    have h_tend : Filter.Tendsto g (𝓝 (0 : ℂ)) (𝓝 (g 0)) := hg_cont_at_0.tendsto
    have h_ball : Metric.ball (g 0) 1 ∈ 𝓝 (g 0) := Metric.ball_mem_nhds _ one_pos
    have h_evt_ball : ∀ᶠ t in 𝓝 (0 : ℂ), g t ∈ Metric.ball (g 0) 1 :=
      h_tend.eventually h_ball
    filter_upwards [h_evt_ball] with t ht
    rw [Metric.mem_ball] at ht
    have h_norm_sub : ‖g t - g 0‖ < 1 := by simpa [dist_eq_norm] using ht
    calc ‖g t‖ ≤ ‖g t - g 0‖ + ‖g 0‖ := by
            have := norm_add_le (g t - g 0) (g 0)
            simpa using this
      _ ≤ 1 + ‖g 0‖ := by linarith [h_norm_sub.le]
      _ = M := by rw [hM_def]; ring
  -- ============================================================
  -- Step 5: Define V, W, M.
  -- ============================================================
  -- W := W₀ ∩ U_kfold (open, contains x₀, ⊆ W₀).
  set W : Set X := W₀ ∩ U_kfold with hW_def
  have hW_open : IsOpen W := hW₀_open.inter hU_kfold_open
  have hxW : x₀ ∈ W := ⟨hxW₀, hxU_kfold⟩
  have hW_sub_W₀ : W ⊆ W₀ := Set.inter_subset_left
  have hW_sub_U : W ⊆ U_kfold := Set.inter_subset_right
  -- Define `w_of y := chartAt ℂ (f x₀) y - c₀` (the chart-local coord of y relative to f x₀).
  set w_of : Y → ℂ := fun y => chartAt ℂ (f x₀) y - c₀ with hw_of_def
  have hw_of_at_y₀ : w_of y₀ = 0 := by
    show chartAt ℂ (f x₀) y₀ - c₀ = 0
    rw [show y₀ = f x₀ from hx₀_fiber.symm, hc₀_def]; ring
  -- Continuity of `w_of` at y₀.
  have h_chart_y₀_cont : ContinuousAt (chartAt ℂ (f x₀)) y₀ := by
    have h_chart_src : (chartAt ℂ (f x₀)).source ∈ 𝓝 y₀ := by
      apply (chartAt ℂ (f x₀)).open_source.mem_nhds
      rw [show y₀ = f x₀ from hx₀_fiber.symm]
      exact mem_chart_source ℂ (f x₀)
    exact (chartAt ℂ (f x₀)).continuousOn.continuousAt h_chart_src
  have hw_of_cont : ContinuousAt w_of y₀ := h_chart_y₀_cont.sub continuousAt_const
  have hw_of_tendsto : Filter.Tendsto w_of (𝓝 y₀) (𝓝 (0 : ℂ)) := by
    have h := hw_of_cont.tendsto
    rwa [hw_of_at_y₀] at h
  -- `kthRoot` tendsto 0 at 0.
  have h_kthRoot_tendsto : Filter.Tendsto kthRoot (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h := h_kthRoot_cont.tendsto
    rwa [h_kthRoot_zero] at h
  -- Per-j scaled-rootlet: ε_j(y) := ζ^j * kthRoot (w_of y). Tendsto 0 as y → y₀.
  have h_ε_tendsto : ∀ j : Fin k,
      Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) (𝓝 y₀) (𝓝 (0 : ℂ)) := by
    intro j
    have h := h_kthRoot_tendsto.comp hw_of_tendsto
    have h2 : Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) (𝓝 y₀)
        (𝓝 ((ζ ^ (j : ℕ)) * 0)) := by
      exact (Filter.Tendsto.const_mul (ζ ^ (j : ℕ)) h)
    simpa using h2
  -- Per-j candidate preimage: candX j y := (chart x₀).symm (r (ζ^j · kthRoot (w_of y))).
  set candX : Fin k → Y → X := fun j y =>
    (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) with hcandX_def
  -- Continuity of (chartAt ℂ x₀).symm at z₀.
  have h_chart_symm_cont_at_z₀ : ContinuousAt (chartAt ℂ x₀).symm z₀ := by
    apply (chartAt ℂ x₀).continuousAt_symm
    show z₀ ∈ (chartAt ℂ x₀).target
    rw [hz₀_def]
    exact (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)
  have h_chart_symm_tendsto : Filter.Tendsto (chartAt ℂ x₀).symm (𝓝 z₀) (𝓝 x₀) := by
    have h_val : (chartAt ℂ x₀).symm z₀ = x₀ := by
      rw [hz₀_def]; exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
    have h := h_chart_symm_cont_at_z₀.tendsto
    rwa [h_val] at h
  have h_candX_tendsto : ∀ j : Fin k, Filter.Tendsto (candX j) (𝓝 y₀) (𝓝 x₀) := by
    intro j
    have h := h_chart_symm_tendsto.comp (hr_tendsto_z₀.comp (h_ε_tendsto j))
    exact h
  -- Choose V: intersection of eventually-nhds (V_kfold, candidates ∈ W, kthRoot w_y small, etc.).
  -- We need: y ∈ V_kfold, |w_y| small enough that:
  --   (a) For each j, candX j y ∈ W = W₀ ∩ U_kfold.
  --   (b) For each j, ζ^j · kthRoot w_y is in the right-inverse nhd of `r` (h_right_inv).
  --   (c) ‖g (w_y)‖ ≤ M (hg_evt_bound).
  --   (d) ζ^j · kthRoot w_y is in the rotation-avg eventually nhd from DA (h_avg_eq).
  -- Plus DB-A's eventually-y bijection ((h_evt_bij : ∀ᶠ y in 𝓝 y₀, …)).
  -- And `y` in (chartAt ℂ (f x₀)).source (for the chart-coordinate w_y to be valid).
  have h_W_nhd_x₀ : W ∈ 𝓝 x₀ := hW_open.mem_nhds hxW
  have h_candX_in_W_evt : ∀ j : Fin k, ∀ᶠ y in 𝓝 y₀, candX j y ∈ W :=
    fun j => (h_candX_tendsto j).eventually h_W_nhd_x₀
  -- ζ^j · kthRoot w_y in r's right-inverse nhd.
  have h_right_inv_evt_jallY : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k,
      φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) = (ζ ^ (j : ℕ)) * kthRoot (w_of y) := by
    rw [Filter.eventually_all]
    intro j
    exact (h_ε_tendsto j).eventually h_right_inv
  -- g-bound at w_y.
  have hg_bound_evt : ∀ᶠ y in 𝓝 y₀, ‖g (w_of y)‖ ≤ M := hw_of_tendsto.eventually hg_evt_bound
  -- Rotation-avg formula at kthRoot w_y.
  have h_avg_evt_y : ∀ᶠ y in 𝓝 y₀,
      (∑ j ∈ Finset.range k, ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))) =
        (kthRoot (w_of y)) ^ (k - 1) * g ((kthRoot (w_of y)) ^ k) := by
    have h_kthRoot_tend := h_kthRoot_tendsto.comp hw_of_tendsto
    exact h_kthRoot_tend.eventually h_avg_eq
  -- All candidates analytic-target-nhd containment (so we can use chart.right_inv on chart x₀ (candX j y)).
  have h_chart_x₀_tgt_nhd : (chartAt ℂ x₀).target ∈ 𝓝 z₀ :=
    (chartAt ℂ x₀).open_target.mem_nhds
      (by rw [hz₀_def]; exact (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have h_rε_tgt_evt : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k,
      r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target := by
    rw [Filter.eventually_all]
    intro j
    exact (hr_tendsto_z₀.comp (h_ε_tendsto j)).eventually h_chart_x₀_tgt_nhd
  -- y ∈ source of chart at f x₀.
  have h_y_in_chart_src_evt : ∀ᶠ y in 𝓝 y₀, y ∈ (chartAt ℂ (f x₀)).source := by
    have h_src_nhd : (chartAt ℂ (f x₀)).source ∈ 𝓝 y₀ := by
      apply (chartAt ℂ (f x₀)).open_source.mem_nhds
      rw [show y₀ = f x₀ from hx₀_fiber.symm]
      exact mem_chart_source ℂ (f x₀)
    exact Filter.eventually_mem_set.mpr h_src_nhd
  -- Layer B deriv formula at each chart x₀ (candX j y) = r (ζ^j · kthRoot w_y).
  have h_deriv_evt_y : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k,
      deriv (chartLocalAt f x₀) (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
        (k : ℂ) * φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ^ (k - 1) *
          deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) := by
    rw [Filter.eventually_all]
    intro j
    exact (hr_tendsto_z₀.comp (h_ε_tendsto j)).eventually h_deriv_evt
  -- deriv φ continuous at z₀ (from analyticAt), so deriv φ (r ε_j) ≠ 0 eventually.
  have h_dφ_cont_at_z₀ : ContinuousAt (deriv φ) z₀ := hφ_an.deriv.continuousAt
  have h_dφr_ne_evt : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k,
      deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ≠ 0 := by
    rw [Filter.eventually_all]
    intro j
    -- deriv φ continuous at z₀; deriv φ z₀ ≠ 0 ⇒ deriv φ ≠ 0 on a nhd of z₀.
    -- Then r ε_j ∈ that nhd eventually y.
    have h_dφ_ne_evt_z : ∀ᶠ z in 𝓝 z₀, deriv φ z ≠ 0 := by
      have h_tend : Filter.Tendsto (deriv φ) (𝓝 z₀) (𝓝 (deriv φ z₀)) := h_dφ_cont_at_z₀.tendsto
      have h_compl_open : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_iff.mpr isClosed_singleton
      have h_compl_nhd : ({0}ᶜ : Set ℂ) ∈ 𝓝 (deriv φ z₀) :=
        h_compl_open.mem_nhds (Set.mem_compl_singleton_iff.mpr hφ_deriv)
      exact h_tend.eventually h_compl_nhd
    exact (hr_tendsto_z₀.comp (h_ε_tendsto j)).eventually h_dφ_ne_evt_z
  -- Collect everything into one eventually-y.
  have h_all_evt : ∀ᶠ y in 𝓝 y₀,
      (∀ j : Fin k, candX j y ∈ W) ∧
      (∀ j : Fin k, φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) = (ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∧
      (‖g (w_of y)‖ ≤ M) ∧
      ((∑ j ∈ Finset.range k, ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))) =
        (kthRoot (w_of y)) ^ (k - 1) * g ((kthRoot (w_of y)) ^ k)) ∧
      (∀ j : Fin k, r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target) ∧
      (y ∈ (chartAt ℂ (f x₀)).source) ∧
      (∀ j : Fin k, deriv (chartLocalAt f x₀) (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
          (k : ℂ) * φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ^ (k - 1) *
            deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))) ∧
      (∀ j : Fin k, deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ≠ 0) := by
    have h_candX_all : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k, candX j y ∈ W := by
      rw [Filter.eventually_all]; exact h_candX_in_W_evt
    filter_upwards [h_candX_all, h_right_inv_evt_jallY, hg_bound_evt,
      h_avg_evt_y, h_rε_tgt_evt, h_y_in_chart_src_evt, h_deriv_evt_y, h_dφr_ne_evt, h_evt_bij]
      with y h1 h2 h3 h4 h5 h6 h7 h8 _h_bij
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  -- Also include DB-A's eventually-y bijection separately.
  have h_combined_evt : ∀ᶠ y in 𝓝 y₀,
      (∀ j : Fin k, candX j y ∈ W) ∧
      (∀ j : Fin k, φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) = (ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∧
      (‖g (w_of y)‖ ≤ M) ∧
      ((∑ j ∈ Finset.range k, ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))) =
        (kthRoot (w_of y)) ^ (k - 1) * g ((kthRoot (w_of y)) ^ k)) ∧
      (∀ j : Fin k, r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target) ∧
      (y ∈ (chartAt ℂ (f x₀)).source) ∧
      (∀ j : Fin k, deriv (chartLocalAt f x₀) (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
          (k : ℂ) * φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ^ (k - 1) *
            deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))) ∧
      (∀ j : Fin k, deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ≠ 0) ∧
      (y ≠ y₀ → ∀ (s : Finset X), s.card = k → (↑s : Set X) ⊆ U_kfold →
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) →
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s) →
        ∃ e : Fin k → s, Function.Injective e ∧
          ∀ j : Fin k, (e j : X) =
            (chartAt ℂ x₀).symm
              (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))) := by
    filter_upwards [h_all_evt, h_evt_bij] with y h1 h2
    refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
      h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2, ?_⟩
    intro hy_ne s hs_card hs_sub hs_unram hs_exhaust
    obtain ⟨e, he_inj, he_form⟩ := h2 hy_ne s hs_card hs_sub hs_unram hs_exhaust
    refine ⟨e, he_inj, ?_⟩
    intro j
    show (e j : X) = (chartAt ℂ x₀).symm
      (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))
    have h_eq : chartAt ℂ (f x₀) y - chartAt ℂ (f x₀) (f x₀) = w_of y := by
      show chartAt ℂ (f x₀) y - c₀ = w_of y
      rw [hw_of_def]
    rw [← h_eq]
    exact he_form j
  -- Now extract V as an open subset of V_kfold ∩ source ∩ (eventually-y nhd of y₀).
  obtain ⟨V_evt, hV_evt_open, hy₀V_evt, hV_evt_sub⟩ :
      ∃ V_evt : Set Y, IsOpen V_evt ∧ y₀ ∈ V_evt ∧
        ∀ y ∈ V_evt,
          (∀ j : Fin k, candX j y ∈ W) ∧
          (∀ j : Fin k, φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) = (ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∧
          (‖g (w_of y)‖ ≤ M) ∧
          ((∑ j ∈ Finset.range k, ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))) =
            (kthRoot (w_of y)) ^ (k - 1) * g ((kthRoot (w_of y)) ^ k)) ∧
          (∀ j : Fin k, r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target) ∧
          (y ∈ (chartAt ℂ (f x₀)).source) ∧
          (∀ j : Fin k, deriv (chartLocalAt f x₀) (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
              (k : ℂ) * φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ^ (k - 1) *
                deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))) ∧
          (∀ j : Fin k, deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) ≠ 0) ∧
          (y ≠ y₀ → ∀ (s : Finset X), s.card = k → (↑s : Set X) ⊆ U_kfold →
            (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) →
            (∀ x' ∈ U_kfold, f x' = y → x' ∈ s) →
            ∃ e : Fin k → s, Function.Injective e ∧
              ∀ j : Fin k, (e j : X) =
                (chartAt ℂ x₀).symm
                  (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)))) := by
    rw [Filter.eventually_iff_exists_mem] at h_combined_evt
    obtain ⟨S, hS_nhd, hS_prop⟩ := h_combined_evt
    rw [mem_nhds_iff] at hS_nhd
    obtain ⟨V₀, hV₀_sub, hV₀_open, hy₀V₀⟩ := hS_nhd
    refine ⟨V₀ ∩ V_kfold, hV₀_open.inter hV_kfold_open, ⟨hy₀V₀, hy₀V_kfold⟩, ?_⟩
    intro y ⟨hy_V₀, _hy_Vk⟩
    exact hS_prop _ (hV₀_sub hy_V₀)
  -- Use V := V_evt ∩ V_kfold; that gives us the needed properties AND y ∈ V_kfold for h_kfold_data.
  refine ⟨V_evt ∩ V_kfold, W, M, hV_evt_open.inter hV_kfold_open,
    ⟨hy₀V_evt, hy₀V_kfold⟩, hW_open, hxW, hW_sub_W₀, ?_⟩
  intro y ⟨hy_V_evt, hy_Vk⟩ hy_ne hy_reg
  -- Extract all per-y info.
  obtain ⟨h_candX_W, h_φr_eq, h_g_bd, h_avg_y, h_rε_tgt, h_y_src, h_deriv_y, h_dφr_ne, h_bij_y⟩ :=
    hV_evt_sub y hy_V_evt
  -- Extract the kfold data for this y.
  obtain ⟨s, hs_card, hs_sub_Uk, hs_data, hs_exhaust⟩ := h_kfold_data y hy_Vk hy_ne
  have hs_fiber : ∀ x' ∈ s, f x' = y := fun x' hx's => (hs_data x' hx's).1
  have hs_unram : ∀ x' ∈ s, hbc.ramificationIndex x' = 1 := fun x' hx's => (hs_data x' hx's).2
  -- Extract bijection.
  obtain ⟨e, he_inj, he_form⟩ := h_bij_y hy_ne s hs_card hs_sub_Uk hs_data hs_exhaust
  -- Each (e j).val = candX j y, hence in W.
  have h_e_in_W : ∀ j : Fin k, (e j : X) ∈ W := by
    intro j; rw [he_form j]; exact h_candX_W j
  -- (e j).val also in s_y (subtype).
  -- e : Fin k → {x // x ∈ s} is injective + same card ⇒ bijective.
  have h_e_bij : Function.Bijective e := by
    have h_card_eq : Fintype.card (Fin k) = Fintype.card { x // x ∈ s } := by
      rw [Fintype.card_fin, Fintype.card_coe]; exact hs_card.symm
    exact (Fintype.bijective_iff_injective_and_card e).mpr ⟨he_inj, h_card_eq⟩
  -- Conclude (↑s : Set X) ⊆ W: each x' ∈ s equals e j for some j.
  have hs_sub_W : (↑s : Set X) ⊆ W := by
    intro x' hx's
    obtain ⟨j, hj⟩ := h_e_bij.2 ⟨x', hx's⟩
    have : (e j : X) = x' := by rw [hj]
    rw [← this]; exact h_e_in_W j
  -- Apply norm_filterSum_eq_norm_phiForm.
  -- Need source / fsource of each x ∈ s.
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hs_source : ∀ x ∈ s, x ∈ (chartAt ℂ x₀).source := by
    intro x' hx's
    obtain ⟨j, hj⟩ := h_e_bij.2 ⟨x', hx's⟩
    have h_x'_eq : x' = (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) := by
      have : (e j : X) = x' := by rw [hj]
      rw [← this]; exact he_form j
    rw [h_x'_eq]
    exact (chartAt ℂ x₀).map_target (h_rε_tgt j)
  have hs_fsource : ∀ x ∈ s, f x ∈ (chartAt ℂ (f x₀)).source := by
    intro x' hx's
    rw [hs_fiber x' hx's]
    exact h_y_src
  -- Apply norm_filterSum_eq_norm_phiForm.
  have h_deriv_at_s : ∀ x ∈ s,
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) =
        (k : ℂ) * φ (chartAt ℂ x₀ x) ^ (k - 1) * deriv φ (chartAt ℂ x₀ x) := by
    intro x' hx's
    obtain ⟨j, hj⟩ := h_e_bij.2 ⟨x', hx's⟩
    have h_x'_eq : x' = (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) := by
      have : (e j : X) = x' := by rw [hj]
      rw [← this]; exact he_form j
    have h_chart_x' : chartAt ℂ x₀ x' = r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) := by
      rw [h_x'_eq]
      exact (chartAt ℂ x₀).right_inv (h_rε_tgt j)
    rw [h_chart_x']
    exact h_deriv_y j
  -- Bound the norm.
  rw [norm_filterSum_eq_norm_phiForm hbc hcompat hHol η x₀ k φ W hW_sub_U s
        hs_unram hs_fiber hs_exhaust hs_sub_W hs_source hs_fsource h_deriv_at_s]
  -- Goal: ‖s.attach.sum (fun x => (((k : ℂ) * φ(chart x₀ x.1)^(k-1) * deriv φ(chart x₀ x.1))⁻¹) •
  --                                  (η.toFun x.1) 1)‖ ≤ M
  -- Reindex via e : Fin k → {x // x ∈ s} (bijection) → sum over Finset.univ in Fin k.
  let eEquiv : Fin k ≃ { x // x ∈ s } := Equiv.ofBijective e h_e_bij
  have h_reindex :
      s.attach.sum (fun x => (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
            deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
          (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))
        = (Finset.univ : Finset (Fin k)).sum (fun j =>
          (((k : ℂ) * φ (chartAt ℂ x₀ (e j).1) ^ (k - 1) *
              deriv φ (chartAt ℂ x₀ (e j).1))⁻¹) •
            (η.toFun (e j).1) (1 : TangentSpace 𝓘(ℂ, ℂ) (e j).1)) := by
    show (Finset.univ : Finset { x // x ∈ s }).sum _ = _
    rw [← Equiv.sum_comp eEquiv]
    rfl
  rw [h_reindex]
  -- Substitute the explicit formulas: e j = (chart x₀).symm (r (ζ^j · kthRoot w_y))
  -- chart x₀ (e j).1 = r (ζ^j · kthRoot w_y), and φ ∘ r ε = ε, so φ(r(...)) = ζ^j · kthRoot w_y.
  have h_summand_explicit : ∀ j : Fin k,
      (((k : ℂ) * φ (chartAt ℂ x₀ (e j).1) ^ (k - 1) *
          deriv φ (chartAt ℂ x₀ (e j).1))⁻¹) •
          (η.toFun (e j).1) (1 : TangentSpace 𝓘(ℂ, ℂ) (e j).1)
        = ((k : ℂ) * ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1) *
            deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))⁻¹ *
            ((η.toFun ((chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))) (1 : ℂ)) := by
    intro j
    have h_x'_eq : (e j).1 = (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) :=
      he_form j
    have h_chart_ej : chartAt ℂ x₀ (e j).1 = r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) := by
      rw [h_x'_eq]; exact (chartAt ℂ x₀).right_inv (h_rε_tgt j)
    rw [h_chart_ej, h_φr_eq j, h_x'_eq]
    -- TangentSpace 𝓘(ℂ,ℂ) p = ℂ definitionally; smul = mul.
    show _ • _ = _ * _
    rw [smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => h_summand_explicit j)]
  -- Sum is now Σ_{j ∈ univ Fin k} (k * (ε_j)^(k-1) * deriv φ (r ε_j))⁻¹ * (eta1Comp (r ε_j))
  -- where ε_j = ζ^j · kthRoot w_y.
  -- Pull out (k * (kthRoot w_y)^(k-1))⁻¹ and rewrite (ζ^j)^(k-1) factor.
  -- Recall h_DA(ε) = (eta1Comp (r ε)) / (deriv φ (r ε)).
  -- So each summand = (k * (ε_j)^(k-1))⁻¹ * h_DA(ε_j) * (η.toFun (chart.symm (r ε_j))) 1 *
  --                  (deriv φ (r ε_j))⁻¹ ... wait, let's recompute.
  -- Summand = (k * (ε_j)^(k-1) * deriv φ (r ε_j))⁻¹ * (η.toFun (chart.symm (r ε_j))) 1
  --        = (1/k) * (ε_j)^(-(k-1)) * (deriv φ (r ε_j))⁻¹ * (η.toFun (chart.symm (r ε_j))) 1
  --        = (1/k) * (ε_j)^(-(k-1)) * h_DA(ε_j)
  -- where h_DA(ε) = (η.toFun (chart.symm (r ε))) 1 / deriv φ (r ε).
  -- Note ε_j = ζ^j · kthRoot w_y; (ε_j)^(-(k-1)) = (ζ^j)^(-(k-1)) * (kthRoot w_y)^(-(k-1)).
  -- And (ζ^j)^(-(k-1)) = ζ^j (using ζ^k = 1, -(k-1) ≡ 1 mod k).
  -- So summand = (1/k) * ζ^j * (kthRoot w_y)^(-(k-1)) * h_DA(ζ^j · kthRoot w_y).
  -- Sum = (1/k) * (kthRoot w_y)^(-(k-1)) * ∑ j, ζ^j * h_DA(ζ^j · kthRoot w_y)
  --     = (1/k) * (kthRoot w_y)^(-(k-1)) * (kthRoot w_y)^(k-1) * g((kthRoot w_y)^k)   [by DA]
  --     = (1/k) * g(w_y)   [since (kthRoot w_y)^k = w_y].
  -- For this to make sense we need (kthRoot w_y)^(-(k-1)) · (kthRoot w_y)^(k-1) = 1, i.e.,
  -- kthRoot w_y ≠ 0 (i.e., w_y ≠ 0 i.e., y ≠ y₀). Already have y ≠ y₀.
  -- Critical helper: w_y ≠ 0.
  have hw_y_ne : w_of y ≠ 0 := by
    intro hzero
    apply hy_ne
    have heq : chartAt ℂ (f x₀) y = c₀ := by
      have h0 : chartAt ℂ (f x₀) y - c₀ = 0 := hzero
      linear_combination h0
    have h_fx₀_src : f x₀ ∈ (chartAt ℂ (f x₀)).source := mem_chart_source ℂ (f x₀)
    rw [show y₀ = f x₀ from hx₀_fiber.symm]
    exact (chartAt ℂ (f x₀)).injOn h_y_src h_fx₀_src heq
  have hkthRoot_ne : kthRoot (w_of y) ≠ 0 := by
    intro hzero
    apply hw_y_ne
    have h := h_kthRoot_pow (w_of y)
    rw [hzero, zero_pow hk_pos.ne'] at h
    exact h.symm
  -- Build the sum equation:
  -- ∑ j, (above summand) = (k : ℂ)⁻¹ • g(w_y) = g(w_y) / k.
  -- And we have ∑_{j ∈ range k} ζ^j · h_DA(ζ^j · kthRoot w_y) = (kthRoot w_y)^(k-1) · g(w_y)  (from h_avg_y).
  -- Define the factored summand:
  -- f_j = (k * (ε_j)^(k-1) * deriv φ (r ε_j))⁻¹ * (eta1Comp (r ε_j))
  -- Show ∑ j∈univ, f_j = (k : ℂ)⁻¹ * g(w_y).
  have h_sum_eq :
      (Finset.univ : Finset (Fin k)).sum (fun j =>
          ((k : ℂ) * ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1) *
              deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))⁻¹ *
              ((η.toFun ((chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))) (1 : ℂ)))
        = (k : ℂ)⁻¹ * g (w_of y) := by
    -- Each summand: (k * (ε_j)^(k-1) * deriv φ (r ε_j))⁻¹ * eta1
    -- Rewrite each as (1/k) * ((ε_j)^(k-1))⁻¹ * h_DA(ε_j).
    -- Use (k : ℂ) ≠ 0 (k > 0).
    have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
    have hζ_ne : ∀ j : Fin k, ζ ^ (j : ℕ) ≠ 0 := fun j =>
      pow_ne_zero _ (hζ_pr.ne_zero hk_pos.ne')
    have h_ε_ne : ∀ j : Fin k, (ζ ^ (j : ℕ)) * kthRoot (w_of y) ≠ 0 :=
      fun j => mul_ne_zero (hζ_ne j) hkthRoot_ne
    -- Step A: rewrite each summand as (1/k) * ((ε_j)^(k-1))⁻¹ * h_DA(ε_j)
    -- where h_DA(ε) := (η.toFun (chart.symm (r ε))) 1 / deriv φ (r ε).
    have h_summand_to_hDA : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        ((k : ℂ) * ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1) *
            deriv φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))⁻¹ *
            ((η.toFun ((chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))) (1 : ℂ))
          = (k : ℂ)⁻¹ * (((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1))⁻¹ *
              h_DA ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) := by
      intro j _
      have h_dφr := h_dφr_ne j
      have h_ε := h_ε_ne j
      have h_εp_ne : ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1) ≠ 0 := pow_ne_zero _ h_ε
      show _ = _
      -- Unfold h_DA: (η.toFun (chart.symm (r ε))) 1 / deriv φ (r ε).
      simp only [hh_DA_def]
      field_simp
    rw [Finset.sum_congr rfl h_summand_to_hDA]
    -- Step B: pull ζ^j * t^(-(k-1)) factor + (1/k).
    have h_summand_to_avg_form : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        (k : ℂ)⁻¹ * (((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1))⁻¹ *
            h_DA ((ζ ^ (j : ℕ)) * kthRoot (w_of y))
          = ((k : ℂ)⁻¹ * ((kthRoot (w_of y)) ^ (k - 1))⁻¹) *
              ((ζ ^ (j : ℕ)) * h_DA ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) := by
      intro j _
      have h_ζj_ne := hζ_ne j
      have h_ζj_p_ne : (ζ ^ (j : ℕ)) ^ (k - 1) ≠ 0 := pow_ne_zero _ h_ζj_ne
      have h_kr_p_ne : (kthRoot (w_of y)) ^ (k - 1) ≠ 0 := pow_ne_zero _ hkthRoot_ne
      -- (ζ^j)^(k-1) = (ζ^j)⁻¹ since (ζ^j)^k = 1.
      have h_ζj_pow_k : (ζ ^ (j : ℕ)) ^ k = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ_pr.pow_eq_one, one_pow]
      have h_pow_eq_inv : (ζ ^ (j : ℕ)) ^ (k - 1) = (ζ ^ (j : ℕ))⁻¹ := by
        -- (ζ^j)^(k-1) * (ζ^j) = (ζ^j)^k = 1
        have h_prod : (ζ ^ (j : ℕ)) ^ (k - 1) * (ζ ^ (j : ℕ)) = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hk_pos, h_ζj_pow_k]
        exact eq_inv_of_mul_eq_one_left h_prod
      have h_ε_pow : ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ^ (k - 1) =
          (ζ ^ (j : ℕ)) ^ (k - 1) * (kthRoot (w_of y)) ^ (k - 1) := by
        rw [mul_pow]
      rw [h_ε_pow, mul_inv, h_pow_eq_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl h_summand_to_avg_form]
    -- Step C: pull the constant out of the sum.
    rw [← Finset.mul_sum]
    -- Step D: convert univ-sum over Fin k to range-sum.
    have h_univ_to_range :
        ((Finset.univ : Finset (Fin k)).sum
          (fun j : Fin k => (ζ ^ (j : ℕ)) * h_DA ((ζ ^ (j : ℕ)) * kthRoot (w_of y))))
          = (Finset.range k).sum
            (fun j : ℕ => ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))) := by
      rw [← Finset.sum_range fun j => ζ ^ j * h_DA (ζ ^ j * kthRoot (w_of y))]
    rw [h_univ_to_range, h_avg_y]
    -- Step E: simplify.
    have h_kr_p_ne : (kthRoot (w_of y)) ^ (k - 1) ≠ 0 := pow_ne_zero _ hkthRoot_ne
    have h_kthRoot_pow_w : (kthRoot (w_of y)) ^ k = w_of y := h_kthRoot_pow (w_of y)
    rw [h_kthRoot_pow_w]
    field_simp
  rw [h_sum_eq]
  -- Final norm bound: ‖g(w_y) / k‖ ≤ M.
  have hk_ne_R : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
  have hk_pos_R : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have hk_le : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
  have hM_nn : 0 ≤ M := by rw [hM_def]; positivity
  rw [show ((k : ℂ)⁻¹ * g (w_of y)) = (g (w_of y)) / (k : ℂ) by field_simp]
  rw [norm_div, Complex.norm_natCast]
  have h_norm_le_M : ‖g (w_of y)‖ ≤ M := h_g_bd
  calc ‖g (w_of y)‖ / (k : ℝ) ≤ M / (k : ℝ) := by
        exact div_le_div_of_nonneg_right h_norm_le_M (le_of_lt hk_pos_R)
    _ ≤ M / 1 := by
        apply div_le_div_of_nonneg_left hM_nn one_pos hk_le
    _ = M := by norm_num

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Strictly narrower fiber-point helper (Provider 2 internal),
ramified leaf, `y ≠ y₀` case.** When `x₀` is ramified of index
`n ≥ 2`, the local coordinate form `w = z^n + …` makes the `n`
cotangent pushforwards at the preimages of `y` near `y₀ = f x₀` have
leading terms with fractional `w`-powers `w^{(1-n)/n}` that
individually blow up. The sum over the `n` roots-of-unity preimages
cancels these fractional powers, leaving a clean power series in
`w` whose leading coefficient provides a chart-local bound.

The hypothesis `y ≠ y₀` is essential: at `y = y₀ = f x₀`, the
preimages collapse to `x₀` itself (no `n`-fold splitting), and the
sum is not given by the same formula. (The `y = y₀` case is
vacuous in the broader `ramifiedFiberPoint_partialTrace_locally_bounded`
because `y₀` is not a regular value when `x₀` is ramified.)

This is now a sorry-free reduction to the strictly narrower
`ramifiedKfoldSum_locally_bounded`: apply `local_kfold_ramified` to
identify the partial sum over preimages in `W₀ ∩ U_kfold` with the
`k`-element Finset of unramified preimages of `y` produced by the
kfold structure, then delegate the pure boundedness obligation.
-/
private theorem ramifiedNonY₀FiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (_hx₀_ram : hbc.ramificationIndex x₀ ≠ 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, y ≠ y₀ → ∀ (_hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  -- Extract the kfold-ramification structure at x₀ from IsHolomorphic.
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  let k : ℕ := hbc.ramificationIndex x₀
  have hk_pos : 0 < k := hbc.ramificationIndex_pos x₀
  have hk_ram_eq : k = mapAnalyticOrderAt f x₀ :=
    hbc.ramificationIndex_eq_mapAnalyticOrderAt hcompat (hHol.holomorphicAt x₀)
  obtain ⟨U_kfold, hU_kfold_open, hxU_kfold, V_kfold, hV_kfold_open,
    hfxV_kfold, h_kfold_raw⟩ :=
    hHol.local_kfold_ramified hk_pos hk_ram_eq.symm
  have hy₀V_kfold : y₀ ∈ V_kfold := hx₀_fiber ▸ hfxV_kfold
  -- Convert mapAnalyticOrderAt-typed kfold_data to hbc.ramificationIndex-typed.
  have h_kfold_data : ∀ y ∈ V_kfold, y ≠ y₀ →
      ∃ s : Finset X, s.card = k ∧ (↑s : Set X) ⊆ U_kfold ∧
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) ∧
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s) := by
    intro y hyV hyne
    have hyne' : y ≠ f x₀ := by rw [hx₀_fiber]; exact hyne
    obtain ⟨s, hs_card, hs_sub, hs_data, hs_exhaust⟩ :=
      h_kfold_raw y hyV hyne'
    refine ⟨s, hs_card, hs_sub, ?_, hs_exhaust⟩
    intro x' hx's
    refine ⟨(hs_data x' hx's).1, ?_⟩
    -- mapAnalyticOrderAt f x' = 1 ⇒ ramificationIndex x' = 1.
    have hx'_hol : IsHolomorphicAt f x' := hHol.holomorphicAt x'
    rw [hbc.ramificationIndex_eq_mapAnalyticOrderAt hcompat hx'_hol]
    exact (hs_data x' hx's).2
  -- Apply the kfold-sum bound helper.
  exact ramifiedKfoldSum_locally_bounded f hf η hbc hcompat y₀ x₀ hx₀_fiber
    k hk_pos rfl U_kfold hU_kfold_open hxU_kfold V_kfold hV_kfold_open
    hy₀V_kfold h_kfold_data W₀ hW₀_open hxW₀

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Strictly narrower fiber-point helper (Provider 2 internal),
ramified leaf, dispatcher.** Refines the `ramifiedNonY₀` narrower
helper to the broader signature accepted by
`fiberPoint_partialTrace_locally_bounded`'s dispatcher. The case
`y = y₀` is vacuous: if `y` were regular and equal to `y₀ = f x₀`,
then by `isRegularValue` we'd get `hbc.ramificationIndex x₀ = 1`,
contradicting `hx₀_ram`. The case `y ≠ y₀` is delegated to
`ramifiedNonY₀FiberPoint_partialTrace_locally_bounded`.

Sorry-free.
-/
private theorem ramifiedFiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (hx₀_ram : hbc.ramificationIndex x₀ ≠ 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  obtain ⟨V', W', M', hV'_open, hy₀_V', hW'_open, hxW', hW'_sub, hbound'⟩ :=
    ramifiedNonY₀FiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀
  refine ⟨V', W', M', hV'_open, hy₀_V', hW'_open, hxW', hW'_sub, ?_⟩
  intro y hy_V hy_reg
  by_cases hy_eq : y = y₀
  · -- `y = y₀`: regularity contradicts ramification of x₀.
    exfalso
    apply hx₀_ram
    have hx₀_fib_y : x₀ ∈ f ⁻¹' {y} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hx₀_fiber, hy_eq]
    exact hy_reg x₀ hx₀_fib_y
  · -- `y ≠ y₀`: delegate to the narrower helper.
    exact hbound' y hy_V hy_eq hy_reg

omit [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Strictly narrower fiber-point helper (Provider 2 internal),
dispatcher.** Branches on whether `x₀` is unramified or ramified
and delegates to the appropriate leaf. Sorry-free.
-/
private theorem fiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  by_cases hx₀_ram : hbc.ramificationIndex x₀ = 1
  · exact unramifiedFiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀
  · exact ramifiedFiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀

omit [CompactSpace Y] [ConnectedSpace Y] in
/--
**Provider (2).** *Trace locally bounded near branch values.* At
every branch value `y₀` (a non-regular value) of `hbc`, there is a
neighbourhood of `y₀` and a real bound `M` such that the
chart-local finite-fibre sum is bounded by `M` on the neighbourhood
(intersected with the regular locus).

Mathematically: in a chart-local neighbourhood of a branch value
`y₀`, the preimage `f⁻¹(y₀)` is a finite set; each unramified
preimage contributes a locally bounded (in fact holomorphic) term;
each ramified preimage contributes a term whose chart-local
expansion has the form of a holomorphic 1-form pulled back through
a finite-order branched cover, which is bounded because the input
`η` is holomorphic (not meromorphic). The ramified-preimage
contribution is `0` because the cotangent pushforward at a ramified
point is `0` (the `mfderiv` is not an isomorphism there).

This is now a sorry-free combinatorial assembly of the strictly
narrower per-fiber-point helper
`fiberPoint_partialTrace_locally_bounded`: separate the finite fiber
`f⁻¹{y₀}` by T2 disjoint open nhds, apply the helper at each fiber
point, then assemble via `eventually_fiber_subset_of_compact_T2`
(properness of `f` on the compact source forces nearby fibers to lie
in the union of these chart-neighbourhoods, so the regular-value
trace decomposes as a finite disjoint sum of partial-sum
contributions each bounded by the helper).

The hypotheses are exactly the inputs consumed by Provider (3),
plus `hcompat`, which is already in scope at the unique call site
(`traceForm_extension_per_BCD`).
-/
theorem traceAtRegularValue_locally_bounded_near_branch_values
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (_hy₀ : ¬ isRegularValue hbc y₀) :
    ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, ∀ hy : isRegularValue hbc y,
        ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy‖ ≤ M := by
  classical
  set S : Finset X := (hbc.finite_fiber y₀).toFinset with hS_def
  have hfiber_eq : ∀ {x : X}, x ∈ S ↔ x ∈ f ⁻¹' {y₀} := by
    intro x; rw [hS_def, Set.Finite.mem_toFinset]
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  -- T2 separation: pairwise disjoint open nhds of points in S.
  have hS_fin : (S : Set X).Finite := S.finite_toSet
  obtain ⟨W₀, hW₀_local, hW₀_disj⟩ := hS_fin.exists_pairwiseDisjoint_open_nhds
  -- For each x ∈ S, apply the per-fiber-point helper.
  have hper_x : ∀ x ∈ S, ∃ (V_x : Set Y) (W_x : Set X) (M_x : ℝ),
      IsOpen V_x ∧ y₀ ∈ V_x ∧ IsOpen W_x ∧ x ∈ W_x ∧ W_x ⊆ W₀ x ∧
      ∀ y ∈ V_x, ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W_x)).attach.sum
            (fun x' => (cotangentPushforward f x'.1 (η.toFun x'.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M_x := by
    intro x hxS
    have hx_fiber : f x = y₀ := (hfiber_eq.mp hxS)
    exact fiberPoint_partialTrace_locally_bounded f hf η hbc hcompat y₀ x hx_fiber
      (W₀ x) (hW₀_local x hxS).1 (hW₀_local x hxS).2
  -- Choose V_x, W_x, M_x using `choose`.
  choose! V_x W_x M_x hV_x_open hy₀_in_V_x hW_x_open hxW_x hW_x_sub_W₀ hbound
    using hper_x
  -- Pairwise disjointness of W_x.
  have hW_x_disj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → Disjoint (W_x x₁) (W_x x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne
    exact (hW₀_disj hx₁ hx₂ hne).mono (hW_x_sub_W₀ x₁ hx₁) (hW_x_sub_W₀ x₂ hx₂)
  -- V_int := ⋂ x ∈ S, V_x x.
  have hV_int_nhds : (⋂ x ∈ (S : Set X), V_x x) ∈ 𝓝 y₀ := by
    refine (Filter.biInter_finset_mem S).mpr ?_
    intro x hxS
    exact (hV_x_open x hxS).mem_nhds (hy₀_in_V_x x hxS)
  -- Ω := ⋃ x ∈ S, W_x x.
  let Ω : Set X := ⋃ x ∈ (S : Set X), W_x x
  have hΩ_open : IsOpen Ω :=
    isOpen_biUnion (fun x hxS => hW_x_open x hxS)
  have hFiber_sub_Ω : f ⁻¹' {y₀} ⊆ Ω := by
    intro x hx_fib
    have hxS : x ∈ S := hfiber_eq.mpr hx_fib
    exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) (hxW_x x hxS)
  have hFiber_eventually : ∀ᶠ y' in 𝓝 y₀, f ⁻¹' {y'} ⊆ Ω :=
    eventually_fiber_subset_of_compact_T2 hHol.continuous hΩ_open hFiber_sub_Ω
  -- Combine into a single open V ∋ y₀.
  obtain ⟨V_fiber, hV_fiber_sub, hV_fiber_open, hy₀_in_V_fiber⟩ :=
    mem_nhds_iff.mp hFiber_eventually
  obtain ⟨V_int_open, hV_int_open_sub, hV_int_open_isOpen, hy₀_in_V_int_open⟩ :=
    mem_nhds_iff.mp hV_int_nhds
  set V : Set Y := V_fiber ∩ V_int_open with hV_def
  have hV_open : IsOpen V := hV_fiber_open.inter hV_int_open_isOpen
  have hy₀_V : y₀ ∈ V := ⟨hy₀_in_V_fiber, hy₀_in_V_int_open⟩
  -- The bound: sum of all per-fiber-point bounds.
  refine ⟨V, ∑ x ∈ S, M_x x, hV_open, hy₀_V, ?_⟩
  intro y hy_V hy_reg
  have hy_fib : f ⁻¹' {y} ⊆ Ω := hV_fiber_sub hy_V.1
  have hy_in_V_x : ∀ x ∈ S, y ∈ V_x x := by
    intro x hxS
    have hy_int : y ∈ ⋂ x ∈ (S : Set X), V_x x := hV_int_open_sub hy_V.2
    exact (Set.mem_iInter₂.mp hy_int) x (Finset.mem_coe.mpr hxS)
  -- Decompose (hbc.finite_fiber y).toFinset by which W_x x contains the preimage.
  -- For each preimage x' ∈ fiber(y), x' ∈ Ω, so exactly one x ∈ S has x' ∈ W_x x.
  set T : Finset X := (hbc.finite_fiber y).toFinset with hT_def
  -- Type-stable summand using CotangentModelFiber ℂ.
  let v : X → CotangentModelFiber ℂ := fun x =>
    cotangentPushforward f x (η.toFun x)
  have hT_decomp_sum :
      (T.attach.sum (fun x => v x.1) : CotangentModelFiber ℂ) =
        ∑ x₀ ∈ S, ((T.filter (· ∈ W_x x₀)).attach.sum
          (fun x' => v x'.1) : CotangentModelFiber ℂ) := by
    -- Step 1: reduce both sides' attach sums to ordinary sums.
    have hLHS : T.attach.sum (fun x => v x.1) = T.sum v :=
      Finset.sum_attach T v
    have hRHS : ∀ x₀ ∈ S,
        ((T.filter (· ∈ W_x x₀)).attach.sum (fun x' => v x'.1) :
          CotangentModelFiber ℂ) =
        (T.filter (· ∈ W_x x₀)).sum v :=
      fun x₀ _ => Finset.sum_attach (T.filter (· ∈ W_x x₀)) v
    rw [hLHS]
    rw [show (∑ x₀ ∈ S, ((T.filter (· ∈ W_x x₀)).attach.sum (fun x' => v x'.1) :
            CotangentModelFiber ℂ)) =
          ∑ x₀ ∈ S, (T.filter (· ∈ W_x x₀)).sum v from
      Finset.sum_congr rfl hRHS]
    -- Step 2: T = ⋃ x₀ ∈ S, T.filter (· ∈ W_x x₀), disjoint union.
    -- Use sum_biUnion in reverse.
    symm
    rw [← Finset.sum_biUnion]
    · -- The big-union equals T.
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x'
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨_, _, hx'T, _⟩; exact hx'T
      · intro hx'T
        have hx'_fib : x' ∈ f ⁻¹' {y} := (Set.Finite.mem_toFinset _).mp hx'T
        have hx'_Ω : x' ∈ Ω := hy_fib hx'_fib
        rcases Set.mem_iUnion₂.mp hx'_Ω with ⟨x₀, hx₀S_coe, hx'W⟩
        exact ⟨x₀, Finset.mem_coe.mp hx₀S_coe, hx'T, hx'W⟩
    · -- Pairwise disjointness of filters.
      intro x₁ hx₁ x₂ hx₂ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      rintro x' ⟨_, hx'W₁⟩ ⟨_, hx'W₂⟩
      exact (Set.disjoint_iff.mp
        (hW_x_disj x₁ hx₁ x₂ hx₂ hne)) ⟨hx'W₁, hx'W₂⟩
  -- Now bound the trace via triangle inequality + per-fiber-point bound.
  show ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg‖ ≤ ∑ x ∈ S, M_x x
  -- traceAtRegularValue unfolds to T.attach.sum.
  have htrace_eq :
      (traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg :
        CotangentModelFiber ℂ) =
        T.attach.sum (fun x => v x.1) := by
    unfold traceAtRegularValue
    rfl
  rw [show ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg‖ =
      ‖(T.attach.sum (fun x => v x.1) : CotangentModelFiber ℂ)‖ from
    congrArg norm htrace_eq]
  rw [hT_decomp_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro x₀ hx₀S
  exact hbound x₀ hx₀S y (hy_in_V_x x₀ hx₀S) hy_reg

/--
**Per-branch-point Riemann removable-singularity provider.**

Given a function `g : Y → CotangentModelFiber ℂ` holomorphic on
`regular` (with finite complement) and locally bounded on a
neighborhood `U` of a branch point `y₀ ∈ regularᶜ`, Riemann's
removable singularity theorem produces a function `g_y₀` that is
holomorphic at `y₀` and agrees with `g` on a small `Y`-nhd of `y₀`
intersected with `regular`.

Mathematically: in chart-local coordinates around `y₀`, the function
`cotangentFiberIso ∘ g ∘ chart.symm` is a `ℂ`-valued holomorphic
function on a punctured disc around `chart y₀` (since the only
non-regular point in a small `Y`-nhd of `y₀` is `y₀` itself, by
finiteness of `regularᶜ`) and is bounded there. Riemann's classical
removable singularity theorem extends this to a holomorphic function
on the full disc, which translates back to `g_y₀` holomorphic at `y₀`.

The chart-local transposition is now sorry-free: the entire analytic
content has been reduced to the strictly narrower 1D sub-lemma
`removableSingularity_oneD_punctured_disc` via
* `StableChartAt ℂ Y` (chart agrees with `chartAt ℂ y₀` near `y₀`),
* `singletonChartedSpace_chartAt_eq` (the chart on
  `CotangentModelFiber ℂ` is `cotangentFiberIso`),
* operator-norm bound `‖cotangentFiberIso w‖ ≤ ‖cotangentFiberIso‖ * ‖w‖`,
* `AnalyticAt.congr` / `apply_symm_apply` / `symm_apply_apply`.
-/
private theorem removableSingularity_at_branchPoint
    (regular : Set Y) (_hOpen : IsOpen regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular, IsHolomorphicAt (fun y' : Y => g y') y)
    (y₀ : Y) (hy₀_branch : y₀ ∈ regularᶜ)
    (U : Set Y) (hU_open : IsOpen U) (hy₀_U : y₀ ∈ U) (M : ℝ)
    (hbound : ∀ y ∈ U ∩ regular, ‖g y‖ ≤ M) :
    ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
      IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧
      IsHolomorphicAt g_y₀ y₀ ∧
      ∀ y ∈ V ∩ regular, g_y₀ y = g y := by
  classical
  -- Set up chart at y₀ and refine the open nhd to exclude other branch points.
  set chart := chartAt ℂ y₀ with hchart_def
  set c : ℂ := chart y₀ with hc_def
  have hy₀_chart_src : y₀ ∈ chart.source := mem_chart_source ℂ y₀
  -- Other branch points (regularᶜ \ {y₀}) form a finite (hence closed) set.
  set otherBranches : Set Y := regularᶜ \ {y₀} with hotherBranches_def
  have hotherBranches_finite : otherBranches.Finite := hFiniteCompl.diff
  have hotherBranches_closed : IsClosed otherBranches :=
    hotherBranches_finite.isClosed
  -- Refined open nhd of y₀ inside U ∩ chart.source minus other branch points.
  set U' : Set Y := U ∩ chart.source ∩ otherBranchesᶜ with hU'_def
  have hU'_open : IsOpen U' :=
    (hU_open.inter chart.open_source).inter hotherBranches_closed.isOpen_compl
  have hy₀_U' : y₀ ∈ U' := by
    refine ⟨⟨hy₀_U, hy₀_chart_src⟩, ?_⟩
    intro hcontra
    exact hcontra.2 rfl
  have hU'_sub_src : U' ⊆ chart.source :=
    fun y hy => hy.1.2
  have hU'_sub_U : U' ⊆ U := fun y hy => hy.1.1
  -- s = chart '' U', open in ℂ, nhd of c.
  set s : Set ℂ := chart '' U' with hs_def
  have hs_open : IsOpen s := chart.isOpen_image_of_subset_source hU'_open hU'_sub_src
  have hc_mem_s : c ∈ s := ⟨y₀, hy₀_U', rfl⟩
  have hs_nhds : s ∈ 𝓝 c := hs_open.mem_nhds hc_mem_s
  -- φ : ℂ → ℂ, the chart-local form of g at y₀.
  set φ : ℂ → ℂ := fun z => cotangentFiberIso (g (chart.symm z)) with hφ_def
  -- Analyticity of φ on s \ {c}. For z ∈ s with z ≠ c, let y := chart.symm z.
  -- y ∈ U', y ≠ y₀ (chart-injective), and y ∉ otherBranches, so y ∈ regular.
  -- Then chartLocalAt g y = φ near z (via StableChartAt), giving AnalyticAt φ z.
  have hφ_hol : ∀ z ∈ s, z ≠ c → AnalyticAt ℂ φ z := by
    intro z hz_in_s hz_ne_c
    obtain ⟨y, hy_U', hy_chart⟩ := hz_in_s
    -- y ∈ chart.source.
    have hy_src : y ∈ chart.source := hU'_sub_src hy_U'
    -- y ≠ y₀, because chart y ≠ chart y₀.
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h
      apply hz_ne_c
      rw [← hy_chart, h]
    -- y ∉ otherBranches.
    have hy_not_other : y ∉ otherBranches := hy_U'.2
    -- y ∈ regular: y is not in regularᶜ \ {y₀} and y ≠ y₀, so y ∉ regularᶜ.
    have hy_reg : y ∈ regular := by
      by_contra hy_not_reg
      apply hy_not_other
      exact ⟨hy_not_reg, hy_ne_y₀⟩
    -- StableChartAt: chartAt ℂ y = chartAt ℂ y₀ = chart.
    have hchart_y_eq : chartAt ℂ y = chart := by
      have := StableChartAt.chartAt_eq_of_mem_source (H := ℂ) (M := Y) y₀ y hy_src
      exact this
    -- IsHolomorphicAt g y means AnalyticAt ℂ (chartLocalAt g y) (chartAt ℂ y y).
    have hg_hol_y : IsHolomorphicAt g y := hHol y hy_reg
    -- chartLocalAt g y = cotangentFiberIso ∘ g ∘ (chartAt ℂ y).symm.
    -- Under hchart_y_eq, this equals cotangentFiberIso ∘ g ∘ chart.symm = φ.
    -- And (chartAt ℂ y) y = chart y = z.
    have hg_hol_y' : AnalyticAt ℂ (chartLocalAt g y) (chartAt ℂ y y) := hg_hol_y
    -- Rewrite using hchart_y_eq.
    have hchart_loc_eq :
        chartLocalAt g y = fun q => chartAt ℂ (g y) (g (chart.symm q)) := by
      unfold chartLocalAt
      funext q
      simp [hchart_y_eq, Function.comp]
    have h_point_eq : chartAt ℂ y y = z := by
      rw [hchart_y_eq, ← hy_chart]
    rw [hchart_loc_eq, h_point_eq] at hg_hol_y'
    -- chartAt ℂ (g y) = cotangentFiberIso (singleton chart on CotangentModelFiber ℂ).
    -- So chartLocalAt g y q = cotangentFiberIso (g (chart.symm q)) = φ q.
    have hchart_target_eq :
        (fun q => chartAt ℂ (g y) (g (chart.symm q))) = φ := by
      funext q
      show chartAt ℂ (g y) (g (chart.symm q)) = cotangentFiberIso (g (chart.symm q))
      rfl
    rw [hchart_target_eq] at hg_hol_y'
    exact hg_hol_y'
  -- Boundedness of φ on s \ {c}.
  -- ‖φ z‖ = ‖cotangentFiberIso (g y)‖ ≤ ‖cotangentFiberIso‖ * ‖g y‖ ≤ ‖cotangentFiberIso‖ * M.
  set Miso : ℝ := ‖(cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ)‖ with hMiso_def
  have hMiso_nonneg : 0 ≤ Miso :=
    norm_nonneg (cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ)
  set M' : ℝ := Miso * M + 1 with hM'_def
  have hφ_bnd : ∀ z ∈ s, z ≠ c → ‖φ z‖ ≤ M' := by
    intro z hz_in_s hz_ne_c
    obtain ⟨y, hy_U', hy_chart⟩ := hz_in_s
    have hy_src : y ∈ chart.source := hU'_sub_src hy_U'
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h; apply hz_ne_c; rw [← hy_chart, h]
    have hy_not_other : y ∉ otherBranches := hy_U'.2
    have hy_reg : y ∈ regular := by
      by_contra hy_not_reg
      apply hy_not_other
      exact ⟨hy_not_reg, hy_ne_y₀⟩
    have hy_U : y ∈ U := hU'_sub_U hy_U'
    have hbnd_y : ‖g y‖ ≤ M := hbound y ⟨hy_U, hy_reg⟩
    -- ‖φ z‖ = ‖cotangentFiberIso (g y)‖.
    have hφz_eq : φ z = cotangentFiberIso (g y) := by
      show cotangentFiberIso (g (chart.symm z)) = cotangentFiberIso (g y)
      rw [← hy_chart, chart.left_inv hy_src]
    rw [hφz_eq]
    -- Use ‖cotangentFiberIso (g y)‖ ≤ ‖cotangentFiberIso‖ * ‖g y‖.
    have h_op_bnd : ‖cotangentFiberIso (g y)‖ ≤ Miso * ‖g y‖ :=
      (cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ).le_opNorm (g y)
    have h_mul_bnd : Miso * ‖g y‖ ≤ Miso * M :=
      mul_le_mul_of_nonneg_left hbnd_y hMiso_nonneg
    have h_total : ‖cotangentFiberIso (g y)‖ ≤ Miso * M :=
      h_op_bnd.trans h_mul_bnd
    linarith
  -- Apply the 1D removable-singularity helper.
  obtain ⟨φ_ext, s', hs'_nhds, hs'_sub, hφ_ext_an, hφ_ext_eq⟩ :=
    removableSingularity_oneD_punctured_disc φ c s hs_nhds hφ_hol M' hφ_bnd
  -- Define g_y₀ on chart.source and 0 elsewhere.
  let g_y₀ : Y → CotangentModelFiber ℂ := fun y =>
    if hy : y ∈ chart.source then cotangentFiberIso.symm (φ_ext (chart y))
    else (0 : CotangentModelFiber ℂ)
  -- Extract an open subset s'_open ⊆ s' that is a nhd of c.
  -- Since s' ∈ 𝓝 c, ∃ open T ⊆ s' with c ∈ T.
  obtain ⟨s'_open, hs'_open_sub, hs'_open_isOpen, hc_mem_s'_open⟩ :=
    mem_nhds_iff.mp hs'_nhds
  -- V = chart ⁻¹' s'_open ∩ U'. This is open (preimage of open under continuous chart
  -- restricted to source, intersected with open U' which ⊆ source).
  set V : Set Y := chart.source ∩ chart ⁻¹' s'_open ∩ U' with hV_def
  have hV_open : IsOpen V := by
    have h1 : IsOpen (chart.source ∩ chart ⁻¹' s'_open) :=
      chart.continuousOn.isOpen_inter_preimage chart.open_source hs'_open_isOpen
    exact h1.inter hU'_open
  have hy₀_V : y₀ ∈ V := by
    refine ⟨⟨hy₀_chart_src, ?_⟩, hy₀_U'⟩
    show chart y₀ ∈ s'_open
    rw [← hc_def]; exact hc_mem_s'_open
  have hV_sub_U : V ⊆ U := fun y hy => hU'_sub_U hy.2
  refine ⟨g_y₀, V, hV_open, hy₀_V, hV_sub_U, ?_, ?_⟩
  · -- IsHolomorphicAt g_y₀ y₀: chartLocalAt g_y₀ y₀ is analytic at c.
    -- Show chartLocalAt g_y₀ y₀ =ᶠ[𝓝 c] φ_ext, then apply
    -- AnalyticAt.congr (φ_ext is analytic at c).
    show AnalyticAt ℂ (chartLocalAt g_y₀ y₀) (chartAt ℂ y₀ y₀)
    -- Need a nhd of c where chartLocalAt g_y₀ y₀ q = φ_ext q.
    -- For q in chart.target, chart.symm q ∈ chart.source, so
    -- g_y₀ (chart.symm q) = cotangentFiberIso.symm (φ_ext (chart (chart.symm q)))
    --                     = cotangentFiberIso.symm (φ_ext q).
    -- Then chartLocalAt g_y₀ y₀ q = chartAt ℂ (g_y₀ y₀) (g_y₀ (chart.symm q))
    --                             = cotangentFiberIso (cotangentFiberIso.symm (φ_ext q))
    --                             = φ_ext q.
    have h_target_nhd : chart.target ∈ 𝓝 c := by
      have hc_target : c ∈ chart.target := by
        rw [hc_def]; exact chart.map_source hy₀_chart_src
      exact chart.open_target.mem_nhds hc_target
    have h_ev_eq : chartLocalAt g_y₀ y₀ =ᶠ[𝓝 (chart y₀)] φ_ext := by
      have : chart y₀ = c := by rw [hc_def]
      rw [this]
      filter_upwards [h_target_nhd] with q hq_target
      have hsymm_src : chart.symm q ∈ chart.source := chart.map_target hq_target
      have hright_inv : chart (chart.symm q) = q := chart.right_inv hq_target
      show chartAt ℂ (g_y₀ y₀) (g_y₀ (chart.symm q)) = φ_ext q
      have h_gy_eq : g_y₀ (chart.symm q) = cotangentFiberIso.symm (φ_ext q) := by
        show (if hy : chart.symm q ∈ chart.source then
                cotangentFiberIso.symm (φ_ext (chart (chart.symm q)))
              else (0 : CotangentModelFiber ℂ)) =
              cotangentFiberIso.symm (φ_ext q)
        rw [dif_pos hsymm_src, hright_inv]
      rw [h_gy_eq]
      show cotangentFiberIso (cotangentFiberIso.symm (φ_ext q)) = φ_ext q
      exact cotangentFiberIso.apply_symm_apply (φ_ext q)
    exact hφ_ext_an.congr h_ev_eq.symm
  · -- Agreement: g_y₀ y = g y for y ∈ V ∩ regular.
    intro y hyV
    obtain ⟨⟨⟨hy_src, hy_pre⟩, hy_U'⟩, hy_reg⟩ := hyV
    -- chart y ∈ s'_open ⊆ s'.
    have hy_s' : chart y ∈ s' := hs'_open_sub hy_pre
    -- chart y ≠ c since y ≠ y₀ (because y ∈ regular, y₀ ∉ regular).
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h; rw [h] at hy_reg; exact hy₀_branch hy_reg
    have hchart_ne_c : chart y ≠ c := by
      intro h
      apply hy_ne_y₀
      have hinj := chart.injOn
      exact hinj hy_src hy₀_chart_src (by rw [h, hc_def])
    have hext_eq : φ_ext (chart y) = φ (chart y) :=
      hφ_ext_eq (chart y) hy_s' hchart_ne_c
    -- φ (chart y) = cotangentFiberIso (g (chart.symm (chart y))) = cotangentFiberIso (g y).
    have hφ_chart_y : φ (chart y) = cotangentFiberIso (g y) := by
      show cotangentFiberIso (g (chart.symm (chart y))) = cotangentFiberIso (g y)
      rw [chart.left_inv hy_src]
    -- g_y₀ y = cotangentFiberIso.symm (φ_ext (chart y))
    --       = cotangentFiberIso.symm (cotangentFiberIso (g y)) = g y.
    show (if hy : y ∈ chart.source then cotangentFiberIso.symm (φ_ext (chart y))
          else (0 : CotangentModelFiber ℂ)) = g y
    rw [dif_pos hy_src, hext_eq, hφ_chart_y]
    exact cotangentFiberIso.symm_apply_apply (g y)

/--
**Bundle-section `ContMDiff` from pointwise holomorphicity (strictly
narrower sub-helper).**

Given a function `g_ext : Y → CotangentModelFiber ℂ` that is
`IsHolomorphicAt` at every point of `Y`, the corresponding section
of the cotangent bundle is `ContMDiff` of class `⊤`.

The proof inlines the following structural assembly:
1. `contMDiff_iff_contMDiffAt` reduces to pointwise.
2. `Trivialization.contMDiffAt_section_iff` reduces bundle-section
   `ContMDiff` to `ContMDiff` of the trivialized section
   `(e ⟨y, g_ext y⟩).2`.
3. The cotangent-trivialization formula (inlined, mirroring
   `cotangent_triv_inversion_snd` in
   `InversionChartContinuity.lean:192`) rewrites
   `(e ⟨y, g⟩).snd = g.comp (tT.symmL ℂ y)`.
4. The CLM composition is `ContMDiffAt` by `ContMDiffAt.clm_comp`,
   using:
   - `contMDiff_normedClm_of_contMDiff_singletonChart` to upgrade the
     manifold-`ContMDiff` of `g_ext` (singleton-chart) to normed-space
     `ContMDiff` (CLM-valued).
   - Smoothness of `y ↦ tT.symmL ℂ y` proved inline via the tangent
     trivialization on a stable-chart manifold.
-/
private theorem bundleSection_contMDiff_of_pointwiseHolomorphic
    (g_ext : Y → CotangentModelFiber ℂ)
    (hg_ext_hol : ∀ y : Y, IsHolomorphicAt g_ext y) :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentModelFiber ℂ))
      (⊤ : WithTop ℕ∞)
      (fun y : Y =>
        (Bundle.TotalSpace.mk' (E := CotangentSpace ℂ Y) (CotangentModelFiber ℂ)
          y (g_ext y) :
          Bundle.TotalSpace (CotangentModelFiber ℂ) (CotangentSpace ℂ Y))) := by
  -- Reduce to pointwise (ContMDiff = ∀ x, ContMDiffAt by definition).
  intro y₀
  -- Trivialization at y₀; y₀ is in its baseSet.
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ Y) y₀ with he_def
  have hy₀_base : y₀ ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y₀
  -- Reduce to ContMDiffAt of the trivialized section (e ⟨y, g_ext y⟩).2.
  rw [e.contMDiffAt_section_iff hy₀_base]
  -- The cotangent bundle trivialization decomposes via the tangent
  -- bundle and the trivial line bundle.
  set tT := trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) y₀ with htT_def
  -- Cotangent-trivialization formula (inlined, mirroring
  -- cotangent_triv_inversion_snd):
  --   (e ⟨y, g⟩).snd = g.comp (tT.symmL ℂ y).
  have h_triv_eq :
      ∀ y : Y,
        (e ⟨y, (g_ext y : CotangentSpace ℂ Y y)⟩).snd =
          (g_ext y).comp (tT.symmL ℂ y) := by
    intro y
    show (e ⟨y, (g_ext y : CotangentSpace ℂ Y y)⟩).snd =
        (g_ext y).comp (tT.symmL ℂ y)
    rw [show e = tT.continuousLinearMap (RingHom.id ℂ)
        (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀) from rfl,
      Bundle.Trivialization.continuousLinearMap_apply]
    have hTrivial :
        (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀).continuousLinearMapAt ℂ y =
          ContinuousLinearMap.id ℂ ℂ := by
      have h₀ : (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ y
          = ContinuousLinearMap.id ℂ ℂ :=
        Bundle.Trivial.continuousLinearMapAt_trivialization ℂ Y ℂ y
      have hbridge :
          (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀).continuousLinearMapAt ℂ y =
            (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ y := by
        congr 1
      exact hbridge.trans h₀
    rw [hTrivial]
    rfl
  -- Rewrite the goal via h_triv_eq using congr_of_eventuallyEq.
  apply ContMDiffAt.congr_of_eventuallyEq _ (Filter.Eventually.of_forall h_triv_eq)
  -- Now goal: ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ⊤
  --   (fun y => (g_ext y).comp (tT.symmL ℂ y)) y₀.
  -- Discharge via clm_comp.
  have hg_normed : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, CotangentModelFiber ℂ) (⊤ : WithTop ℕ∞) g_ext :=
    contMDiff_normedClm_of_contMDiff_singletonChart
      (contMDiff_of_pointwiseHolomorphic g_ext hg_ext_hol)
  -- Smoothness of the symmL factor.
  -- Key facts (inlined from Mathlib + project):
  -- * `symmL_trivializationAt_eq_core` (Mathlib): for `b ∈ chart.source`,
  --   `(trivializationAt … b₀).symmL ℂ b = tangentBundleCore.coordChange ...`.
  -- * Under `StableChartAt ℂ Y`, `achart ℂ b = achart ℂ b₀` on
  --   `chart.source` (project's `achart_eq_of_mem_source`).
  -- * `tangentBundleCore.coordChange_self` then makes the coordChange the
  --   identity, so `symmL` is locally constant equal to `(1 : ℂ →L[ℂ] ℂ)`.
  -- Therefore the function is `ContMDiffAt` via `congr_of_eventuallyEq`
  -- with the constant function (1 : ℂ →L[ℂ] ℂ).
  have h_symmL : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y : Y => show ℂ →L[ℂ] ℂ from tT.symmL ℂ y) y₀ := by
    have h_const : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun _ : Y => (1 : ℂ →L[ℂ] ℂ)) y₀ := contMDiffAt_const
    refine h_const.congr_of_eventuallyEq ?_
    -- Show: ∀ᶠ y in 𝓝 y₀, tT.symmL ℂ y = (1 : ℂ →L[ℂ] ℂ).
    have h_src_nhds : (chartAt ℂ y₀).source ∈ 𝓝 y₀ :=
      (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
    filter_upwards [h_src_nhds] with y hy
    show tT.symmL ℂ y = (1 : ℂ →L[ℂ] ℂ)
    -- Use symmL_trivializationAt_eq_core then coordChange_self via StableChartAt.
    rw [TangentBundle.symmL_trivializationAt_eq_core (b₀ := y₀) (b := y) hy]
    -- Now goal: tangentBundleCore ⟨ℂ, ℂ⟩ Y .coordChange (achart ℂ y₀) (achart ℂ y) y = 1.
    have hachart : achart ℂ y = achart ℂ y₀ :=
      JacobianChallenge.Periods.achart_eq_of_mem_source (H := ℂ) (M := Y) hy
    rw [hachart]
    -- Now: coordChange (achart ℂ y₀) (achart ℂ y₀) y = 1.
    have hy_base : y ∈ (tangentBundleCore 𝓘(ℂ, ℂ) Y).baseSet (achart ℂ y₀) := by
      rw [tangentBundleCore_baseSet, coe_achart]
      exact hy
    apply ContinuousLinearMap.ext
    intro v
    rw [(tangentBundleCore 𝓘(ℂ, ℂ) Y).coordChange_self (achart ℂ y₀) y hy_base v]
    simp
  -- Now apply clm_comp.
  have h_goal : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y => (g_ext y).comp (show ℂ →L[ℂ] ℂ from tT.symmL ℂ y)) y₀ :=
    hg_normed.contMDiffAt.clm_comp h_symmL
  -- The goal modulo defeq is the same.
  exact h_goal

/--
**Bundle-section packaging: pointwise holomorphicity → `HolomorphicOneForm`.**

Given a function `g_ext : Y → CotangentModelFiber ℂ` that is
`IsHolomorphicAt` at every point of `Y`, this helper packages it
into a `HolomorphicOneForm ℂ Y` whose underlying function `τ.toFun`
equals `g_ext` pointwise.

This is now a sorry-free reduction to the strictly narrower
bundle-section `ContMDiff` sub-helper
`bundleSection_contMDiff_of_pointwiseHolomorphic`. The
`HolomorphicOneForm` is constructed via the `ContMDiffSection`
constructor with `toFun := g_ext` (relying on the defeq
`CotangentSpace ℂ Y y = CotangentModelFiber ℂ` coming from
`TangentSpace 𝓘(ℂ, ℂ) y = ℂ` and `Bundle.Trivial Y ℂ y = ℂ`); the
agreement `τ.toFun y = g_ext y` then holds by `rfl`.
-/
private theorem holomorphicOneForm_of_pointwiseHolomorphic
    (g_ext : Y → CotangentModelFiber ℂ)
    (hg_ext_hol : ∀ y : Y, IsHolomorphicAt g_ext y) :
    ∃ τ : HolomorphicOneForm ℂ Y, ∀ y : Y, τ.toFun y = g_ext y :=
  ⟨⟨g_ext,
    bundleSection_contMDiff_of_pointwiseHolomorphic g_ext hg_ext_hol⟩,
    fun _ => rfl⟩

/--
**Global assembly of a holomorphic 1-form from per-branch-point
local extensions.**

Given the holomorphic function `g` on the open dense `regular` set,
together with per-branch-point local extensions `g_y₀` (each
holomorphic at its branch point `y₀` and agreeing with `g` on a nhd
of `y₀` intersected with `regular`), this provider glues them into a
single global `HolomorphicOneForm ℂ Y` whose `toFun` agrees with `g`
on `regular`.

This is now a sorry-free reduction to two strictly narrower providers:
* `globalHolomorphicFunction_from_local_extensions` (pointwise
  function-level gluing into a globally `IsHolomorphicAt` function);
* `holomorphicOneForm_of_pointwiseHolomorphic` (bundle-section
  packaging of a pointwise-holomorphic function as a
  `HolomorphicOneForm`).
-/
private theorem assemble_holomorphicOneForm_from_local_extensions
    (regular : Set Y) (hOpen : IsOpen regular) (hDense : Dense regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular, IsHolomorphicAt (fun y' : Y => g y') y)
    (extensions : ∀ y₀ ∈ regularᶜ,
      ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
        IsOpen V ∧ y₀ ∈ V ∧ IsHolomorphicAt g_y₀ y₀ ∧
        ∀ y ∈ V ∩ regular, g_y₀ y = g y) :
    ∃ τ : HolomorphicOneForm ℂ Y, ∀ y ∈ regular, τ.toFun y = g y := by
  -- Step 1: pointwise gluing into a globally holomorphic function.
  obtain ⟨g_ext, hg_ext_hol, hg_ext_eq⟩ :=
    globalHolomorphicFunction_from_local_extensions regular hOpen hDense
      hFiniteCompl g hHol extensions
  -- Step 2: bundle-section packaging.
  obtain ⟨τ, hτ⟩ := holomorphicOneForm_of_pointwiseHolomorphic g_ext hg_ext_hol
  -- Combine: τ.toFun y = g_ext y = g y for y ∈ regular.
  refine ⟨τ, ?_⟩
  intro y hy_reg
  rw [hτ y]
  exact hg_ext_eq y hy_reg

/--
**Provider (3).** *Generic removable-singularity provider for
holomorphic 1-forms.*

For any function `g : Y → CotangentModelFiber ℂ` that is
* holomorphic at every point of `regular` (an *open* dense subset of
  `Y` whose complement is `finite`), and
* locally bounded near every point of `regularᶜ`,

Riemann's removable singularity theorem produces a global
`HolomorphicOneForm ℂ Y` whose `toFun` agrees with `g` on `regular`.

This is the substantive classical analytic content — pure complex analysis
on `Y`, no reference to the source `X` or to the trace map. The
hypotheses are exactly the data produced by Providers (1) and (2)
when specialized to the trace function. Note that the conclusion
quantifies over a single open set `regular` and does not mention
branched-cover data, so it is strictly smaller than
`traceForm_global_extension` (which quantifies over *all* BCDs).

This is now a sorry-free combinatorial reduction to two strictly
narrower providers:
* `removableSingularity_at_branchPoint` (per-branch-point Riemann
  removable singularity);
* `assemble_holomorphicOneForm_from_local_extensions` (global bundle
  section gluing).
-/
theorem holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded
    (regular : Set Y) (hOpen : IsOpen regular) (hDense : Dense regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular,
      IsHolomorphicAt (fun y' : Y => g y') y)
    (hBounded : ∀ y₀ ∈ regularᶜ,
      ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
        ∀ y ∈ U ∩ regular, ‖g y‖ ≤ M) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ y ∈ regular, τ.toFun y = g y := by
  -- For each branch point, extract local bound data + apply per-point
  -- removable singularity to get a local extension.
  have extensions : ∀ y₀ ∈ regularᶜ,
      ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
        IsOpen V ∧ y₀ ∈ V ∧ IsHolomorphicAt g_y₀ y₀ ∧
        ∀ y ∈ V ∩ regular, g_y₀ y = g y := by
    intro y₀ hy₀_branch
    obtain ⟨U, M, hU_open, hy₀_U, hbound⟩ := hBounded y₀ hy₀_branch
    obtain ⟨g_y₀, V, hV_open, hy₀_V, _hV_sub_U, hg_y₀_hol, hg_y₀_eq⟩ :=
      removableSingularity_at_branchPoint regular hOpen hFiniteCompl g hHol
        y₀ hy₀_branch U hU_open hy₀_U M hbound
    exact ⟨g_y₀, V, hV_open, hy₀_V, hg_y₀_hol, hg_y₀_eq⟩
  -- Assemble the global holomorphic form.
  exact assemble_holomorphicOneForm_from_local_extensions regular hOpen hDense
    hFiniteCompl g hHol extensions

omit [CompactSpace Y] [ConnectedSpace Y] in
/--
**Trace-locus pointwise holomorphic auxiliary for Provider (3).**

Provider (1) gives holomorphicity of `localTraceAtRegularValue` (a
chart-local representative). Provider (3) consumes pointwise
holomorphicity of the `dite`-extended global fibre sum. Bridging the
two is the chart-local identification of `localTraceAtRegularValue`
with the global pointwise `traceAtRegularValue`.
-/
theorem regularLocus_dite_trace_holomorphicAt
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y =>
        open Classical in
        if hy' : isRegularValue hbc y' then
          traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
        else (0 : CotangentModelFiber ℂ)) y := by
  classical
  intro y hy_reg
  have hy : isRegularValue hbc y := hy_reg
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hloc_holo : IsHolomorphicAt
      (localTraceAtRegularValue hbc hHol η y hy) y :=
    localTraceAtRegularValue_holomorphic hbc hcompat hHol η y hy
  refine hloc_holo.congr_of_eventuallyEq ?_
  have hRegOpen : IsOpen (regularLocus hbc) := by
    have hfin : ({y : Y | ¬ isRegularValue hbc y}).Finite :=
      branchLocus_finite hbc
    have hC : IsClosed ({y : Y | ¬ isRegularValue hbc y}) := hfin.isClosed
    have hco : IsOpen ({y : Y | ¬ isRegularValue hbc y}ᶜ) := hC.isOpen_compl
    convert hco using 1
    ext z; simp [regularLocus]
  have hReg_mem : regularLocus hbc ∈ 𝓝 y := hRegOpen.mem_nhds hy_reg
  set S : Finset X := (hbc.finite_fiber y).toFinset with hS_def
  have hfiber_eq : ∀ {x : X}, x ∈ S ↔ x ∈ f ⁻¹' {y} := by
    intro x; rw [hS_def, Set.Finite.mem_toFinset]
  -- T2 separation gives raw pairwise disjoint nhds W₀ x.
  have hS_fin : (S : Set X).Finite := S.finite_toSet
  obtain ⟨W₀, hW₀_local, hW₀_disj⟩ := hS_fin.exists_pairwiseDisjoint_open_nhds
  -- For each x ∈ S, ramification index = 1, so the BCD provides U₀ x, V₀ x
  -- with f bijective from U₀ x to V₀ x and inverse identities. Build
  -- `W x := W₀ x ∩ U₀ x`: open, contains x (since x ∈ U₀ x and x ∈ W₀ x),
  -- pairwise disjoint (W₀'s are), and inside U₀ x so `hleft` applies for any
  -- x' ∈ W x giving `localInverseAt x hx_ram (f x') = x'`.
  -- Then use continuity of localInverseAt x at f x = y to find a Y-nhd V₁ x
  -- such that localInverseAt x hx_ram(V₁ x) ⊆ W x.
  have hper_x : ∀ x : X, x ∈ S → ∃ (Wx : Set X) (V₁ : Set Y),
        IsOpen Wx ∧ IsOpen V₁ ∧ x ∈ Wx ∧ y ∈ V₁ ∧
        (∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → x = x₁ ∨ x = x₂ → True) ∧
        (∀ hx_ram : hbc.ramificationIndex x = 1,
          (∀ z ∈ V₁, f (hbc.localInverseAt x hx_ram z) = z ∧
                      hbc.localInverseAt x hx_ram z ∈ Wx) ∧
          (∀ x' ∈ Wx, hbc.localInverseAt x hx_ram (f x') = x')) ∧
        Wx ⊆ W₀ x := by
    intro x hxS
    have hx_fiber : x ∈ f ⁻¹' {y} := hfiber_eq.mp hxS
    have hx_ram : hbc.ramificationIndex x = 1 := hy x hx_fiber
    obtain ⟨U₀, V₀, hU₀_open, hV₀_open, hxU₀, hfxV₀, _hbij, hright, hleft⟩ :=
      hbc.localInverse_is_inverse hx_ram
    have hfx_eq : f x = y := hx_fiber
    -- Wx := W₀ x ∩ U₀: open, x ∈ Wx, Wx ⊆ U₀, Wx ⊆ W₀ x.
    let Wx : Set X := W₀ x ∩ U₀
    have hWx_open : IsOpen Wx := (hW₀_local x hxS).1.inter hU₀_open
    have hxWx : x ∈ Wx := ⟨(hW₀_local x hxS).2, hxU₀⟩
    have hWx_sub_U₀ : Wx ⊆ U₀ := fun _ h => h.2
    have hWx_sub_W₀ : Wx ⊆ W₀ x := fun _ h => h.1
    have hWx_pre : hbc.localInverseAt x hx_ram ⁻¹' Wx ∈ 𝓝 (f x) :=
      localInverseAt_preimage_mem_nhds hbc hcompat hHol x hx_ram hWx_open hxWx
    -- Get an open V₁'' ⊆ preimage of Wx, containing f x.
    obtain ⟨V₁'', hV₁''_sub, hV₁''_open, hyV₁''⟩ := mem_nhds_iff.mp hWx_pre
    refine ⟨Wx, V₀ ∩ V₁'', hWx_open, hV₀_open.inter hV₁''_open, hxWx, ?_, ?_, ?_, hWx_sub_W₀⟩
    · -- y ∈ V₀ ∩ V₁''
      refine ⟨?_, ?_⟩
      · rw [← hfx_eq]; exact hfxV₀
      · rw [← hfx_eq]; exact hyV₁''
    · intros; trivial
    · intro hx_ram'
      refine ⟨?_, ?_⟩
      · intro z ⟨hz_V₀, hz_V₁''⟩
        have h_eq_ram : hx_ram' = hx_ram := rfl
        refine ⟨?_, ?_⟩
        · rw [h_eq_ram]; exact hright z hz_V₀
        · rw [h_eq_ram]; exact hV₁''_sub hz_V₁''
      · intro x' hx'Wx
        have h_eq_ram : hx_ram' = hx_ram := rfl
        rw [h_eq_ram]
        exact hleft x' (hWx_sub_U₀ hx'Wx)
  -- Choose Wx, V₁ etc.
  choose! Wx V₁ hWx_open hV₁_open hxWx hyV₁ _hdisj_trivial hWx_inv hWx_sub_W₀
    using hper_x
  -- Pairwise disjointness of Wx (using hWx_sub_W₀).
  have hWx_disj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → Disjoint (Wx x₁) (Wx x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne
    exact (hW₀_disj hx₁ hx₂ hne).mono (hWx_sub_W₀ x₁ hx₁) (hWx_sub_W₀ x₂ hx₂)
  -- V := ⋂ x ∈ S, V₁ x. Open nhd of y.
  have hV_int_nhds : (⋂ x ∈ (S : Set X), V₁ x) ∈ 𝓝 y := by
    refine (Filter.biInter_finset_mem S).mpr ?_
    intro x hxS
    exact (hV₁_open x hxS).mem_nhds (hyV₁ x hxS)
  -- Ω := ⋃ x ∈ S, Wx x. Open set in X containing fiber(y).
  let Ω : Set X := ⋃ x ∈ (S : Set X), Wx x
  have hΩ_open : IsOpen Ω :=
    isOpen_biUnion (fun x hxS => hWx_open x hxS)
  have hFiber_sub_Ω : f ⁻¹' {y} ⊆ Ω := by
    intro x hx_fib
    have hxS : x ∈ S := hfiber_eq.mpr hx_fib
    exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) (hxWx x hxS)
  have hFiber_eventually : ∀ᶠ y' in 𝓝 y, f ⁻¹' {y'} ⊆ Ω :=
    eventually_fiber_subset_of_compact_T2 hHol.continuous hΩ_open hFiber_sub_Ω
  filter_upwards [hFiber_eventually, hV_int_nhds, hReg_mem] with
    y' hy'_fib hy'_V hy'_regset
  have hy'_reg : isRegularValue hbc y' := hy'_regset
  show localTraceAtRegularValue hbc hHol η y hy y' = _
  rw [dif_pos hy'_reg]
  have hx_ram_of_S : ∀ x ∈ S, hbc.ramificationIndex x = 1 := by
    intro x hxS; exact hy x (hfiber_eq.mp hxS)
  -- The local-inverse bijection φ.
  let φ : ∀ x : X, x ∈ S → X := fun x hxS =>
    hbc.localInverseAt x (hx_ram_of_S x hxS) y'
  have hy'_in_V₁ : ∀ x ∈ S, y' ∈ V₁ x := by
    intro x hxS
    exact (Set.mem_iInter₂.mp hy'_V) x (Finset.mem_coe.mpr hxS)
  have hφ_f : ∀ x : X, ∀ hxS : x ∈ S, f (φ x hxS) = y' := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.1
  have hφ_in_Wx : ∀ x : X, ∀ hxS : x ∈ S, φ x hxS ∈ Wx x := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.2
  have hφ_toFinset : ∀ x : X, ∀ hxS : x ∈ S,
      φ x hxS ∈ (hbc.finite_fiber y').toFinset := by
    intro x hxS
    rw [Set.Finite.mem_toFinset]
    exact hφ_f x hxS
  have hφ_inj : ∀ x₁ : X, ∀ hx₁ : x₁ ∈ S, ∀ x₂ : X, ∀ hx₂ : x₂ ∈ S,
      φ x₁ hx₁ = φ x₂ hx₂ → x₁ = x₂ := by
    intro x₁ hx₁ x₂ hx₂ heq
    by_contra hne
    have hdisj : Disjoint (Wx x₁) (Wx x₂) := hWx_disj x₁ hx₁ x₂ hx₂ hne
    have h1 : φ x₁ hx₁ ∈ Wx x₁ := hφ_in_Wx x₁ hx₁
    have h2 : φ x₂ hx₂ ∈ Wx x₂ := hφ_in_Wx x₂ hx₂
    rw [heq] at h1
    exact (Set.disjoint_iff.mp hdisj) ⟨h1, h2⟩
  have hφ_surj : ∀ x' ∈ (hbc.finite_fiber y').toFinset,
      ∃ (x : X) (hxS : x ∈ S), φ x hxS = x' := by
    intro x' hx'
    have hx'_fib : x' ∈ f ⁻¹' {y'} :=
      (Set.Finite.mem_toFinset _).mp hx'
    have hx'_in_Ω : x' ∈ Ω := hy'_fib hx'_fib
    rcases Set.mem_iUnion₂.mp hx'_in_Ω with ⟨x, hxS_coe, hx'_in_Wx⟩
    have hxS : x ∈ S := Finset.mem_coe.mp hxS_coe
    refine ⟨x, hxS, ?_⟩
    -- φ x hxS = localInverseAt x (hx_ram_of_S x hxS) y'.
    -- We need this = x'.  Since x' ∈ Wx x and f x' = y', and (Wx x, V₁ x) is
    -- a "section" pair with the left-inverse identity on Wx x:
    --   localInverseAt x hx_ram (f x') = x'  (from hWx_inv x hxS hx_ram .2).
    -- And f x' = y', so localInverseAt x hx_ram y' = x', as needed.
    have hfx' : f x' = y' := hx'_fib
    have hLI := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).2 x' hx'_in_Wx
    -- hLI : hbc.localInverseAt x (hx_ram_of_S x hxS) (f x') = x'.
    show hbc.localInverseAt x (hx_ram_of_S x hxS) y' = x'
    rw [← hfx']; exact hLI
  -- Use Finset.sum_nbij' with i, j inverses.
  unfold localTraceAtRegularValue traceAtRegularValue
  -- choose: hφ_surj_choice extracts the unique x ∈ S from a fiber-point x'.
  -- For each x' ∈ fiber(y'), pick (xOfFib x', hxOfFib_mem) such that φ xOfFib x' (...) = x'.
  let xOfFib : ∀ x' : X, x' ∈ (hbc.finite_fiber y').toFinset → X :=
    fun x' hx' => (hφ_surj x' hx').choose
  let xOfFib_mem : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      xOfFib x' hx' ∈ S := fun x' hx' => (hφ_surj x' hx').choose_spec.choose
  have xOfFib_eq : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      φ (xOfFib x' hx') (xOfFib_mem x' hx') = x' :=
    fun x' hx' => (hφ_surj x' hx').choose_spec.choose_spec
  refine Finset.sum_bij'
    (i := fun (z : { x // x ∈ S }) (_ : z ∈ S.attach) =>
      (⟨φ z.1 z.2, hφ_toFinset z.1 z.2⟩ :
        { x // x ∈ (hbc.finite_fiber y').toFinset }))
    (j := fun (z' : { x // x ∈ (hbc.finite_fiber y').toFinset })
        (_ : z' ∈ (hbc.finite_fiber y').toFinset.attach) =>
      (⟨xOfFib z'.1 z'.2, xOfFib_mem z'.1 z'.2⟩ : { x // x ∈ S }))
    ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_attach _ _
  · intro z' _; exact Finset.mem_attach _ _
  · intro z _
    apply Subtype.ext
    show xOfFib (φ z.1 z.2) (hφ_toFinset z.1 z.2) = z.1
    have hee := xOfFib_eq (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    have hxof_S := xOfFib_mem (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    exact hφ_inj _ hxof_S _ z.2 hee
  · intro z' _
    apply Subtype.ext
    show φ (xOfFib z'.1 z'.2) (xOfFib_mem z'.1 z'.2) = z'.1
    exact xOfFib_eq z'.1 z'.2
  · intro z _
    show localPullbackAt hbc hHol η z.1 (hy z.1 ((Set.Finite.mem_toFinset _).mp z.2)) y' =
      cotangentPushforward f (φ z.1 z.2) (η.toFun (φ z.1 z.2))
    unfold localPullbackAt
    rfl
