import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.ChartedFormPullbackChainRule
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Chart-level chain rule for `pathIntegralViaChartCorrect`

States: when a path `γ` on `X` lies in a chart `chartAt ℂ p` and the
mapped path `γ.map hf.continuous` lies in a chart `chartAt ℂ q` on `Y`,
the chart-corrected integral of the form-pullback agrees with the
chart-corrected integral of the original form along the mapped path:

`pathIntegralViaChartCorrect (chartAt ℂ p)
       (pullbackFormsBundledLM X Y f hf η) γ hX =
   pathIntegralViaChartCorrect (chartAt ℂ q) η
       (γ.map hf.continuous) hY`.

## Mathematical content

Unfolding both sides:

LHS = `curveIntegral (chartedFormPullback (chartAt ℂ p)
           (pullbackFormsBundledLM X Y f hf η)) (chartLift (chartAt ℂ p) γ hX)`

RHS = `curveIntegral (chartedFormPullback (chartAt ℂ q) η)
           (chartLift (chartAt ℂ q) (γ.map hf.continuous) hY)`

The chart-lifted paths are related by the chart transition
`(chartAt ℂ q) ∘ f ∘ (chartAt ℂ p).symm`, which is smooth on the
overlap (chart-transition smoothness from `[IsManifold ⊤]` plus
smoothness of `f`).

The integrand transformation factors via the algebraic chart-level
chain rule (in `Jacobian/Periods/ChartedFormPullbackChainRule.lean`):

`chartedFormPullback cX (pullbackFormsBundledLM f hf η) e
   = (chartedFormPullback cY η (ψ e)).comp (mfderiv ψ e)`

The integral identity then reduces to the chain rule for `derivWithin`
applied to `ψ ∘ γ_X.extend = γ_Y.extend`, which holds pointwise at
every t where `γ_X.extend` is differentiable.

## Proof structure
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

open scoped Manifold ContDiff Topology Asymptotics NNReal

/--
The hypothesis-free version
`pathIntegralViaChartCorrect_pullbackFormsBundledLM` retains the same
named obligation as before; this variant discharges it under the
intended-use Lipschitz regularity.
-/
theorem pathIntegralViaChartCorrect_pullbackFormsBundledLM_lipschitz
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (p : X) (q : Y)
    {a b : X} (γ : Path a b)
    (hX : range γ ⊆ (chartAt ℂ p).source)
    (hY : range (γ.map hf.continuous) ⊆ (chartAt ℂ q).source)
    (K : NNReal)
    (hLip : LipschitzOnWith K (chartLift (chartAt ℂ p) γ hX).extend
              (Set.Icc (0 : ℝ) 1)) :
    pathIntegralViaChartCorrect (chartAt ℂ p)
        (pullbackFormsBundledLM X Y f hf η) γ hX =
      pathIntegralViaChartCorrect (chartAt ℂ q) η
        (γ.map hf.continuous) hY := by
  -- Notation
  set cX : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hcX
  set cY : OpenPartialHomeomorph Y ℂ := chartAt ℂ q with hcY
  -- The smooth chart-transition `ψ : ℂ → ℂ`.
  set ψ : ℂ → ℂ := fun e => cY (f (cX.symm e)) with hψ
  -- The chart-lifted paths in the model space ℂ.
  set γ_X : Path (cX a) (cX b) := chartLift cX γ hX with hγ_X
  set γ_Y : Path (cY (f a)) (cY (f b)) :=
    chartLift cY (γ.map hf.continuous) hY with hγ_Y
  -- Key continuity / smoothness / inclusion facts about γ_X.extend.
  -- Helper: γ.extend t ∈ cX.source for all t.
  have hγ_in_cX_source : ∀ t : ℝ, γ.extend t ∈ cX.source := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero γ ht.le]
      have hin : a ∈ range γ := ⟨0, γ.source⟩
      exact hX hin
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le γ ht1.le]
        have hin : b ∈ range γ := ⟨1, γ.target⟩
        exact hX hin
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply γ htI]
        exact hX ⟨⟨t, htI⟩, rfl⟩
  have hgX_extend_in_target : ∀ t : ℝ, γ_X.extend t ∈ cX.target := by
    intro t
    have hγ_in_source : γ.extend t ∈ cX.source := hγ_in_cX_source t
    -- (chartLift cX γ hX).extend t = cX (γ.extend t).
    have hext_eq : γ_X.extend t = cX (γ.extend t) := by
      show (chartLift cX γ hX).extend t = cX (γ.extend t)
      rcases lt_or_ge t 0 with ht | ht
      · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
      · rcases lt_or_ge 1 t with ht1 | ht1
        · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
        · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
          rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
          rfl
    rw [hext_eq]
    exact cX.map_source hγ_in_source
  have hgX_extend_eq : ∀ t : ℝ, γ_X.extend t = cX (γ.extend t) := by
    intro t
    show (chartLift cX γ hX).extend t = cX (γ.extend t)
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
        rfl
  have hgX_symm : ∀ t : ℝ, cX.symm (γ_X.extend t) = γ.extend t := by
    intro t
    have hγ_in_source : γ.extend t ∈ cX.source := hγ_in_cX_source t
    rw [hgX_extend_eq t, cX.left_inv hγ_in_source]
  have hf_in_cY_source : ∀ t : ℝ, f (γ.extend t) ∈ cY.source := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero γ ht.le]
      have h_in : f a ∈ range (γ.map hf.continuous) := ⟨0, by simp⟩
      exact hY h_in
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le γ ht1.le]
        have h_in : f b ∈ range (γ.map hf.continuous) := ⟨1, by simp⟩
        exact hY h_in
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply γ htI]
        have h_in : f (γ ⟨t, htI⟩) ∈ range (γ.map hf.continuous) := ⟨⟨t, htI⟩, rfl⟩
        exact hY h_in
  -- (chartLift cY (γ.map hf.continuous) hY).extend t = cY (f (γ.extend t)) = ψ (γ_X.extend t).
  have hgY_extend_eq : ∀ t : ℝ, γ_Y.extend t = cY (f (γ.extend t)) := by
    intro t
    show (chartLift cY (γ.map hf.continuous) hY).extend t = cY (f (γ.extend t))
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
        rfl
  have hgY_eq_psi_gX : ∀ t : ℝ, γ_Y.extend t = ψ (γ_X.extend t) := by
    intro t
    rw [hgY_extend_eq t]
    show cY (f (γ.extend t)) = cY (f (cX.symm (γ_X.extend t)))
    rw [hgX_symm t]
  -- Main proof: unfold both sides to curveIntegral and apply integral_congr.
  show curveIntegral (chartedFormPullback cX (pullbackFormsBundledLM X Y f hf η)) γ_X =
       curveIntegral (chartedFormPullback cY η) γ_Y
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [curveIntegralFun_def, curveIntegralFun_def]
  -- After unfolding: chartedFormPullback cX (...) (γ_X.extend t) (derivWithin γ_X.extend I t)
  --                  = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Apply chart-level chain rule on LHS.
  have he_target : γ_X.extend t ∈ cX.target := hgX_extend_in_target t
  have he_source : f (cX.symm (γ_X.extend t)) ∈ cY.source := by
    rw [hgX_symm t]; exact hf_in_cY_source t
  rw [chartedFormPullback_pullbackFormsBundledLM_apply f hf η p q
    (γ_X.extend t) he_target he_source]
  -- LHS = chartedFormPullback cY η (cY (f (cX.symm (γ_X.extend t))))
  --         (mfderiv ψ (γ_X.extend t) (derivWithin γ_X.extend I t))
  -- = chartedFormPullback cY η (γ_Y.extend t) (mfderiv ψ ... (deriv ...))   [position match]
  -- We need = RHS = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Identify positions:
  have hpos : cY (f (cX.symm (γ_X.extend t))) = γ_Y.extend t :=
    (hgY_eq_psi_gX t).symm
  rw [hpos]
  -- Now reduces to: chartedFormPullback cY η (γ_Y.extend t)
  --   ((mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t))
  -- = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Sufficient: (mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t)
  --           = derivWithin γ_Y.extend I t
  -- This is the chain rule for derivWithin.
  congr 1
  -- Goal: (mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t) = derivWithin γ_Y.extend I t
  -- Strategy: γ_Y.extend = ψ ∘ γ_X.extend, apply chain rule.
  have hgY_extend_eq_comp : γ_Y.extend = ψ ∘ γ_X.extend := by
    funext s
    exact hgY_eq_psi_gX s
  rw [hgY_extend_eq_comp]
  -- ψ has fderiv at every point of cX.target via smoothness.
  -- We use HasFDerivAt.comp_hasDerivWithinAt-style chain rule, requiring
  -- HasDerivWithinAt for γ_X.extend at t.
  by_cases hd : DifferentiableWithinAt ℝ γ_X.extend (Set.Icc (0:ℝ) 1) t
  · -- γ_X.extend differentiable at t. Apply chain rule.
    have hpsi_diff : DifferentiableAt ℂ ψ (γ_X.extend t) := by
      -- ψ = cY ∘ f ∘ cX.symm, smooth at γ_X.extend t.
      have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
      have hf_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (cX.symm (γ_X.extend t)) :=
        hf.mdifferentiable htop _
      have hcXsymm_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cX.symm (γ_X.extend t) :=
        (mdifferentiable_chart p).mdifferentiableAt_symm he_target
      have hcY_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm (γ_X.extend t))) :=
        (mdifferentiable_chart q).mdifferentiableAt he_source
      have hfcX_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ cX.symm) (γ_X.extend t) :=
        hf_diff_at.comp _ hcXsymm_diff_at
      have hψ_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (γ_X.extend t) := by
        have hψ_comp : ψ = cY ∘ (f ∘ cX.symm) := rfl
        rw [hψ_comp]
        exact MDifferentiableAt.comp _ hcY_diff_at hfcX_diff_at
      rwa [mdifferentiableAt_iff_differentiableAt] at hψ_mdiff
    have hgX_diff_real : HasDerivWithinAt γ_X.extend
        (derivWithin γ_X.extend (Set.Icc (0:ℝ) 1) t) (Set.Icc (0:ℝ) 1) t :=
      hd.hasDerivWithinAt
    have hpsi_fderiv : HasFDerivAt ψ (fderiv ℂ ψ (γ_X.extend t)) (γ_X.extend t) :=
      hpsi_diff.hasFDerivAt
    have hcomp : HasDerivWithinAt (ψ ∘ γ_X.extend)
        ((fderiv ℂ ψ (γ_X.extend t)) (derivWithin γ_X.extend (Set.Icc (0:ℝ) 1) t))
        (Set.Icc (0:ℝ) 1) t := by
      have := hpsi_fderiv.restrictScalars ℝ
      exact this.comp_hasDerivWithinAt t hgX_diff_real
    -- The unique-diff condition on Icc 0 1 at t.
    have hunique : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) t :=
      uniqueDiffOn_Icc_zero_one t ht
    rw [hcomp.derivWithin hunique]
    -- Now: (mfderiv ψ ...) (derivWithin γ_X.extend ... t) = (fderiv ℂ ψ ...) (derivWithin γ_X.extend ... t)
    show (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (γ_X.extend t)) (derivWithin γ_X.extend
        (Set.Icc (0:ℝ) 1) t) = _
    rw [mfderiv_eq_fderiv]
    rfl
  · -- γ_X.extend not differentiable at t. derivWithin γ_X.extend I t = 0.
    rw [derivWithin_zero_of_not_differentiableWithinAt hd]
    refine Eq.trans (map_zero _) ?_
    -- Goal: 0 = derivWithin (ψ ∘ γ_X.extend) I t.
    by_cases hd' : DifferentiableWithinAt ℝ (ψ ∘ γ_X.extend) (Set.Icc (0:ℝ) 1) t
    · -- Pathological case: γ_X.extend not differentiable but ψ ∘ γ_X.extend is.
      -- This requires γ_X.extend t to be at a critical point of ψ:
      -- if `fderiv ℂ ψ (γ_X.extend t) ≠ 0`, ψ is locally invertible (in 1D), and
      -- γ_X.extend = ψ⁻¹ ∘ (ψ ∘ γ_X.extend) would be differentiable at t,
      -- contradicting `hd`.
      -- At critical points (`fderiv ψ = 0`), the Lipschitz hypothesis on
      -- γ_X.extend lets us prove ψ ∘ γ_X.extend has derivative 0 at t via:
      --   |ψ(γ_X(s)) - ψ(γ_X(t))| ≤ ε|γ_X(s) - γ_X(t)| ≤ ε K |s - t|     (HasFDerivAt + Lipschitz)
      -- → o(|s - t|), hence HasDerivWithinAt (ψ ∘ γ_X.extend) 0 at t.
      -- By uniqueness, derivWithin = 0.
      -- We split on whether `fderiv ℂ ψ (γ_X.extend t) = 0`.
      -- Helper: ψ has fderiv at γ_X.extend t (since ψ is smooth there).
      have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
      have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (cX.symm (γ_X.extend t)) :=
        hf.mdifferentiable htop _
      have hcXsymm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cX.symm (γ_X.extend t) :=
        (mdifferentiable_chart p).mdifferentiableAt_symm he_target
      have hcY_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm (γ_X.extend t))) :=
        (mdifferentiable_chart q).mdifferentiableAt he_source
      have hfcX_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ cX.symm) (γ_X.extend t) :=
        hf_diff.comp _ hcXsymm_diff
      have hψ_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (γ_X.extend t) := by
        have hψ_comp : ψ = cY ∘ (f ∘ cX.symm) := rfl
        rw [hψ_comp]
        exact MDifferentiableAt.comp _ hcY_diff hfcX_diff
      have hψ_diffAt : DifferentiableAt ℂ ψ (γ_X.extend t) :=
        mdifferentiableAt_iff_differentiableAt.1 hψ_mdiff
      have hpsi_fderivAt : HasFDerivAt ψ
          (fderiv ℂ ψ (γ_X.extend t)) (γ_X.extend t) :=
        hψ_diffAt.hasFDerivAt
      -- Case-split on whether ψ' = 0 (critical point) or ≠ 0.
      by_cases hpsi' : fderiv ℂ ψ (γ_X.extend t) = 0
      · -- Case: ψ' = 0. Use sandwich argument to get HasDerivWithinAt 0.
        have hpsi_zero : HasFDerivAt ψ (0 : ℂ →L[ℂ] ℂ) (γ_X.extend t) := by
          rw [← hpsi']; exact hpsi_fderivAt
        -- Sandwich: ψ(z) - ψ(γ_X.extend t) = o(|z - γ_X.extend t|).
        have hLittleO : (fun z => ψ z - ψ (γ_X.extend t)) =o[𝓝 (γ_X.extend t)]
            (fun z => z - γ_X.extend t) := by
          have := hpsi_zero.isLittleO
          simpa using this
        -- Compose with γ_X.extend (continuous, so tendsto in 𝓝[Icc 0 1] t).
        have hgX_tendsto : Filter.Tendsto γ_X.extend
            (𝓝[Set.Icc (0:ℝ) 1] t) (𝓝 (γ_X.extend t)) := by
          apply ContinuousAt.continuousWithinAt
          exact (chartLift cX γ hX).continuous_extend.continuousAt
        have hLittleO_comp :
            (fun s => ψ (γ_X.extend s) - ψ (γ_X.extend t)) =o[𝓝[Set.Icc 0 1] t]
            (fun s => γ_X.extend s - γ_X.extend t) :=
          hLittleO.comp_tendsto hgX_tendsto
        -- Lipschitz: |γ_X.extend s - γ_X.extend t| ≤ K |s - t| for s ∈ Icc 0 1.
        have hBigO : (fun s => γ_X.extend s - γ_X.extend t) =O[𝓝[Set.Icc (0:ℝ) 1] t]
            (fun s => s - t) := by
          rw [Asymptotics.isBigO_iff]
          refine ⟨K, ?_⟩
          rw [Filter.eventually_iff_exists_mem]
          refine ⟨Set.Icc (0:ℝ) 1, self_mem_nhdsWithin, fun s hs => ?_⟩
          have hLip_bound : dist (γ_X.extend s) (γ_X.extend t) ≤ K * dist s t :=
            hLip.dist_le_mul s hs t ht
          calc ‖γ_X.extend s - γ_X.extend t‖
              = dist (γ_X.extend s) (γ_X.extend t) := (dist_eq_norm _ _).symm
            _ ≤ ↑K * dist s t := hLip_bound
            _ = ↑K * ‖s - t‖ := by rw [Real.dist_eq]; rfl
        -- Combine: o(s - t)
        have hLittleO_lin :
            (fun s => ψ (γ_X.extend s) - ψ (γ_X.extend t))
              =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => s - t) :=
          hLittleO_comp.trans_isBigO hBigO
        -- This is HasDerivWithinAt (ψ ∘ γ_X.extend) 0 (Icc 0 1) t.
        have hHasDeriv : HasDerivWithinAt (ψ ∘ γ_X.extend) 0 (Set.Icc (0:ℝ) 1) t := by
          rw [hasDerivWithinAt_iff_isLittleO]
          simpa [Function.comp_apply] using hLittleO_lin
        -- By uniqueness: derivWithin = 0.
        have hUnique : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) t :=
          uniqueDiffOn_Icc_zero_one t ht
        rw [hHasDeriv.derivWithin hUnique]
      · -- Case: ψ' ≠ 0. Derive contradiction with hd.
        -- ψ' is invertible (in 1D, non-zero CLM = invertible).
        -- From the chain rule sandwich: γ_X.extend has HasDerivWithinAt at t.
        -- Specifically: HasDerivWithinAt (ψ ∘ γ_X.extend) v at t (from hd').
        -- Combined with HasFDerivAt ψ ψ' at γ_X.extend t and Lipschitz:
        --   ψ' (γ_X.extend(s) - γ_X.extend(t))/(s - t) → v.
        -- Since ψ'⁻¹ exists (1D, ψ' ≠ 0):
        --   (γ_X.extend(s) - γ_X.extend(t))/(s - t) → ψ'⁻¹(v).
        -- HasDerivWithinAt γ_X.extend (ψ'⁻¹(v)) at t. Contradicts hd.
        exfalso
        apply hd
        -- Goal: DifferentiableWithinAt ℝ γ_X.extend (Icc 0 1) t.
        -- Build via HasDerivWithinAt.
        set v := derivWithin (ψ ∘ γ_X.extend) (Set.Icc (0:ℝ) 1) t with hv
        -- Get HasDerivWithinAt for ψ ∘ γ_X.extend.
        have hd'_has : HasDerivWithinAt (ψ ∘ γ_X.extend) v (Set.Icc (0:ℝ) 1) t :=
          hd'.hasDerivWithinAt
        -- ψ' as a complex number (1D CLM = scalar mult).
        let α : ℂ := fderiv ℂ ψ (γ_X.extend t) 1
        have hα_ne : α ≠ 0 := by
          intro hα_zero
          apply hpsi'
          apply ContinuousLinearMap.ext_ring
          show α = (0 : ℂ →L[ℂ] ℂ) 1
          rw [hα_zero, ContinuousLinearMap.zero_apply]
        -- HasDerivAt-style: ψ has HasDerivAt α (γ_X.extend t).
        -- α := fderiv ℂ ψ ... 1, and HasFDerivAt.hasDerivAt gives this.
        have hpsi_derivAt : HasDerivAt ψ α (γ_X.extend t) :=
          hpsi_fderivAt.hasDerivAt
        -- HasDerivAt.isLittleO: the standard Taylor expansion.
        have h_psi_taylor : (fun z => ψ z - ψ (γ_X.extend t) - (z - γ_X.extend t) • α)
            =o[𝓝 (γ_X.extend t)] (fun z => z - γ_X.extend t) :=
          hpsi_derivAt.isLittleO
        have hgX_tendsto : Filter.Tendsto γ_X.extend
            (𝓝[Set.Icc (0:ℝ) 1] t) (𝓝 (γ_X.extend t)) := by
          apply ContinuousAt.continuousWithinAt
          exact (chartLift cX γ hX).continuous_extend.continuousAt
        have h_psi_taylor_comp :
            (fun s => ψ (γ_X.extend s) - ψ (γ_X.extend t) -
              (γ_X.extend s - γ_X.extend t) • α)
            =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => γ_X.extend s - γ_X.extend t) :=
          h_psi_taylor.comp_tendsto hgX_tendsto
        -- Lipschitz: γ_X.extend s - γ_X.extend t = O(s - t).
        have hBigO : (fun s => γ_X.extend s - γ_X.extend t) =O[𝓝[Set.Icc (0:ℝ) 1] t]
            (fun s => s - t) := by
          rw [Asymptotics.isBigO_iff]
          refine ⟨K, ?_⟩
          rw [Filter.eventually_iff_exists_mem]
          refine ⟨Set.Icc (0:ℝ) 1, self_mem_nhdsWithin, fun s hs => ?_⟩
          have hLip_bound : dist (γ_X.extend s) (γ_X.extend t) ≤ K * dist s t :=
            hLip.dist_le_mul s hs t ht
          calc ‖γ_X.extend s - γ_X.extend t‖
              = dist (γ_X.extend s) (γ_X.extend t) := (dist_eq_norm _ _).symm
            _ ≤ ↑K * dist s t := hLip_bound
            _ = ↑K * ‖s - t‖ := by rw [Real.dist_eq]; rfl
        -- Combined: ψ ∘ γ_X.extend - ψ(γ_X.extend t) - (γ_X.extend - γ_X.extend t) • α = o(s - t)
        have h_taylor_lin : (fun s => ψ (γ_X.extend s) - ψ (γ_X.extend t) -
              (γ_X.extend s - γ_X.extend t) • α)
            =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => s - t) :=
          h_psi_taylor_comp.trans_isBigO hBigO
        -- HasDerivWithinAt (ψ ∘ γ_X.extend) v at t (from hd'_has).
        have hd'_isLittleO : (fun s => (ψ ∘ γ_X.extend) s - (ψ ∘ γ_X.extend) t -
              (s - t) • v) =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => s - t) :=
          hd'_has.isLittleO
        -- Subtract: (γ_X.extend - γ_X.extend t) • α - (s - t) • v = o(s - t)
        have h_combined : (fun s => (γ_X.extend s - γ_X.extend t) • α -
              (s - t) • v) =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => s - t) := by
          have h_eq : (fun s => (γ_X.extend s - γ_X.extend t) • α - (s - t) • v) =
              (fun s => -((ψ (γ_X.extend s) - ψ (γ_X.extend t) -
                (γ_X.extend s - γ_X.extend t) • α) -
                ((ψ ∘ γ_X.extend) s - (ψ ∘ γ_X.extend) t - (s - t) • v))) := by
            funext s
            simp only [Function.comp_apply]
            ring
          rw [h_eq]
          exact (h_taylor_lin.sub hd'_isLittleO).neg_left
        -- Divide by α (ne 0): γ_X.extend - γ_X.extend t - (s - t) • (v/α) = o(s - t).
        -- We use the smul-on-ℂ identity: (γ_X.extend - γ_X.extend t) • α = α • (γ_X.extend - γ_X.extend t)
        -- (since smul on ℂ is commutative as multiplication in the field ℂ).
        have h_div_alpha : (fun s => γ_X.extend s - γ_X.extend t - (s - t) • (v / α))
            =o[𝓝[Set.Icc (0:ℝ) 1] t] (fun s => s - t) := by
          have h_smul_eq : ∀ s : ℝ,
              (1 / α : ℂ) • ((γ_X.extend s - γ_X.extend t) • α - (s - t) • v) =
                γ_X.extend s - γ_X.extend t - (s - t) • (v / α) := by
            intro s
            rw [smul_sub]
            congr 1
            · -- (1/α) • ((γ_X.extend s - γ_X.extend t) • α) = γ_X.extend s - γ_X.extend t
              show (1 / α : ℂ) * ((γ_X.extend s - γ_X.extend t) * α) =
                γ_X.extend s - γ_X.extend t
              field_simp
            · -- (1/α) • (s - t) • v = (s - t) • (v / α)
              rw [smul_comm (1 / α : ℂ) (s - t : ℝ) v]
              congr 1
              show (1 / α : ℂ) * v = v / α
              field_simp
          have h_eq : (fun s => γ_X.extend s - γ_X.extend t - (s - t) • (v / α)) =
              (fun s => (1 / α : ℂ) •
                ((γ_X.extend s - γ_X.extend t) • α - (s - t) • v)) := by
            funext s
            exact (h_smul_eq s).symm
          rw [h_eq]
          exact h_combined.const_smul_left (1 / α : ℂ)
        -- This is HasDerivWithinAt γ_X.extend (v/α) at t.
        have hHasDeriv_gX : HasDerivWithinAt γ_X.extend (v / α) (Set.Icc (0:ℝ) 1) t := by
          rw [hasDerivWithinAt_iff_isLittleO]
          exact h_div_alpha
        exact hHasDeriv_gX.differentiableWithinAt
    · rw [derivWithin_zero_of_not_differentiableWithinAt hd']

end JacobianChallenge.Periods
