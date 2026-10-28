import Jacobian.Periods.PathIntegralViaCoverWithRefine
import Jacobian.Periods.ChartedFormPullbackChartChange
import Jacobian.Periods.ChartedFormPullbackCurveIntegrable
import Jacobian.Periods.ChartedFormPullbackContinuous
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

set_option linter.unusedSectionVars false

/-!
# Refinement invariance of `pathIntegralViaCoverWith`

States: any two valid uniform chart partitions of the same path
yield the same `pathIntegralViaCoverWith` value.
-/

open MeasureTheory Path

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-! ### Helpers for the chart-change theorem -/

omit [IsManifold (modelWithCornersSelf ℂ E) ⊤ X] in
/-- The extend of a `chartLift c γ h` factors as `c ∘ γ.extend` (definitionally). -/
private lemma chartLift_extend_eq
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    (chartLift c γ h).extend = (c : X → E) ∘ γ.extend := rfl

/-- The path-extension `γ.extend t` lies in `range γ` for any `t : ℝ`. -/
private lemma extend_mem_range
    {a b : X} (γ : Path a b) (t : ℝ) :
    γ.extend t ∈ range γ := by
  rw [← Path.extend_range γ]
  exact ⟨t, rfl⟩

omit [NormedSpace ℂ E] [IsManifold (modelWithCornersSelf ℂ E) ⊤ X] in
/--
Under chart change, the local equality `(chartAt E q) ∘ γ.extend
=ᶠ[𝓝 t] ((chartAt E q) ∘ (chartAt E p).symm) ∘ ((chartAt E p) ∘ γ.extend)` holds
on the open set where `γ.extend` stays in both chart sources.
-/
private lemma chart_compose_eventuallyEq
    (p q : X) {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source) (_hq : range γ ⊆ (chartAt E q).source)
    (t : ℝ) :
    ((chartAt E q : X → E) ∘ γ.extend) =ᶠ[nhds t]
      (((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ∘
        ((chartAt E p : X → E) ∘ γ.extend)) := by
  have h_subset : ∀ s : ℝ, γ.extend s ∈ (chartAt E p).source := by
    intro s
    have : γ.extend s ∈ range γ.extend := mem_range_self s
    rw [Path.extend_range] at this
    exact hp this
  have h_open : IsOpen ((chartAt E p).source) := (chartAt E p).open_source
  have h_pre_open : IsOpen (γ.extend ⁻¹' (chartAt E p).source) :=
    h_open.preimage γ.continuous_extend
  have h_pre_mem : t ∈ γ.extend ⁻¹' (chartAt E p).source := h_subset t
  refine Filter.eventually_of_mem (h_pre_open.mem_nhds h_pre_mem) ?_
  intro s hs
  show (chartAt E q) (γ.extend s) =
    (chartAt E q) ((chartAt E p).symm ((chartAt E p) (γ.extend s)))
  rw [(chartAt E p).left_inv hs]

/--
The chart transition `(chartAt E q) ∘ (chartAt E p).symm` has a
Fréchet derivative at every point `(chartAt E p) x` for
`x ∈ (chartAt E p).source ∩ (chartAt E q).source`. The derivative
agrees with `mfderiv` of the same composition.
-/
private lemma chartTransition_hasFDerivAt
    (p q : X) (x : X)
    (hp : x ∈ (chartAt E p).source) (hq : x ∈ (chartAt E q).source) :
    HasFDerivAt ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x))
      ((chartAt E p) x) := by
  have h_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E)
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      ((chartAt E p) x) :=
    chartTransition_mdifferentiableAt p q x hp hq
  have h_diff_C : DifferentiableAt ℂ
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x) := by
    rw [mdifferentiableAt_iff_differentiableAt] at h_mdiff
    exact h_mdiff
  have h_hf : HasFDerivAt
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      (fderiv ℂ ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x))
      ((chartAt E p) x) := h_diff_C.hasFDerivAt
  rw [show mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x) =
      fderiv ℂ ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
        ((chartAt E p) x) from mfderiv_eq_fderiv]
  exact h_hf

/-- **Lemma B (chart-transition chain rule for `derivWithin`).** -/
private lemma derivWithin_chart_transition_chain_rule
    (p q : X) {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source) (hq : range γ ⊆ (chartAt E q).source)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    derivWithin ((chartAt E q : X → E) ∘ γ.extend) (Set.Icc (0:ℝ) 1) t =
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)))
        ((chartAt E p) (γ.extend t))
        (derivWithin ((chartAt E p : X → E) ∘ γ.extend) (Set.Icc (0:ℝ) 1) t) := by
  set f_p : ℝ → E := (chartAt E p : X → E) ∘ γ.extend with hf_p
  set f_q : ℝ → E := (chartAt E q : X → E) ∘ γ.extend with hf_q
  set ψ : E → E := (chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X) with hψ
  set ψ_inv : E → E := (chartAt E p : X → E) ∘ ((chartAt E q).symm : E → X) with hψ_inv
  set s : Set ℝ := Set.Icc (0:ℝ) 1
  have hγt_p : γ.extend t ∈ (chartAt E p).source :=
    hp (extend_mem_range γ t)
  have hγt_q : γ.extend t ∈ (chartAt E q).source :=
    hq (extend_mem_range γ t)
  have h_ψ_fderiv : HasFDerivAt ψ
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
        ((chartAt E p) (γ.extend t)))
      ((chartAt E p) (γ.extend t)) :=
    chartTransition_hasFDerivAt p q (γ.extend t) hγt_p hγt_q
  have h_ψ_inv_fderiv : HasFDerivAt ψ_inv
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
        ((chartAt E q) (γ.extend t)))
      ((chartAt E q) (γ.extend t)) :=
    chartTransition_hasFDerivAt q p (γ.extend t) hγt_q hγt_p
  have h_eq_ψfp : f_q =ᶠ[nhds t] ψ ∘ f_p :=
    chart_compose_eventuallyEq p q γ hp hq t
  have h_eq_ψinvfq : f_p =ᶠ[nhds t] ψ_inv ∘ f_q :=
    chart_compose_eventuallyEq q p γ hq hp t
  by_cases h_diff : DifferentiableWithinAt ℝ f_p s t
  · have h_fp_hasDeriv : HasDerivWithinAt f_p (derivWithin f_p s t) s t :=
      h_diff.hasDerivWithinAt
    have h_ψ_fderiv_R : HasFDerivAt ψ
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))).restrictScalars ℝ)
        ((chartAt E p) (γ.extend t)) :=
      h_ψ_fderiv.restrictScalars ℝ
    have h_comp : HasDerivWithinAt (ψ ∘ f_p)
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))) (derivWithin f_p s t)) s t := by
      have := h_ψ_fderiv_R.comp_hasDerivWithinAt t h_fp_hasDeriv
      convert this using 1
    have h_fq_hasDeriv : HasDerivWithinAt f_q
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))) (derivWithin f_p s t)) s t := by
      apply h_comp.congr_of_eventuallyEq
      · exact h_eq_ψfp.filter_mono nhdsWithin_le_nhds
      · exact h_eq_ψfp.self_of_nhds
    rw [h_fq_hasDeriv.derivWithin (uniqueDiffOn_Icc_zero_one t ht)]
  · have h_fp_zero : derivWithin f_p s t = 0 :=
      derivWithin_zero_of_not_differentiableWithinAt h_diff
    have h_fq_not_diff : ¬ DifferentiableWithinAt ℝ f_q s t := by
      intro h_fq_diff
      apply h_diff
      have h_fq_hd : HasDerivWithinAt f_q (derivWithin f_q s t) s t :=
        h_fq_diff.hasDerivWithinAt
      have h_ψinv_R : HasFDerivAt ψ_inv
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))).restrictScalars ℝ)
          ((chartAt E q) (γ.extend t)) :=
        h_ψ_inv_fderiv.restrictScalars ℝ
      have h_psi_inv_fq : HasDerivWithinAt (ψ_inv ∘ f_q)
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))) (derivWithin f_q s t)) s t := by
        have := h_ψinv_R.comp_hasDerivWithinAt t h_fq_hd
        convert this using 1
      have h_fp_hd : HasDerivWithinAt f_p
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))) (derivWithin f_q s t)) s t := by
        apply h_psi_inv_fq.congr_of_eventuallyEq
        · exact h_eq_ψinvfq.filter_mono nhdsWithin_le_nhds
        · exact h_eq_ψinvfq.self_of_nhds
      exact h_fp_hd.differentiableWithinAt
    have h_fq_zero : derivWithin f_q s t = 0 :=
      derivWithin_zero_of_not_differentiableWithinAt h_fq_not_diff
    rw [h_fq_zero, h_fp_zero, ContinuousLinearMap.map_zero]


theorem pathIntegralViaChartCorrect_chart_change
    (ω : HolomorphicOneForm E X) (p q : X)
    {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source)
    (hq : range γ ⊆ (chartAt E q).source) :
    pathIntegralViaChartCorrect (chartAt E p) ω γ hp =
      pathIntegralViaChartCorrect (chartAt E q) ω γ hq := by
  unfold pathIntegralViaChartCorrect pathIntegralInChartCorrect
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [curveIntegralFun_def, curveIntegralFun_def]
  rw [chartLift_extend_eq, chartLift_extend_eq]
  rw [derivWithin_chart_transition_chain_rule p q γ hp hq t ht]
  have hγt_p : γ.extend t ∈ (chartAt E p).source :=
    hp (extend_mem_range γ t)
  have hγt_q : γ.extend t ∈ (chartAt E q).source :=
    hq (extend_mem_range γ t)
  exact chartedFormPullback_chart_change_apply p q ω (γ.extend t) _ hγt_p hγt_q

/-! ### Chart-pick independence -/

/-
For the same uniform grid, different chart picks yield the same integral.
This follows from chart-change invariance at each segment.
-/
private lemma pathIntegralViaCoverWith_pick_independent
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pick₁ pick₂ : Fin n → X)
    (hcov₁ : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pick₁ i)).source)
    (hcov₂ : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pick₂ i)).source) :
    pathIntegralViaCoverWith ω γ n hn pick₁ hcov₁ =
      pathIntegralViaCoverWith ω γ n hn pick₂ hcov₂ := by
  unfold pathIntegralViaCoverWith;
  grind +suggestions

/-
Invariance under propositional equality of grid sizes. Combines
`subst` with `pathIntegralViaCoverWith_pick_independent`.
-/
private lemma pathIntegralViaCoverWith_eq_of_size_eq
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : n = m)
    (pick₁ : Fin n → X) (pick₂ : Fin m → X)
    (hcov₁ : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pick₁ i)).source)
    (hcov₂ : ∀ (i : Fin m) (t : unitInterval),
      (i : ℝ) / m ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / m →
      γ t ∈ (chartAt E (pick₂ i)).source) :
    pathIntegralViaCoverWith ω γ n hn pick₁ hcov₁ =
      pathIntegralViaCoverWith ω γ m hm pick₂ hcov₂ := by
  subst h
  generalize_proofs at *;
  exact pathIntegralViaCoverWith_pick_independent ω γ n hn pick₁ pick₂ hcov₁ hcov₂

/-! ### Coverage for common refinement -/

/-
Coverage condition for the common refinement from the first partition.
-/
private lemma coverage_refinement
    {a b : X} (γ : Path a b)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (j : Fin (n * k)) (t : unitInterval)
    (h1 : (j : ℝ) / ((n * k : ℕ) : ℝ) ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ ((j : ℝ) + 1) / ((n * k : ℕ) : ℝ)) :
    γ t ∈ (chartAt E (pickChart
      ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)).source := by
  convert hcov ⟨ j / k, _ ⟩ t _ _
  all_goals generalize_proofs at *;
  · refine' le_trans _ h1;
    rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_mul_le_self j k, Nat.div_add_mod j k, Nat.mod_lt j hk ];
  · refine' h2.trans _;
    rw [ div_le_div_iff₀ ] <;> norm_cast <;> try positivity;
    nlinarith! [ Nat.div_add_mod j k, Nat.mod_lt j hk ]

/-! ### Integrability from C¹ hypothesis -/

/-
Integrability of the chart-pullback integrand on each segment,
derived from the C¹ path hypothesis and StableChartAt.
-/
private lemma segment_integrability
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (hγ : ∀ (p : X), ContDiffOn ℝ 1 ((chartAt E p) ∘ γ.extend)
          (γ.extend ⁻¹' (chartAt E p).source ∩ Set.Icc 0 1))
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (i : Fin n) :
    IntervalIntegrable
      (fun t => (chartedFormPullback (chartAt E (pickChart i)) ω)
        ((chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ n hn pickChart hcov i)).extend t)
        (derivWithin (chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ n hn pickChart hcov i)).extend
          (Set.Icc 0 1) t))
      volume 0 1 := by
  have h_cont_diff : ContDiffOn ℝ 1 (⇑(chartAt E (pickChart i)) ∘ ⇑(γ.subpath (divFinIcc n hn ↑i.val (le_of_lt i.isLt)) (divFinIcc n hn (↑i.val + 1) i.isLt)).extend) (⇑(γ.subpath (divFinIcc n hn ↑i.val (le_of_lt i.isLt)) (divFinIcc n hn (↑i.val + 1) i.isLt)).extend ⁻¹' (chartAt E (pickChart i)).source ∩ Icc 0 1) := by
    convert hγ ( pickChart i ) |> ContDiffOn.comp <| show ContDiffOn ℝ 1 ( fun t => ( divFinIcc n hn ( i : ℕ ) ( Nat.le_of_lt i.2 ) : ℝ ) + ( divFinIcc n hn ( i + 1 ) i.2 - divFinIcc n hn ( i : ℕ ) ( Nat.le_of_lt i.2 ) ) * t ) ( Icc 0 1 ) from ?_ using 1;
    · constructor <;> intro h;
      · intro h_maps_to
        apply ContDiffOn.comp (hγ (pickChart i)) (by
        exact ContDiffOn.add contDiffOn_const ( ContDiffOn.mul contDiffOn_const contDiffOn_id )) h_maps_to;
      · convert h _ |> ContDiffOn.congr <| fun t ht => ?_ using 1;
        · ext t; simp [Path.subpath];
          intro ht₁ ht₂;
          convert hcov i ⟨ divFinIcc n hn i.val ( le_of_lt i.isLt ) + ( divFinIcc n hn ( i.val + 1 ) i.isLt - divFinIcc n hn i.val ( le_of_lt i.isLt ) ) * t, by
            simp +decide [ divFinIcc_val ];
            constructor <;> nlinarith [ show ( i : ℝ ) + 1 ≤ n by norm_cast; exact Nat.succ_le_of_lt i.2, show ( i : ℝ ) ≥ 0 by positivity, div_mul_cancel₀ ( ( i : ℝ ) + 1 ) ( by positivity : ( n : ℝ ) ≠ 0 ), div_mul_cancel₀ ( ( i : ℝ ) ) ( by positivity : ( n : ℝ ) ≠ 0 ) ] ⟩ _ _ using 1
          generalize_proofs at *;
          · refine DFunLike.congr_arg γ (Subtype.ext ?_)
            simp only [Set.Icc.coe_convexComb, divFinIcc_val, Set.coe_projIcc]
            rw [min_eq_right ht₂, max_eq_right ht₁]
            push_cast
            ring
          · simp +decide [ divFinIcc ];
            exact mul_nonneg ( sub_nonneg.2 <| by gcongr ; linarith ) ht₁;
          · all_goals generalize_proofs at *;
            simp +decide [ divFinIcc ];
            nlinarith [ show ( i : ℝ ) + 1 ≤ n by norm_cast, div_mul_cancel₀ ( ( i : ℝ ) + 1 ) ( by positivity : ( n : ℝ ) ≠ 0 ), div_mul_cancel₀ ( ( i : ℝ ) ) ( by positivity : ( n : ℝ ) ≠ 0 ) ];
        · intro t ht
          simp [divFinIcc] at *;
          convert hcov i ( ↑↑i / ↑n + ( ( ↑↑i + 1 ) / ↑n - ↑↑i / ↑n ) * t ) _ _ _ _ using 1 <;> ring_nf <;> norm_num [ hn.ne' ];
          any_goals nlinarith [ inv_pos.2 ( by positivity : 0 < ( n : ℝ ) ) ];
          grind;
          nlinarith [ show ( i : ℝ ) + 1 ≤ n by norm_cast; linarith [ Fin.is_lt i ], inv_mul_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ];
        · simp +decide [ Path.subpath, Path.extend ];
          simp +decide [ IccExtend ];
          simp +decide [ projIcc ];
          obtain ⟨ht₁, ht₂⟩ := ht
          refine congrArg (⇑(chartAt E (pickChart i))) (DFunLike.congr_arg γ (Subtype.ext ?_))
          simp only [Set.Icc.coe_convexComb, divFinIcc_val]
          rw [min_eq_right ht₂, max_eq_right ht₁]
          have hpos : (0:ℝ) < n := by positivity
          have hni : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.2
          have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
          have hninv : (0:ℝ) ≤ (↑n)⁻¹ := by positivity
          have hsum : ((i:ℝ) / ↑n + (((i:ℝ) + 1) / ↑n - (i:ℝ) / ↑n) * t)
              = ((i:ℝ) + t) / ↑n := by
            field_simp; ring
          have haff₀ : 0 ≤ ((i:ℝ) / ↑n + (((i:ℝ) + 1) / ↑n - (i:ℝ) / ↑n) * t) := by
            rw [hsum]; apply div_nonneg _ (le_of_lt hpos); nlinarith
          have haff₁ : ((i:ℝ) / ↑n + (((i:ℝ) + 1) / ↑n - (i:ℝ) / ↑n) * t) ≤ 1 := by
            rw [hsum, div_le_one hpos]; nlinarith
          rw [min_eq_right haff₁, max_eq_right haff₀]
          push_cast
          ring
    · fun_prop;
  have h_cont_diff : ContinuousOn (fun t => (chartedFormPullback (chartAt E (pickChart i)) ω) ((chartAt E (pickChart i)) ((γ.subpath (divFinIcc n hn ↑i.val (le_of_lt i.isLt)) (divFinIcc n hn (↑i.val + 1) i.isLt)).extend t)) (derivWithin ((chartAt E (pickChart i)) ∘ ⇑(γ.subpath (divFinIcc n hn ↑i.val (le_of_lt i.isLt)) (divFinIcc n hn (↑i.val + 1) i.isLt)).extend) (Icc 0 1) t)) (Set.Icc 0 1) := by
    refine' ContinuousOn.clm_apply _ _;
    · refine' ContinuousOn.comp
        ( JacobianChallenge.Periods.ChartedFormPullbackContinuous.chartedFormPullback_chartAt_continuousOn
            (pickChart i) ω ) _ _;
      · refine' h_cont_diff.continuousOn.mono _;
        intro t ht;
        simp_all +decide [ Path.subpath ];
        have hpos : (0:ℝ) < n := by positivity
        have hni : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.2
        have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
        have hninv : (0:ℝ) ≤ (↑n)⁻¹ := by positivity
        have hinv : (n:ℝ) * (↑n)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
        convert hcov i _ _ _ _ _ using 1 <;>
          simp only [Set.Icc.coe_convexComb, divFinIcc_val, div_eq_mul_inv] <;>
          push_cast <;>
          nlinarith [ht.1, ht.2, hninv, hinv, hni, hi0,
            mul_nonneg ht.1 hninv, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hninv,
            mul_nonneg ht.1 hi0, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hi0,
            mul_le_of_le_one_left hninv ht.2,
            mul_le_of_le_one_left hninv (by linarith : (1:ℝ) - t ≤ 1)]
      · intro t ht;
        obtain ⟨ht₁, ht₂⟩ := ht
        have hpos : (0:ℝ) < n := by positivity
        have hni : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.2
        have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
        have hninv : (0:ℝ) ≤ (↑n)⁻¹ := by positivity
        simp only [Path.subpath, Path.coe_mk_mk,
          Path.extend, Set.IccExtend]
        apply (chartAt E (pickChart i)).map_source
        have hcoe2 : (1 - t) * ((i:ℝ) / n) + t * (((i:ℝ) + 1) / n) = ((i:ℝ) + t) / n := by
          field_simp; ring
        refine hcov i _ ?_ ?_
        · simp only [Set.Icc.coe_convexComb, divFinIcc_val, Set.coe_projIcc, min_eq_right ht₂, max_eq_right ht₁]
          push_cast
          rw [hcoe2, div_le_div_iff_of_pos_right hpos]
          linarith
        · simp only [Set.Icc.coe_convexComb, divFinIcc_val, Set.coe_projIcc, min_eq_right ht₂, max_eq_right ht₁]
          push_cast
          rw [hcoe2, div_le_div_iff_of_pos_right hpos]
          linarith
    · have h_cont_diff : ContDiffOn ℝ 1 (⇑(chartAt E (pickChart i)) ∘ ⇑(γ.subpath (divFinIcc n hn ↑i.val (le_of_lt i.isLt)) (divFinIcc n hn (↑i.val + 1) i.isLt)).extend) (Icc 0 1) := by
        refine' h_cont_diff.mono _;
        intro t ht;
        obtain ⟨ht₁, ht₂⟩ := ht
        have hpos : (0:ℝ) < n := by positivity
        have hni : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.2
        have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
        have hninv : (0:ℝ) ≤ (↑n)⁻¹ := by positivity
        have hcoe2 : (1 - t) * ((i:ℝ) / n) + t * (((i:ℝ) + 1) / n) = ((i:ℝ) + t) / n := by
          field_simp; ring
        refine ⟨?_, ⟨ht₁, ht₂⟩⟩
        simp only [Set.mem_preimage, Path.subpath, Path.coe_mk_mk,
          Path.extend, Set.IccExtend]
        refine hcov i _ ?_ ?_
        · simp only [Set.Icc.coe_convexComb, divFinIcc_val, Set.coe_projIcc, min_eq_right ht₂, max_eq_right ht₁]
          push_cast
          rw [hcoe2, div_le_div_iff_of_pos_right hpos]
          linarith
        · simp only [Set.Icc.coe_convexComb, divFinIcc_val, Set.coe_projIcc, min_eq_right ht₂, max_eq_right ht₁]
          push_cast
          rw [hcoe2, div_le_div_iff_of_pos_right hpos]
          linarith
      have := h_cont_diff.continuousOn_derivWithin;
      exact this ( uniqueDiffOn_Icc ( by norm_num ) ) le_rfl;
  rw [ intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one ];
  convert h_cont_diff.integrableOn_Icc using 1;
  infer_instance


theorem pathIntegralViaCoverWith_refinement_invariant'
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (hγ : ∀ (p : X), ContDiffOn ℝ 1 ((chartAt E p) ∘ γ.extend)
          (γ.extend ⁻¹' (chartAt E p).source ∩ Set.Icc 0 1))
    (_n : ℕ) (_hn : 0 < _n) (_pickChart : Fin _n → X)
    (_hcov : ∀ (i : Fin _n) (t : unitInterval),
      (i : ℝ) / _n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / _n →
      γ t ∈ (chartAt E (_pickChart i)).source)
    (_n' : ℕ) (_hn' : 0 < _n') (_pickChart' : Fin _n' → X)
    (_hcov' : ∀ (i : Fin _n') (t : unitInterval),
      (i : ℝ) / _n' ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / _n' →
      γ t ∈ (chartAt E (_pickChart' i)).source) :
    pathIntegralViaCoverWith ω γ _n _hn _pickChart _hcov =
      pathIntegralViaCoverWith ω γ _n' _hn' _pickChart' _hcov' := by
  -- Both sides refine to the common multiple _n * _n'.
  -- Step 1: Refine first partition from _n to _n * _n'.
  have hcovA : ∀ (j : Fin (_n * _n')) (t : unitInterval),
      (j : ℝ) / ((_n * _n' : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / ((_n * _n' : ℕ) : ℝ) →
      γ t ∈ (chartAt E (_pickChart
        ⟨j.val / _n', (Nat.div_lt_iff_lt_mul _hn').mpr j.isLt⟩)).source :=
    coverage_refinement γ _n _n' _hn _hn' _pickChart _hcov
  have hintA : ∀ i : Fin _n, IntervalIntegrable
      (fun t => (chartedFormPullback (chartAt E (_pickChart i)) ω)
        ((chartLift (chartAt E (_pickChart i))
          (γ.subpath (divFinIcc _n _hn i.val (le_of_lt i.isLt))
                     (divFinIcc _n _hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ _n _hn _pickChart _hcov i)).extend t)
        (derivWithin (chartLift (chartAt E (_pickChart i))
          (γ.subpath (divFinIcc _n _hn i.val (le_of_lt i.isLt))
                     (divFinIcc _n _hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ _n _hn _pickChart _hcov i)).extend
          (Set.Icc 0 1) t))
      volume 0 1 :=
    segment_integrability ω γ hγ _n _hn _pickChart _hcov
  have h_lhs := pathIntegralViaCoverWith_refine_to_multiple ω γ _n _n' _hn _hn'
    _pickChart _hcov hcovA hintA
  -- Step 2: Refine second partition from _n' to _n' * _n.
  have hcovB : ∀ (j : Fin (_n' * _n)) (t : unitInterval),
      (j : ℝ) / ((_n' * _n : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / ((_n' * _n : ℕ) : ℝ) →
      γ t ∈ (chartAt E (_pickChart'
        ⟨j.val / _n, (Nat.div_lt_iff_lt_mul _hn).mpr j.isLt⟩)).source :=
    coverage_refinement γ _n' _n _hn' _hn _pickChart' _hcov'
  have hintB : ∀ i : Fin _n', IntervalIntegrable
      (fun t => (chartedFormPullback (chartAt E (_pickChart' i)) ω)
        ((chartLift (chartAt E (_pickChart' i))
          (γ.subpath (divFinIcc _n' _hn' i.val (le_of_lt i.isLt))
                     (divFinIcc _n' _hn' (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ _n' _hn' _pickChart' _hcov' i)).extend t)
        (derivWithin (chartLift (chartAt E (_pickChart' i))
          (γ.subpath (divFinIcc _n' _hn' i.val (le_of_lt i.isLt))
                     (divFinIcc _n' _hn' (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ _n' _hn' _pickChart' _hcov' i)).extend
          (Set.Icc 0 1) t))
      volume 0 1 :=
    segment_integrability ω γ hγ _n' _hn' _pickChart' _hcov'
  have h_rhs := pathIntegralViaCoverWith_refine_to_multiple ω γ _n' _n _hn' _hn
    _pickChart' _hcov' hcovB hintB
  -- Step 3: Connect via chart-pick independence and Nat.mul_comm.
  rw [h_lhs, h_rhs]
  exact pathIntegralViaCoverWith_eq_of_size_eq ω γ
    (_n * _n') (_n' * _n) (Nat.mul_pos _hn _hn') (Nat.mul_pos _hn' _hn)
    (Nat.mul_comm _n _n')
    _ _ hcovA hcovB

end JacobianChallenge.Periods
