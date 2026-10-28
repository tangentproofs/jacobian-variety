/-!
# RETIRED — not built, not imported

Declarations moved verbatim out of `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` on branch `independent-repair`
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
**Structural axiom (CRS-fnB).** The eval-at-1 of a smooth
cotangent-bundle section, viewed as `X → ℂ`, is continuous.
-/
theorem ContMDiffSection.continuous_eval_at_one
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    Continuous (fun x => (σ.toFun x) (1 : ℂ)) :=
  continuous_eval_at_one_of_contMDiffSection σ

/--
**Structural axiom (CRS-fn).** The fiber-norm of a smooth section
is continuous.
-/
theorem holomorphicOneForm_fiberNorm_continuous_via_eval_at_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    Continuous (ContMDiffSection.fiberNorm σ) := by
  -- Continuous on a function is proved by showing it's equal to a continuous one.
  have h : ContMDiffSection.fiberNorm σ = (fun x => ‖(σ.toFun x) (1 : ℂ)‖) := by
    funext x
    exact ContMDiffSection.fiberNorm_eq_abs_eval_one σ x
  rw [h]
  exact (ContMDiffSection.continuous_eval_at_one σ).norm

theorem holomorphicOneForm_fiberNorm_continuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    Continuous (ContMDiffSection.fiberNorm σ) :=
  holomorphicOneForm_fiberNorm_continuous_via_eval_at_one σ

/--
Package the fiberwise-norm-continuity into the `hcompat` form
used by `SectionSupNorm` and `SectionMetric`.
-/
theorem holomorphicOneForm_hcompat
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    ∀ (σ : HolomorphicOneForm ℂ X),
      Continuous (ContMDiffSection.fiberNorm σ) :=
  holomorphicOneForm_fiberNorm_continuous X

/--
The `MetricSpace` on `HolomorphicOneForm ℂ X` induced by the
sup-norm distance `dist σ τ = ⨆ x, ‖(σ - τ) x‖`. Constructed from
the individual axioms proved in `SectionMetric.lean`.
-/
@[reducible]
noncomputable def holomorphicOneForm_metricSpace
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    MetricSpace (HolomorphicOneForm ℂ X) :=
  let hc := holomorphicOneForm_hcompat X
  { dist := SectionMetric.dist
    dist_self := SectionMetric.dist_self
    dist_comm := SectionMetric.dist_comm hc
    dist_triangle := SectionMetric.dist_triangle hc
    eq_of_dist_eq_zero := fun h => by
      by_cases hne : Nonempty X
      · exact SectionMetric.eq_of_dist_eq_zero hc h
      · rw [not_nonempty_iff] at hne
        exact ContMDiffSection.ext fun x => (hne.false x).elim
    toUniformSpace := UniformSpace.ofDist SectionMetric.dist
      SectionMetric.dist_self (SectionMetric.dist_comm hc)
      (SectionMetric.dist_triangle hc)
    toBornology := Bornology.ofDist SectionMetric.dist
      (SectionMetric.dist_comm hc) (SectionMetric.dist_triangle hc) }

/--
**Structural axiom (CRS-step1).** Pointwise convergence in each
Banach fiber: a sup-norm Cauchy sequence is uniformly Cauchy hence
pointwise Cauchy in each fiber `CotangentSpace ℂ X x`, which is a
Banach space, so the pointwise limit exists.

Cross-ref: `tex/sections/02-holomorphic-forms-finite-dim.tex`,
`lem:holomorphic-one-form-pointwise-limit-exists`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_pointwise_limit_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ _σ) :
    -- A pointwise limit on the underlying total-space type exists.
    -- The richer statement (smoothness, sup-norm convergence) is split
    -- off into companion steps.
    True := trivial

/--
A genuine metric ingredient for CRS-step1: Cauchy in the global
sup-norm metric implies Cauchy after evaluation in each cotangent
fiber.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_pointwise_cauchy
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (x : X) :
    CauchySeq (fun n => (σ n).toFun x) := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hσ : CauchySeq σ := hCauchy
  rcases (Metric.cauchySeq_iff.1 hσ ε hε) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  have hc := holomorphicOneForm_hcompat X
  calc
    dist ((σ m).toFun x) ((σ n).toFun x)
        = ‖(σ m).toFun x - (σ n).toFun x‖ := dist_eq_norm _ _
    _ = ‖(σ m - σ n).toFun x‖ := by
        have hsub : (σ m - σ n).toFun x = (σ m).toFun x - (σ n).toFun x := by
          change ((σ m - σ n : HolomorphicOneForm ℂ X) : ∀ x, _) x =
            (σ m : ∀ x, _) x - (σ n : ∀ x, _) x
          rw [ContMDiffSection.coe_sub]
          rfl
        rw [hsub]
    _ ≤ SectionSupNorm.supNorm (σ m - σ n) :=
        le_ciSup (SectionSupNorm.bddAbove_range_norm hc (σ m - σ n)) x
    _ = Dist.dist (σ m) (σ n) := rfl

/--
The scalar coefficient obtained by evaluating a sup-norm Cauchy
sequence at `x` and then at the tangent vector `1` converges in `ℂ`.
This is the concrete coefficient-limit part of CRS-step1 used by the
eval-at-one scaffolding.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOne_tendsto_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (x : X) :
    ∃ c : ℂ,
      Filter.Tendsto (fun n => (σ n).toFun x (1 : ℂ)) Filter.atTop (nhds c) := by
  have hFiber : CauchySeq (fun n => (σ n).toFun x) :=
    holomorphicOneForm_supNorm_cauchySeq_pointwise_cauchy X σ hCauchy x
  exact cauchySeq_tendsto_of_complete
    ((ContinuousLinearMap.lipschitz_apply (1 : ℂ)).cauchySeq_comp hFiber)

/--
Uniform version of the coefficient Cauchy estimate: after evaluating
at the tangent vector `1`, the scalar coefficient functions are Cauchy
uniformly in `x`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOne_uniform_cauchy
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x : X,
      dist ((σ m).toFun x (1 : ℂ)) ((σ n).toFun x (1 : ℂ)) < ε := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  intro ε hε
  have hσ : CauchySeq σ := hCauchy
  rcases (Metric.cauchySeq_iff.1 hσ ε hε) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn x => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  have hc := holomorphicOneForm_hcompat X
  calc
    dist ((σ m).toFun x (1 : ℂ)) ((σ n).toFun x (1 : ℂ))
        = ‖(σ m).toFun x (1 : ℂ) - (σ n).toFun x (1 : ℂ)‖ := dist_eq_norm _ _
    _ = ‖(σ m - σ n).toFun x (1 : ℂ)‖ := by
        have hsub : (σ m - σ n).toFun x = (σ m).toFun x - (σ n).toFun x := by
          change ((σ m - σ n : HolomorphicOneForm ℂ X) : ∀ x, _) x =
            (σ m : ∀ x, _) x - (σ n : ∀ x, _) x
          rw [ContMDiffSection.coe_sub]
          rfl
        rw [hsub]
        rfl
    _ = ‖(σ m - σ n).toFun x‖ := by
        simpa [ContMDiffSection.fiberNorm] using
          (ContMDiffSection.fiberNorm_eq_abs_eval_one (σ m - σ n) x).symm
    _ ≤ SectionSupNorm.supNorm (σ m - σ n) :=
        le_ciSup (SectionSupNorm.bddAbove_range_norm hc (σ m - σ n)) x
    _ = Dist.dist (σ m) (σ n) := rfl

/--
Chosen pointwise scalar coefficient limit of a sup-norm Cauchy
sequence after evaluating at tangent vector `1`.
-/
noncomputable def holomorphicOneForm_supNorm_cauchySeq_evalOneLimit
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    X → ℂ :=
  fun x => Classical.choose
    (holomorphicOneForm_supNorm_cauchySeq_evalOne_tendsto_exists X σ hCauchy x)

theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_tendsto
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (x : X) :
    Filter.Tendsto (fun n => (σ n).toFun x (1 : ℂ)) Filter.atTop
      (nhds (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x)) :=
  Classical.choose_spec
    (holomorphicOneForm_supNorm_cauchySeq_evalOne_tendsto_exists X σ hCauchy x)

/--
The scalar coefficient functions obtained from a sup-norm Cauchy
sequence converge uniformly on `X` to the chosen pointwise coefficient
limit.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOne_tendstoUniformlyOn_univ
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    TendstoUniformlyOn
      (fun n x => (σ n).toFun x (1 : ℂ))
      (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy)
      Filter.atTop Set.univ := by
  refine UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto ?hUniformCauchy ?hPointwise
  · rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    rcases holomorphicOneForm_supNorm_cauchySeq_evalOne_uniform_cauchy X σ hCauchy ε hε with
      ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn x _hx
    exact hN m hm n hn x
  · intro x _hx
    exact holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_tendsto X σ hCauchy x

/--
The chosen scalar coefficient limit is continuous, as a uniform limit
of the continuous coefficient functions `x ↦ (σ n).toFun x 1`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_continuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    Continuous (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy) := by
  have hUniformOn :=
    holomorphicOneForm_supNorm_cauchySeq_evalOne_tendstoUniformlyOn_univ X σ hCauchy
  have hUniform :
      TendstoUniformly
        (fun n x => (σ n).toFun x (1 : ℂ))
        (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy)
        Filter.atTop := by
    rwa [← tendstoUniformlyOn_univ]
  exact hUniform.continuous
    (Filter.Frequently.of_forall fun n =>
      ContMDiffSection.continuous_eval_at_one (σ n))

/--
Once a holomorphic 1-form realizes the chosen scalar coefficient
limit, the original Cauchy sequence converges to it in the sup-norm
metric. This isolates the remaining analytic construction problem:
produce such a holomorphic section from the coefficient limit.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_tendsto_of_evalOneLimit
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (a : HolomorphicOneForm ℂ X)
    (ha : ∀ x : X,
      a.toFun x (1 : ℂ) =
        holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x) :
    @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) σ Filter.atTop
      (@nhds (HolomorphicOneForm ℂ X)
        (holomorphicOneForm_metricSpace X).toUniformSpace.toTopologicalSpace a) := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hUniformOn :=
    holomorphicOneForm_supNorm_cauchySeq_evalOne_tendstoUniformlyOn_univ X σ hCauchy
  have hEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hUniformOn (ε / 2) (half_pos hε))
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hc := holomorphicOneForm_hcompat X
  calc
    Dist.dist (σ n) a
        = SectionSupNorm.supNorm (σ n - a) := rfl
    _ ≤ ε / 2 := by
        show (⨆ x : X, ‖(σ n - a).toFun x‖) ≤ ε / 2
        refine @ciSup_le ℝ X _ _ (fun x : X => ‖(σ n - a).toFun x‖) (ε / 2) fun x => ?_
        have hpoint := hN n hn x (Set.mem_univ x)
        have hnorm :
            ‖(σ n - a).toFun x‖ =
              ‖(σ n).toFun x (1 : ℂ) -
                holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x‖ := by
          calc
            ‖(σ n - a).toFun x‖
                = ‖(σ n - a).toFun x (1 : ℂ)‖ := by
                    simpa [ContMDiffSection.fiberNorm] using
                      ContMDiffSection.fiberNorm_eq_abs_eval_one (σ n - a) x
            _ = ‖(σ n).toFun x (1 : ℂ) - a.toFun x (1 : ℂ)‖ := by
                    have hsub : (σ n - a).toFun x = (σ n).toFun x - a.toFun x := by
                      change ((σ n - a : HolomorphicOneForm ℂ X) : ∀ x, _) x =
                        (σ n : ∀ x, _) x - (a : ∀ x, _) x
                      rw [ContMDiffSection.coe_sub]
                      rfl
                    rw [hsub]
                    rfl
            _ = ‖(σ n).toFun x (1 : ℂ) -
                  holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x‖ := by
                    rw [ha x]
        change ‖(σ n - a).toFun x‖ ≤ ε / 2
        rw [hnorm]
        exact le_of_lt (by
          simpa [dist_eq_norm, norm_sub_rev] using hpoint)
    _ < ε := half_lt_self hε

/--
There is at most one holomorphic 1-form realizing the chosen scalar
coefficient limit.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_unique
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    {a b : HolomorphicOneForm ℂ X}
    (ha : ∀ x : X,
      a.toFun x (1 : ℂ) =
        holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x)
    (hb : ∀ x : X,
      b.toFun x (1 : ℂ) =
        holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x) :
    a = b :=
  holomorphicOneForm_ext_eval_one fun x => by rw [ha x, hb x]

/--
The canonical pointwise candidate for the limit section: in a
one-dimensional chart, the scalar coefficient limit `f x` determines
the cotangent vector `v ↦ f x * v`.
-/
noncomputable def holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (x : X) : CotangentSpace ℂ X x :=
  ContinuousLinearMap.toSpanSingleton ℂ
    (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x)

/--
The canonical candidate realizes the chosen scalar coefficient limit
when evaluated on the chart tangent vector `1`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun_apply_one
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (x : X) :
    holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun X σ hCauchy x (1 : ℂ) =
      holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x := by
  change
    (ContinuousLinearMap.toSpanSingleton ℂ
      (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x) :
        ℂ →L[ℂ] ℂ) (1 : ℂ) =
      holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/--
Mechanical bundle lift: a smooth scalar coefficient determines a smooth
cotangent-bundle section by `x ↦ (v ↦ f x * v)`.
-/
theorem holomorphicOneForm_toSpanSingleton_section_contMDiff
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {f : X → ℂ}
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ⊤ f) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ (CotangentModelFiber ℂ)))
      ⊤
      (fun x => Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) (E := CotangentSpace ℂ X) x
        (ContinuousLinearMap.toSpanSingleton ℂ (f x) : CotangentSpace ℂ X x)) := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  have hmodel :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ (CotangentModelFiber ℂ)) ⊤
        (fun x : X => ContinuousLinearMap.toSpanSingleton ℂ (f x)) x₀ := by
    exact ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).contDiff.contMDiff.contMDiffAt).comp
      x₀ (hf x₀)
  refine hmodel.congr_of_eventuallyEq ?_
  have htan : ∀ᶠ x in nhds x₀,
      x ∈ (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) x₀).baseSet := by
    exact (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have htriv : ∀ᶠ x in nhds x₀,
      x ∈ (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).baseSet := by
    exact (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  filter_upwards [htan, htriv] with x hxT hxC
  rw [hom_trivializationAt_apply]
  change ContinuousLinearMap.inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ))
      ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x
      (ContinuousLinearMap.toSpanSingleton ℂ (f x) : CotangentSpace ℂ X x) =
    ContinuousLinearMap.toSpanSingleton ℂ (f x)
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxC]
  have hxChart : x ∈ (chartAt ℂ x₀).source := by
    simpa [TangentBundle.trivializationAt_baseSet] using hxT
  have hachart : achart ℂ x = achart ℂ x₀ :=
    JacobianChallenge.Periods.achart_eq_of_mem_source hxChart
  have hsymm_apply (v : ℂ) :
      ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) x₀).symmL ℂ x)
          v = v := by
    have hsymm :
        (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) x₀).symmL ℂ x =
          (ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] TangentSpace (modelWithCornersSelf ℂ ℂ) x) := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hxChart]
      rw [hachart]
      ext
      exact (tangentBundleCore (modelWithCornersSelf ℂ ℂ) X).coordChange_self
        (achart ℂ x₀) x hxChart (1 : ℂ)
    rw [hsymm]
    rfl
  ext
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  change (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).continuousLinearEquivAt ℂ x hxC
      ((ContinuousLinearMap.toSpanSingleton ℂ (f x))
      (((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) x₀).symmL ℂ x)
        (1 : ℂ))) =
    (ContinuousLinearMap.toSpanSingleton ℂ (f x)) (1 : ℂ)
  rw [hsymm_apply]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/--
Eval-at-one of a holomorphic 1-form is a smooth scalar function.
-/
theorem ContMDiffSection.contMDiff_eval_at_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ⊤ (fun x : X => σ.toFun x (1 : ℂ)) := by
  intro x₀
  have hsection : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        (show (Bundle.Trivial X ℂ) x from σ.toFun x (1 : ℂ))) :=
    σ.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
  have hx := hsection x₀
  rw [Bundle.contMDiffAt_section] at hx
  refine hx.congr_of_eventuallyEq ?_
  filter_upwards with x
  simp

/--
Eval-at-one of a holomorphic 1-form is chart-locally holomorphic.
-/
theorem holomorphicOneForm_evalOne_isHolomorphicAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) (p : X) :
    IsHolomorphicAt (fun x : X => σ.toFun x (1 : ℂ)) p :=
  IsHolomorphicAt.of_contMDiff (ContMDiffSection.contMDiff_eval_at_one σ) p

/--
Under the project-local stable chart selector hypothesis, pulling a
coordinate-ball point back through the base chart keeps the same
`chartAt`.
-/
theorem chartAt_symm_chartAt_eq_of_mem_ball
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
 (p : X)
    {r : ℝ} {z : ℂ}
    (hball : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hz : z ∈ Metric.ball ((chartAt ℂ p) p) r) :
    chartAt ℂ ((chartAt ℂ p).symm z) = chartAt ℂ p :=
  JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source p
    ((chartAt ℂ p).symm z)
    (chartAt_symm_mem_source_of_mem_ball p hball hz)

/--
**Analytic provider.** The scalar coefficient limit of a sup-norm
Cauchy sequence of holomorphic 1-forms is holomorphic at every point.

This is the chart-local Weierstrass theorem for the scalar coefficient
functions. The surrounding lemmas reduce Banach completeness to this
one-dimensional analytic statement plus continuity and the mechanical
bundle lift.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_isHolomorphicAt
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (p : X) :
    IsHolomorphicAt (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy) p := by
  exact isHolomorphicAt_of_tendstoUniformlyOn_holomorphic
    (fun n x => (σ n).toFun x (1 : ℂ))
    (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy)
    p
    (fun n x => holomorphicOneForm_evalOne_isHolomorphicAt (σ n) x)
    (holomorphicOneForm_supNorm_cauchySeq_evalOne_tendstoUniformlyOn_univ X σ hCauchy)

/--
The scalar coefficient limit is smooth once the chart-local
Weierstrass holomorphicity provider is available.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_contMDiff
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ⊤ (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy) := by
  exact ContMDiff.of_isHolomorphic_and_continuous
    (fun p => holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_isHolomorphicAt X σ hCauchy p)
    (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_continuous X σ hCauchy)

/--
**Analytic provider.** The canonical pointwise candidate determined by
the uniform scalar coefficient limit is a smooth cotangent-bundle
section.

This is the chart-local Weierstrass step that remains after the
metric, uniform-convergence, and uniqueness parts have been proved.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun_contMDiff
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ (CotangentModelFiber ℂ)))
      ⊤
      (fun x => Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) x
        (holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun X σ hCauchy x)) := by
  simpa [holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun] using
    holomorphicOneForm_toSpanSingleton_section_contMDiff
      (X := X)
      (f := holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy)
      (holomorphicOneForm_supNorm_cauchySeq_evalOneLimit_contMDiff X σ hCauchy)

/--
**Structural axiom (CRS-step3-provider).** The chosen scalar coefficient
limit comes from an actual holomorphic 1-form.

This is now the precise analytic construction gap in the Banach proof:
the preceding lemmas show the coefficient limit exists, is continuous,
is uniform, and determines any candidate uniquely. What remains is the
chart-local Weierstrass argument that upgrades this continuous scalar
coefficient into a bundled `HolomorphicOneForm`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_exists_evalOneLimit_section
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ∃ a : HolomorphicOneForm ℂ X,
      ∀ x : X,
        a.toFun x (1 : ℂ) =
          holomorphicOneForm_supNorm_cauchySeq_evalOneLimit X σ hCauchy x := by
  refine ⟨
    { toFun := holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun X σ hCauchy
      contMDiff_toFun :=
        holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun_contMDiff X σ hCauchy },
    ?_⟩
  intro x
  exact holomorphicOneForm_supNorm_cauchySeq_evalOneLimitToFun_apply_one X σ hCauchy x

/--
**Structural axiom (CRS-step2).** Continuity of the pointwise
limit, via `TendstoUniformly.continuous`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_limit_continuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ _σ) :
    True := trivial

/--
**Structural axiom (CRS-step3).** Smoothness of the limit
(Weierstrass-on-sections). A uniform limit of holomorphic 1-forms
is holomorphic.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_limit_holomorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ _σ) :
    True := trivial

/--
**Structural axiom (CRS-step3′).** The limit of a Cauchy sequence
of holomorphic 1-forms is smooth (`ContMDiff`).

Since `HolomorphicOneForm ℂ X` is defined as `ContMDiffSection` (a
bundled `C^∞` section of the cotangent bundle), every element carries
a proof of `ContMDiff` by construction. In particular, once the limit
has been constructed as an element of `HolomorphicOneForm ℂ X` (via
the pointwise-limit + Weierstrass route encoded in steps 1–3), its
smoothness is automatic. This theorem records that fact explicitly.

Cross-ref: tex blueprint §14 R8-sub-B.B step 3; supplements
`holomorphicOneForm_supNorm_cauchySeq_limit_holomorphic`.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_limit_contMDiff
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ)
    (a : HolomorphicOneForm ℂ X)
    (_ha : @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) σ Filter.atTop
      (@nhds (HolomorphicOneForm ℂ X)
        (holomorphicOneForm_metricSpace X).toUniformSpace.toTopologicalSpace a)) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ (CotangentModelFiber ℂ)))
      ⊤ (fun x => Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) x (a x)) :=
  a.contMDiff

/--
**Structural axiom (CRS-step4-provider).** The sup-norm metric on the
current `HolomorphicOneForm ℂ X` section space is complete.

This is the precise local provider needed to close the Cauchy-sequence
form of the Banach-space obligation by Mathlib's
`cauchySeq_tendsto_of_complete`. Mathematically, this provider is the
Weierstrass closedness step: a sup-norm Cauchy sequence of smooth
cotangent sections has a uniform limit, and the chart-local
Weierstrass theorem identifies that limit again as a holomorphic
1-form.

Keeping this as a separate named obligation avoids hiding the analytic
gap inside the sequence assembly theorem below. The remaining proof
work is now exactly the local Weierstrass/closed-subspace argument,
rather than the routine `CompleteSpace` to `CauchySeq` conversion.
-/
theorem holomorphicOneForm_supNorm_completeSpace_of_weierstrass
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    @CompleteSpace (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toUniformSpace := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro σ hCauchy
  obtain ⟨a, ha⟩ :=
    holomorphicOneForm_supNorm_cauchySeq_exists_evalOneLimit_section X σ hCauchy
  exact ⟨a, holomorphicOneForm_supNorm_cauchySeq_tendsto_of_evalOneLimit X σ hCauchy a ha⟩

/--
**Structural axiom (CRS-step4).** Sup-norm convergence to the
pointwise/holomorphic limit, assembling the previous three steps.
-/
theorem holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ∃ a : HolomorphicOneForm ℂ X,
      @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) σ Filter.atTop
        (@nhds (HolomorphicOneForm ℂ X)
          (holomorphicOneForm_metricSpace X).toUniformSpace.toTopologicalSpace a) := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  haveI : CompleteSpace (HolomorphicOneForm ℂ X) :=
    holomorphicOneForm_supNorm_completeSpace_of_weierstrass X
  exact cauchySeq_tendsto_of_complete _hCauchy

/-- (Integrated from subagent a8db8a8f8315e0535's TOPDOWN split.) -/
theorem holomorphicOneForm_supNorm_cauchySeq_tendsto
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (_hCauchy : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      (holomorphicOneForm_metricSpace X).toUniformSpace _ σ) :
    ∃ a : HolomorphicOneForm ℂ X,
      @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) σ Filter.atTop
        (@nhds (HolomorphicOneForm ℂ X)
          (holomorphicOneForm_metricSpace X).toUniformSpace.toTopologicalSpace a) := by
  -- Decomposition (per docstring above):
  --   step1: extract pointwise limit a.toFun in each fiber.
  --   step2: continuity of the limit via TendstoUniformly.continuous.
  --   step3: smoothness of the limit via Weierstrass-on-sections.
  --   step4: sup-norm convergence assembly.
  -- Each step is a named structural axiom below.
  exact holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps X σ _hCauchy

/--
The canonical complete-space theorem for the sup-norm metric.
All non-trivial analytic content is isolated in
`holomorphicOneForm_supNorm_completeSpace_of_weierstrass`.
-/
theorem holomorphicOneForm_supNorm_completeSpace
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    @CompleteSpace (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toUniformSpace := by
  exact holomorphicOneForm_supNorm_completeSpace_of_weierstrass X

/--
The canonical sup-norm Banach data used by the compact Riemann
surface finite-dimensionality route.
-/
noncomputable def holomorphicOneForm_supNormBanachData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    HolomorphicOneFormBanachData X :=
  let hc := holomorphicOneForm_hcompat X
  { toNorm := ⟨SectionSupNorm.supNorm⟩
    toMetricSpace := holomorphicOneForm_metricSpace X
    dist_eq := fun _ _ => rfl
    norm_smul_le := SectionSupNorm.supNorm_smul_le hc
    complete := holomorphicOneForm_supNorm_completeSpace X
    norm_le := fun σ x =>
      le_ciSup (SectionSupNorm.bddAbove_range_norm hc σ) x }

/--
**(a) Topology of uniform convergence on compacts.**
On a compact 1-dimensional complex manifold, the space of holomorphic
1-forms admits a Banach-space structure realising the topology of uniform
convergence on compact sets, built atop the existing `ContMDiffSection`
additive / ℂ-module structure. (On a compact base this is the sup-norm
topology.)
-/
theorem holomorphicOneForm_normedSpace_uniformOnCompact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    Nonempty (HolomorphicOneFormBanachData X) :=
  ⟨holomorphicOneForm_supNormBanachData X⟩

/--
Membership in the closed unit ball for the canonical sup-norm metric
gives a pointwise cotangent-fiber norm bound.
-/
theorem holomorphicOneForm_supNorm_closedBall_pointwise_norm_le
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ : HolomorphicOneForm ℂ X}
    (hσ : σ ∈ @Metric.closedBall (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1)
    (x : X) :
    ‖σ.1 x‖ ≤ 1 := by
  let B := holomorphicOneForm_supNormBanachData X
  have hdist : @dist (HolomorphicOneForm ℂ X) B.toMetricSpace.toDist σ 0 ≤ 1 := by
    simpa [B, Metric.mem_closedBall] using hσ
  have hnorm : B.toNorm.norm σ ≤ 1 := by
    have hnorm_sub : B.toNorm.norm (σ - 0) ≤ 1 := by
      simpa [B.dist_eq σ 0] using hdist
    simpa [sub_zero] using hnorm_sub
  exact le_trans (B.norm_le σ x) hnorm

/--
Scalar coefficient version of
`holomorphicOneForm_supNorm_closedBall_pointwise_norm_le`, after
evaluating a cotangent vector on the unit tangent vector `1`.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOne_norm_le
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ : HolomorphicOneForm ℂ X}
    (hσ : σ ∈ @Metric.closedBall (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1)
    (x : X) :
    ‖σ.1 x (1 : ℂ)‖ ≤ 1 := by
  have h := holomorphicOneForm_supNorm_closedBall_pointwise_norm_le X hσ x
  have hEq : ‖σ.1 x‖ = ‖σ.1 x (1 : ℂ)‖ :=
    ContMDiffSection.fiberNorm_eq_abs_eval_one σ x
  rwa [← hEq]

/--
Pointwise compact-orbit form for Arzelà-Ascoli: scalar coefficients of
sup-norm unit-ball sections lie in the closed unit disk of `ℂ`.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOne_mem_closedBall
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ : HolomorphicOneForm ℂ X}
    (hσ : σ ∈ @Metric.closedBall (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1)
    (x : X) :
    σ.1 x (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact holomorphicOneForm_supNorm_closedBall_evalOne_norm_le X hσ x

/--
The eval-at-one scalar coefficient of a holomorphic 1-form, packaged
as a bounded continuous function on compact `X`.
-/
noncomputable def holomorphicOneForm_evalOneBCF
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    BoundedContinuousFunction X ℂ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun x => σ.1 x (1 : ℂ)
      continuous_toFun := ContMDiffSection.continuous_eval_at_one σ }

theorem holomorphicOneForm_evalOneBCF_apply
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) (x : X) :
    holomorphicOneForm_evalOneBCF X σ x = σ.1 x (1 : ℂ) :=
  rfl

/--
Scalar bounded-continuous-function family obtained from the canonical
sup-norm closed unit ball.
-/
noncomputable def holomorphicOneForm_supNorm_closedBall_evalOneBCFSet
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    Set (BoundedContinuousFunction X ℂ) :=
  (fun σ : HolomorphicOneForm ℂ X => holomorphicOneForm_evalOneBCF X σ) ''
    @Metric.closedBall (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1

/--
Every scalar bounded-continuous function in the eval-at-one image of
the sup-norm unit ball takes values in the compact closed unit disk.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_value_mem_closedUnitDisk
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {f : BoundedContinuousFunction X ℂ}
    (hf : f ∈ holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X)
    (x : X) :
    f x ∈ Metric.closedBall (0 : ℂ) 1 := by
  rcases hf with ⟨σ, hσ, rfl⟩
  exact holomorphicOneForm_supNorm_closedBall_evalOne_mem_closedBall X hσ x

/--
Arzelà-Ascoli reduction for the scalar eval-at-one image of the
sup-norm unit ball: after the planned Cauchy-estimate equicontinuity
lemma is supplied, this image is totally bounded in the bounded
continuous function uniform metric.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_totallyBounded_of_equicontinuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hEq : Equicontinuous
      ((↑) :
        holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X →
          X → ℂ)) :
    TotallyBounded (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X) := by
  have hcompactClosure :
      IsCompact (closure (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X)) :=
    BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : ℂ) 1)
      complex_closedUnitDisk_isCompact
      (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X)
      (fun f x hf =>
        holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_value_mem_closedUnitDisk X hf x)
      hEq
  exact hcompactClosure.totallyBounded.subset subset_closure

/--
The canonical sup-norm distance on holomorphic 1-forms is exactly the
uniform distance between their eval-at-one bounded continuous scalar
coefficients.
-/
theorem holomorphicOneForm_evalOneBCF_dist_eq
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ τ : HolomorphicOneForm ℂ X) :
    @dist (HolomorphicOneForm ℂ X) (holomorphicOneForm_metricSpace X).toDist σ τ =
      dist (holomorphicOneForm_evalOneBCF X σ) (holomorphicOneForm_evalOneBCF X τ) := by
  calc
    @dist (HolomorphicOneForm ℂ X) (holomorphicOneForm_metricSpace X).toDist σ τ
        = SectionSupNorm.supNorm (σ - τ) := rfl
    _ = ⨆ x : X, ‖(σ - τ).toFun x (1 : ℂ)‖ := by
        unfold SectionSupNorm.supNorm
        exact iSup_congr fun x =>
          ContMDiffSection.fiberNorm_eq_abs_eval_one (σ - τ) x
    _ = ⨆ x : X,
          dist ((holomorphicOneForm_evalOneBCF X σ) x)
            ((holomorphicOneForm_evalOneBCF X τ) x) := by
        exact iSup_congr fun x => by
          have hsub : (σ - τ).toFun x = σ.toFun x - τ.toFun x := by
            change ((σ - τ : HolomorphicOneForm ℂ X) : ∀ x, _) x =
              (σ : ∀ x, _) x - (τ : ∀ x, _) x
            rw [ContMDiffSection.coe_sub]
            rfl
          rw [hsub]
          simp [holomorphicOneForm_evalOneBCF, dist_eq_norm]
    _ = dist (holomorphicOneForm_evalOneBCF X σ) (holomorphicOneForm_evalOneBCF X τ) := by
        rw [BoundedContinuousFunction.dist_eq_iSup]

/--
If the scalar eval-at-one image of the canonical sup-norm unit ball is
totally bounded, then the original canonical sup-norm unit ball of
holomorphic 1-forms is totally bounded. The proof pulls total
boundedness back along the eval-at-one isometry.
-/
theorem holomorphicOneForm_supNorm_closedBall_totallyBounded_of_evalOneBCFSet
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hScalar : TotallyBounded (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X)) :
    HolomorphicOneFormClosedBallTotallyBounded X
      (holomorphicOneForm_supNormBanachData X) := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := holomorphicOneForm_metricSpace X
  let f : HolomorphicOneForm ℂ X → BoundedContinuousFunction X ℂ :=
    fun σ => holomorphicOneForm_evalOneBCF X σ
  have hfIso : Isometry f :=
    Isometry.of_dist_eq fun σ τ =>
      (holomorphicOneForm_evalOneBCF_dist_eq X σ τ).symm
  have hf : IsUniformInducing f :=
    hfIso.isUniformInducing
  have hpre : TotallyBounded (f ⁻¹' holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X) :=
    totallyBounded_preimage hf hScalar
  exact hpre.subset fun σ hσ => by
    change f σ ∈ holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X
    exact Set.mem_image_of_mem f hσ

/--
Current Montel reduction for the canonical sup-norm ball: it remains
only to prove equicontinuity of the scalar eval-at-one coefficient
family. Arzelà-Ascoli gives total boundedness of the scalar image, and
the eval-at-one isometry pulls it back to the holomorphic 1-form ball.
-/
theorem holomorphicOneForm_supNorm_closedBall_totallyBounded_of_evalOneBCFSet_equicontinuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hEq : Equicontinuous
      ((↑) :
        holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X →
          X → ℂ)) :
    HolomorphicOneFormClosedBallTotallyBounded X
      (holomorphicOneForm_supNormBanachData X) :=
  holomorphicOneForm_supNorm_closedBall_totallyBounded_of_evalOneBCFSet X
    (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_totallyBounded_of_equicontinuous X hEq)

/--
Chart-ball Cauchy-estimate modulus for the canonical sup-norm unit
ball. On a sufficiently small coordinate ball around `chartAt ℂ x₀ x₀`,
the scalar chart coefficients of all unit-ball holomorphic 1-forms
vary by less than `ε`.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOne_chart_ball_modulus
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    ∀ x₀ : X, ∀ ε > 0,
      ∃ r > 0,
        Metric.ball ((chartAt ℂ x₀) x₀) r ⊆ (chartAt ℂ x₀).target ∧
        ∀ (σ : HolomorphicOneForm ℂ X),
          σ ∈ @Metric.closedBall (HolomorphicOneForm ℂ X)
            (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1 →
          ∀ z ∈ Metric.ball ((chartAt ℂ x₀) x₀) r,
            dist (σ.toFun x₀ (1 : ℂ))
              (σ.toFun ((chartAt ℂ x₀).symm z) (1 : ℂ)) < ε := by
  intro x₀ ε hε
  rcases exists_chartAt_target_ball x₀ with ⟨R, hR_pos, hR_target⟩
  let r : ℝ := min (R / 2) (ε * R / 4)
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_le_R : r ≤ R := by
    calc
      r ≤ R / 2 := min_le_left _ _
      _ ≤ R := by linarith
  have hr_lt_epsR_div_two : (2 / R) * r < ε := by
    have hr_le_epsR_div_four : r ≤ ε * R / 4 := min_le_right _ _
    have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
    have hmul : (2 / R) * r ≤ (2 / R) * (ε * R / 4) := by
      gcongr
    have hsimp : (2 / R) * (ε * R / 4) = ε / 2 := by
      field_simp [hR_pos.ne']
      ring
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt (hmul.trans_eq hsimp) hhalf
  refine ⟨r, hr_pos, ?_, ?_⟩
  · intro z hz
    exact hR_target (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le hr_le_R))
  · intro σ hσ z hz
    let F : ℂ → ℂ := fun w => σ.toFun ((chartAt ℂ x₀).symm w) (1 : ℂ)
    have hdiff : DifferentiableOn ℂ F (Metric.ball ((chartAt ℂ x₀) x₀) R) := by
      simpa [F] using
        differentiableOn_chart_symm_of_forall_isHolomorphicAt_on_ball
          (f := fun x : X => σ.toFun x (1 : ℂ)) x₀ hR_target
          (fun x => holomorphicOneForm_evalOne_isHolomorphicAt σ x)
    have hmaps :
        Set.MapsTo F (Metric.ball ((chartAt ℂ x₀) x₀) R)
          (Metric.closedBall (F ((chartAt ℂ x₀) x₀)) 2) := by
      intro w hw
      have hw_source : (chartAt ℂ x₀).symm w ∈ (chartAt ℂ x₀).source :=
        chartAt_symm_mem_source_of_mem_ball x₀ hR_target hw
      have hw_bound :
          ‖σ.toFun ((chartAt ℂ x₀).symm w) (1 : ℂ)‖ ≤ 1 :=
        holomorphicOneForm_supNorm_closedBall_evalOne_norm_le X hσ _
      have hcenter_bound : ‖σ.toFun x₀ (1 : ℂ)‖ ≤ 1 :=
        holomorphicOneForm_supNorm_closedBall_evalOne_norm_le X hσ x₀
      have hcenter :
          F ((chartAt ℂ x₀) x₀) = σ.toFun x₀ (1 : ℂ) := by
        exact congrArg (fun x => σ.toFun x (1 : ℂ))
          ((chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀))
      have hdist_le :
          dist (F w) (F ((chartAt ℂ x₀) x₀)) ≤ 2 := by
        have hFw : ‖F w‖ ≤ 1 := by
          simpa [F] using hw_bound
        have hFc : ‖F ((chartAt ℂ x₀) x₀)‖ ≤ 1 := by
          simpa [hcenter] using hcenter_bound
        calc
          dist (F w) (F ((chartAt ℂ x₀) x₀))
              ≤ ‖F w‖ + ‖F ((chartAt ℂ x₀) x₀)‖ := dist_le_norm_add_norm _ _
          _ ≤ 1 + 1 := add_le_add hFw hFc
          _ = 2 := by norm_num
      simpa [Metric.mem_closedBall] using hdist_le
    have hzR : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) R :=
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le hr_le_R)
    have hschwarz :=
      Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := F)
        hdiff hmaps hzR
    have hzdist : dist z ((chartAt ℂ x₀) x₀) < r :=
      Metric.mem_ball.mp hz
    have hdist_lt : dist (F z) (F ((chartAt ℂ x₀) x₀)) < ε := by
      have hmul_lt : (2 / R) * dist z ((chartAt ℂ x₀) x₀) < ε := by
        exact lt_trans (mul_lt_mul_of_pos_left hzdist (by positivity))
          hr_lt_epsR_div_two
      exact lt_of_le_of_lt hschwarz hmul_lt
    have hcenter :
        F ((chartAt ℂ x₀) x₀) = σ.toFun x₀ (1 : ℂ) := by
      exact congrArg (fun x => σ.toFun x (1 : ℂ))
        ((chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀))
    simpa [F, hcenter, dist_comm] using hdist_lt

/--
Local Cauchy-estimate modulus for the canonical sup-norm unit ball:
near every base point `x₀`, one neighborhood works uniformly for all
holomorphic 1-forms in the closed unit ball.

This is the analytic heart of Montel in this file. In a chart, it is
the usual Cauchy derivative estimate on a smaller disc, transported
back to `X`.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOne_local_cauchy_modulus
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    ∀ x₀ : X, ∀ ε > 0,
      ∃ U ∈ nhds x₀,
        ∀ (σ : HolomorphicOneForm ℂ X),
          σ ∈ @Metric.closedBall (HolomorphicOneForm ℂ X)
            (holomorphicOneForm_metricSpace X).toPseudoMetricSpace 0 1 →
          ∀ x ∈ U,
            dist (σ.toFun x₀ (1 : ℂ)) (σ.toFun x (1 : ℂ)) < ε := by
  intro x₀ ε hε
  rcases holomorphicOneForm_supNorm_closedBall_evalOne_chart_ball_modulus X x₀ ε hε with
    ⟨r, hr_pos, hball_target, hdist⟩
  let U : Set X :=
    (chartAt ℂ x₀).source ∩
      (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) r
  have hsource_nhds : (chartAt ℂ x₀).source ∈ nhds x₀ :=
    chart_source_mem_nhds ℂ x₀
  have hpre_nhds :
      (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) r ∈ nhds x₀ := by
    exact ((chartAt ℂ x₀).continuousAt (mem_chart_source ℂ x₀)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr_pos)
  refine ⟨U, Filter.inter_mem hsource_nhds hpre_nhds, ?_⟩
  intro σ hσ x hx
  rcases hx with ⟨hx_source, hx_ball⟩
  have hchart := hdist σ hσ ((chartAt ℂ x₀) x) hx_ball
  have hx_eq : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x) = x :=
    (chartAt ℂ x₀).left_inv hx_source
  rw [← hx_eq]
  exact hchart

/--
Pointwise epsilon-neighborhood form of the remaining Cauchy-estimate
input. Around each base point `x₀`, all scalar eval-at-one
coefficients from the canonical sup-norm unit ball vary by less than
`ε` on one common neighborhood of `x₀`.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_eventually_dist_lt
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    ∀ x₀ : X, ∀ ε > 0,
      ∀ᶠ x in nhds x₀,
        ∀ f : holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X,
          dist ((f : BoundedContinuousFunction X ℂ) x₀)
            ((f : BoundedContinuousFunction X ℂ) x) < ε := by
  intro x₀ ε hε
  rcases holomorphicOneForm_supNorm_closedBall_evalOne_local_cauchy_modulus X x₀ ε hε with
    ⟨U, hU, hUdist⟩
  filter_upwards [hU] with x hx f
  rcases f.2 with ⟨σ, hσ, hfσ⟩
  have hdist := hUdist σ hσ x hx
  simpa [← hfσ, holomorphicOneForm_evalOneBCF] using hdist

/--
**Montel analytic provider.** The scalar eval-at-one coefficients of
holomorphic 1-forms in the canonical sup-norm closed unit ball are
equicontinuous as bounded continuous functions.

This is the remaining Cauchy-estimate obligation: locally in a complex
chart, the unit sup-norm bound gives a uniform derivative bound on a
smaller disc, hence a uniform modulus of continuity. The surrounding
theorems already turn this into total boundedness by Mathlib's
Arzelà-Ascoli theorem and the eval-at-one isometry.
-/
theorem holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_equicontinuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    Equicontinuous
      ((↑) :
        holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X →
          X → ℂ) := by
  exact equicontinuous_of_eventually_dist_lt
    ((↑) : holomorphicOneForm_supNorm_closedBall_evalOneBCFSet X → X → ℂ)
    (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_eventually_dist_lt X)

theorem holomorphicOneForm_supNorm_closedBall_totallyBounded
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    HolomorphicOneFormClosedBallTotallyBounded X
      (holomorphicOneForm_supNormBanachData X) := by
  exact holomorphicOneForm_supNorm_closedBall_totallyBounded_of_evalOneBCFSet_equicontinuous X
    (holomorphicOneForm_supNorm_closedBall_evalOneBCFSet_equicontinuous X)

@[reducible]
noncomputable def compactRiemannSurface_holomorphicOneFormMontelData_frontier
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 :
    HolomorphicOneFormMontelData X where
  B := holomorphicOneForm_supNormBanachData X
  closedBall_totallyBounded := holomorphicOneForm_supNorm_closedBall_totallyBounded X
