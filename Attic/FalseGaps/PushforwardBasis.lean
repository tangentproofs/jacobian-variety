/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/TraceDegree/PushforwardBasis.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
Raw obligation: the trace lift preserves the period subgroup.

Assembly via:
* `mem_basisAlignedPeriodSubgroupConcrete_iff` (membership characterization);
* `pushforwardTraceLift_apply_holomorphicOneFormDualEquiv` (algebraic bridge);
* `periodPairing_pullbackFormsBundledLM` (Stokes naturality), instantiated
  with the path/chain Lipschitz hypotheses `cycleLipPath_obligation` and
  `cycleLipChain_obligation`;
* `holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete`
  (membership transport).

The genuinely geometric content is now isolated to named sorries:
the algebraic bridge above (a `LinearMap.dualMap` identity), the Stokes
naturality in `Periods/PullbackNaturality.lean`, and the C¹ regularity
obligation `pathPiecewiseC1_obligation`.
-/
theorem pushforwardTraceLift_preserves_lattice_raw
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup := by
  intro v hv
  -- Unfold to the concrete representative.
  show pushforwardTraceLift f hf v ∈ basisAlignedPeriodSubgroupConcrete Y
  -- Extract the witness functional φ from membership in the X-side subgroup.
  have hv' : v ∈ basisAlignedPeriodSubgroupConcrete X := hv
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv'
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv'
  -- φ is in the range of periodPairing; extract a cycle γ.
  change φ ∈ (periodPairing ℂ X).range at hφ_mem
  rw [AddMonoidHom.mem_range] at hφ_mem
  obtain ⟨γ, hγ⟩ := hφ_mem
  -- Apply the bridge + naturality.
  rw [← hφ_eq, ← hγ,
    pushforwardTraceLift_apply_holomorphicOneFormDualEquiv f hf]
  -- Now goal: holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ X γ ∘ pullbackFormsBundledLM ...) ∈ ...
  -- Use naturality: periodPairing X γ ∘ pullbackBundled = periodPairing Y (cyclePushforward γ).
  have hnat : (periodPairing ℂ X γ).comp (pullbackFormsBundledLM X Y f hf) =
      periodPairing ℂ Y (cyclePushforward f hf γ) := by
    refine LinearMap.ext fun η => ?_
    exact periodPairing_pullbackFormsBundledLM f hf γ η
      (fun γ' => cycleLipPath_obligation γ' _
        (pathPiecewiseC1_of_regularity γ').choose_spec)
      (fun m a' b' γs => cycleLipChain_obligation m a' b' γs
        (fun i => pathPiecewiseC1_of_regularity (γs i)))
  rw [hnat]
  -- Now: holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y (cyclePushforward f hf γ)) ∈ basisAlignedPeriodSubgroupConcrete Y.
  refine holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete Y ?_
  show periodPairing ℂ Y (cyclePushforward f hf γ) ∈ (periodPairing ℂ Y).range
  exact AddMonoidHom.mem_range.mpr ⟨cyclePushforward f hf γ, rfl⟩

/--
The analytic pushforward induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.

Note: `pushforwardTraceLiftCLM` has type `→L[ℂ]` while
`pushforwardTraceLift` has type `→+`; the underlying additive maps
agree definitionally (the `→L[ℂ]` and `→ₗ[ℂ]` and `→+` are all
extracted from the same matrix-transpose `Matrix.toLin'` value).
-/
noncomputable def analyticPushforward
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y where
  toFun := ComplexTorus.mapClm (pushforwardTraceLiftCLM f hf)
    (pushforwardTraceLift_preserves_lattice_raw f hf)
  map_zero' := (ComplexTorus.mapClm _ _).map_zero
  map_add' := (ComplexTorus.mapClm _ _).map_add
  continuous_toFun :=
    ComplexTorus.mapClm_continuous (pushforwardTraceLiftCLM f hf)
      (pushforwardTraceLift_preserves_lattice_raw f hf)

/--
Raw obligation: descent compatibility — `analyticPushforward` is
the descent of `pushforwardTraceLift` through the period quotient.
-/
theorem analyticPushforward_mk_spec_raw
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforward f hf
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y)
        (pushforwardTraceLift f hf v) := by
  change ComplexTorus.mapClm (pushforwardTraceLiftCLM f hf)
      (pushforwardTraceLift_preserves_lattice_raw f hf)
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
    ComplexTorus.mk _ (periodFullComplexLattice Y)
      (pushforwardTraceLift f hf v)
  rfl

/--
Raw obligation: the descended map is holomorphic.

The equation on `chart.source` uses `chart.left_inv'` plus
`mapClm`'s definition (`map_mk`).
-/
theorem analyticPushforward_contMDiff_raw
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) := by
  intro q
  set chartX :=
    chartAt (Fin (analyticGenus ℂ X) → ℂ) q with chartX_def
  have hsrc : q ∈ chartX.source := mem_chart_source _ q
  have hOpen : IsOpen chartX.source := chartX.open_source
  have hMem : chartX.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞) chartX chartX.source :=
    contMDiffOn_chart
  -- pushforwardTraceLiftCLM is ContMDiff (continuous linear map).
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (pushforwardTraceLiftCLM f hf) :=
    (pushforwardTraceLiftCLM f hf).contMDiff
  -- mk Y is ContMDiff.
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ Y) → ℂ)
          (periodFullComplexLattice Y)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLattice Y)
  -- Compose to get the auxiliary smooth function on chart.source.
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLattice Y)
          (pushforwardTraceLiftCLM f hf (chartX q')))
        chartX.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  -- On chart.source, analyticPushforward equals the auxiliary.
  have hEq : ∀ q' ∈ chartX.source,
      analyticPushforward f hf q' =
        ComplexTorus.mk _ (periodFullComplexLattice Y)
          (pushforwardTraceLiftCLM f hf (chartX q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLattice X)
        (chartX q') = q' := chartX.left_inv' hq'
    -- Rewrite q' on the LHS as mk (chartX q'), then invoke
    conv_lhs => rw [← hLeft]
    exact analyticPushforward_mk_spec_raw f hf (chartX q')
  -- ContMDiffOn on chart.source → ContMDiffAt at q.
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPushforward f hf) chartX.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact hEq q' hq'
  exact hOn.contMDiffAt hMem

theorem analyticPushforward_contMDiff_spec
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_raw f hf

lemma analyticPushforward_contMDiff
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_spec f hf

theorem pushforwardTraceLift_preserves_lattice
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup :=
  pushforwardTraceLift_preserves_lattice_raw f hf

theorem analyticPushforward_mk_spec
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforward f hf
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y)
        (pushforwardTraceLift f hf v) :=
  analyticPushforward_mk_spec_raw f hf v

theorem analyticPushforward_comp_spec
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    [PiecewiseC1PathRegularity Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec f hf v,
      analyticPushforward_mk_spec (g ∘ f) (hg.comp hf) v,
      analyticPushforward_mk_spec g hg (pushforwardTraceLift f hf v)]
  congr 1
  exact congr_fun (congr_arg _ (pushforwardTraceLift_comp_spec f hf g hg)) v

lemma analyticPushforward_comp_apply
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    [PiecewiseC1PathRegularity Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) :=
  analyticPushforward_comp_spec f hf g hg P

theorem analyticPushforward_id_eq [PiecewiseC1PathRegularity X] :
    analyticPushforward (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec id contMDiff_id v, pushforwardTraceLift_id]
  rfl

theorem analyticPushforward_id_spec [PiecewiseC1PathRegularity X]
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPushforward_id_eq]
  rfl

lemma analyticPushforward_id_apply [PiecewiseC1PathRegularity X]
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P :=
  analyticPushforward_id_spec P
