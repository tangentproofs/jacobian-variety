/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/TraceDegree/PullbackBasis.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
Raw geometric obligation: the corrected trace-dual pullback
preserves the period subgroup (in the contravariant direction).

This is the dual of `pushforwardTraceLift_preserves_lattice_raw` using
the **corrected** representative `traceDualPullbackLiftCLM` (= transpose
of the trace matrix). Mathematically, it relies on the naturality of
integration via the transfer map (pullback on cycles).

The proof decomposes into:
1. Membership witness: `transfer_functional_mem_periodSubgroup`
   (the substantive geometric content — transfer maps for branched covers,
   stated against the corrected trace-dual representative).
2. Algebraic assembly: the trace-dual pullback lift applied to a period
   vector equals the basis-aligned dual equiv applied to the transfer
   functional.
-/
theorem traceDualPullbackLift_preserves_lattice_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice Y).subgroup,
      traceDualPullbackLiftCLM f hf v ∈ (periodFullComplexLattice X).subgroup := by
  intro v hv
  -- Unfold to the concrete representative.
  show traceDualPullbackLiftCLM f hf v ∈ basisAlignedPeriodSubgroupConcrete X
  -- Extract the witness functional φ from membership in the Y-side subgroup.
  have hv' : v ∈ basisAlignedPeriodSubgroupConcrete Y := hv
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv'
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv'
  -- φ is in the range of periodPairing; extract a cycle σ.
  change φ ∈ (periodPairing ℂ Y).range at hφ_mem
  rw [AddMonoidHom.mem_range] at hφ_mem
  obtain ⟨σ, hσ⟩ := hφ_mem
  -- Rewrite v in terms of φ and σ.
  rw [← hφ_eq, ← hσ]
  -- Define ψ as the pulled-back functional.
  set ψ := (holomorphicOneFormDualEquiv ℂ X).symm
    (traceDualPullbackLiftCLM f hf
      (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ))) with hψ_def
  -- ψ ∈ periodSubgroup ℂ X by the transfer obligation.
  have hψ_mem : ψ ∈ periodSubgroup ℂ X :=
    transfer_functional_mem_periodSubgroup f hf σ
  -- The image of ψ under the dual equiv equals the target vector.
  have hψ_eq : holomorphicOneFormDualEquiv ℂ X ψ =
      traceDualPullbackLiftCLM f hf
        (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ)) := by
    rw [hψ_def]
    exact (holomorphicOneFormDualEquiv ℂ X).apply_symm_apply _
  -- Conclude membership.
  rw [← hψ_eq]
  exact holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete X hψ_mem

/--
The analytic pullback induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.
-/
noncomputable def analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X where
  toFun := mapClm (traceDualPullbackLiftCLM f hf)
    (traceDualPullbackLift_preserves_lattice_raw f hf)
  map_zero' := (mapClm _ _).map_zero
  map_add' := (mapClm _ _).map_add
  continuous_toFun := mapClm_continuous (traceDualPullbackLiftCLM f hf)
    (traceDualPullbackLift_preserves_lattice_raw f hf)

/--
Raw obligation: the descended map is holomorphic.

The equation on `chart.source` uses `chart.left_inv'` plus
`mapClm`'s definition (`map_mk`).
-/
theorem analyticPullback_contMDiff_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) := by
  intro q
  set chartY :=
    chartAt (Fin (analyticGenus ℂ Y) → ℂ) q with chartY_def
  have hsrc : q ∈ chartY.source := mem_chart_source _ q
  have hOpen : IsOpen chartY.source := chartY.open_source
  have hMem : chartY.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞) chartY chartY.source :=
    contMDiffOn_chart
  -- traceDualPullbackLiftCLM is ContMDiff (continuous linear map).
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (traceDualPullbackLiftCLM f hf) :=
    (traceDualPullbackLiftCLM f hf).contMDiff
  -- mk X is ContMDiff.
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ)
          (periodFullComplexLattice X)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLattice X)
  -- Compose to get the auxiliary smooth function on chart.source.
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLattice X)
          (traceDualPullbackLiftCLM f hf (chartY q')))
        chartY.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  -- On chart.source, analyticPullback equals the auxiliary.
  have hEq : ∀ q' ∈ chartY.source,
      analyticPullback f hf q' =
        ComplexTorus.mk _ (periodFullComplexLattice X)
          (traceDualPullbackLiftCLM f hf (chartY q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLattice Y)
        (chartY q') = q' := chartY.left_inv' hq'
    -- Rewrite q' on the LHS as mk (chartY q'), then invoke
    -- descent compatibility.
    conv_lhs => rw [← hLeft]
    -- analyticPullback (mk v) = mk (traceDualPullbackLiftCLM v)
    rfl
  -- ContMDiffOn on chart.source → ContMDiffAt at q.
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPullback f hf) chartY.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact hEq q' hq'
  exact hOn.contMDiffAt hMem

/--
Bundle carrying the analytic pullback together with its
covering-space representative `basisDualPullback` and the descent
compatibility axiom `mk_eq`.

The `analyticPullback` field is the bundled `→ₜ+` hom on the
basis-aligned carrier; the `basisDualPullback` field is the additive
hom on the covering space; `mk_eq` is the defining property linking
the two: `analyticPullback (mk v) = mk (basisDualPullback v)`.

Bottom-up: concretising `basisDualPullback` requires the dual of the
basis-aligned form-pullback; `analyticPullback` is then its descent
through the period quotient (using period-preservation), and `mk_eq`
is automatic from the descent.
-/
structure BasisAnalyticPullbackBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (_f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _f) where
  /--
The pullback as a continuous additive group homomorphism on the
  basis-aligned carrier.
-/
  analyticPullback : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X
  /-- The dual form-pullback on the covering space. -/
  basisDualPullback : (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ)
  /--
Descent compatibility: the bundled pullback acts on the period
  quotient as the descended dual form-pullback.
-/
  mk_eq : ∀ v : Fin (analyticGenus ℂ Y) → ℂ,
    analyticPullback (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback v)
  /-- The bundled pullback is smooth as a manifold map. -/
  contMDiff_pull :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω analyticPullback

/--
The bundled analytic pullback (data + descent axiom). Concretely
realized by descent through the period quotient using the corrected
trace-dual representative `traceDualPullbackLift`.
-/
noncomputable def basisAnalyticPullbackBundle (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticPullbackBundle X Y f hf :=
  { analyticPullback := analyticPullback f hf
    basisDualPullback := (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom
    mk_eq := fun _ => rfl
    contMDiff_pull := analyticPullback_contMDiff_raw f hf }

/-- The analytic pullback is holomorphic. -/
lemma analyticPullback_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) :=
  (basisAnalyticPullbackBundle f hf).contMDiff_pull

/--
**Concrete bundle by descent (corrected representative).** The
concrete `basisAnalyticPullbackBundle f hf` agrees, on its
`basisDualPullback` field, with the underlying `AddMonoidHom` of the
corrected trace-dual matrix `basisAlignedFormPullbackMatrix f hf`.
-/
theorem basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  rfl

theorem basisAnalyticPullbackBundle_eq_pullbackFormsMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      pullbackFormsMap X Y f hf := by
  rw [basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom f hf,
      pullbackFormsMap_eq_matrix_AddHom f hf]

/--
Bundle-level axiom: the `basisDualPullback` field of the bundle
selected at `(X, X, id, contMDiff_id)` is the identity additive group
homomorphism on the covering space.
-/
theorem basisAnalyticPullbackBundle_id_dualPullback :
    (basisAnalyticPullbackBundle (X := X) (Y := X) id contMDiff_id).basisDualPullback =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (X := X) (Y := X)
      id contMDiff_id,
    pullbackFormsMap_id_eq_id (X := X)]

/--
Descent compatibility: `analyticPullback` acts on the period
quotient as the descended `basisDualPullback`.
-/
theorem analyticPullback_mk_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullback f hf (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback f hf v) :=
  (basisAnalyticPullbackBundle f hf).mk_eq v

/--
Contravariant functoriality of the dual form-pullback on the
covering space: `basisDualPullback (g ∘ f) = basisDualPullback f ∘ basisDualPullback g`.

Bottom-up content: the dual of form-pullback reverses composition.
This is the lifting of `pullbackFormsFun_comp_apply` to the
basis-aligned linear maps, then dualization.

**Goal.** Show that the covering-space dual pullback for `g ∘ f`
equals the composition of dual pullbacks for `f` and `g`
(contravariantly), at each covering-space vector.

The proof now routes through the concrete basis-level map
`pullbackFormsMap`; it does not use quotient smoothness or the
trace-pullback degree field from `BasisAnalyticPullbackBundle`.
-/
theorem basisAnalyticPullbackBundle_comp_dualPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)).basisDualPullback =
      ((basisAnalyticPullbackBundle f hf).basisDualPullback).comp
        (basisAnalyticPullbackBundle g hg).basisDualPullback := by
  -- Route through the concrete basis-level pullback map.
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (g ∘ f) (hg.comp hf),
      basisAnalyticPullbackBundle_eq_pullbackFormsMap f hf,
      basisAnalyticPullbackBundle_eq_pullbackFormsMap g hg,
      pullbackFormsMap_comp_eq f hf g hg]

/--
Companion spec for `analyticPullback_comp_apply`: pullback of forms is
contravariantly functorial, and descent preserves composition.

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
and `basisDualPullback_comp`. Every element of the quotient is
`⟦v⟧` for some covering-space vector `v`; rewrite both sides using
descent compatibility, then apply the covering-space composition law.
-/
theorem analyticPullback_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq (g ∘ f) (hg.comp hf) v]
    rw [analyticPullback_mk_eq g hg v]
    rw [analyticPullback_mk_eq f hf (basisDualPullback g hg v)]
    rw [basisDualPullback_comp f hf g hg v]

/--
Pullback distributes contravariantly over composition.

Pure assembly of `analyticPullback_comp_spec`.
-/
lemma analyticPullback_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) :=
  analyticPullback_comp_spec f hf g hg P

/--
Companion spec: pullback along the identity map equals the identity
homomorphism (as a `ContinuousAddMonoidHom`).

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
(descent compatibility) and `basisDualPullback_id` (covering-space
identity functoriality). On each `mk v`, rewrite via descent and
identify the dual pullback as the identity.
-/
theorem analyticPullback_id_spec :
    analyticPullback (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq id contMDiff_id v, basisDualPullback_id]
    rfl

/--
Pullback along the identity is the identity.

Assembly from `analyticPullback_id_spec`.
-/
lemma analyticPullback_id_apply (P : BasisAnalyticJacobian X) :
    analyticPullback (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPullback_id_spec]
  rfl

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPullbackBundle X Y f hf) :=
  ⟨{ analyticPullback := 0
     basisDualPullback := 0
     mk_eq := fun _ => rfl
     contMDiff_pull := contMDiff_const }⟩
