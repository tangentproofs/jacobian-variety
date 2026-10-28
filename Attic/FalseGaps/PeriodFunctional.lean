/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/PeriodFunctional.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
**Sub-obligation 1b.1 (Stage-A surface classification + CW).**
A compact connected oriented Riemann surface `X` admits a `ℤ`-basis
of `H₁(X, ℤ)` indexed by `Fin (2 * topologicalGenus X)`.
-/
theorem stageA_surface_CW_basis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) := by
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  haveI : Orientable X := complexManifold_orientable X
  exact singularH1_basis_of_compactOrientableSurface X

/--
**Sub-obligation 1b.** `H₁(X, ℤ)` of a compact connected
Riemann surface of topological genus `g_top` is free of rank
`2 g_top`. Mathlib blockers: surface classification, CW-structure,
cellular homology — all absent in v4.28.0.
-/
theorem h1_free_of_compact_surface
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus X)) ℤ
      (IntegralOneCycle X)) :=
  stageA_surface_CW_basis X

/--
**Sub-obligation 2 (Stage-B Hodge bridge).** The analytic and
topological genera coincide on a compact connected Riemann surface.
-/
theorem stageB_analytic_eq_topological
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = topologicalGenus X := by
  have h := JacobianChallenge.HolomorphicForms.two_analyticGenus_eq_finrank_intH1 X
  -- h : 2 * analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X)
  -- topologicalGenus X = Module.finrank ℤ (singularH1 X) / 2
  --                    = Module.finrank ℤ (IntegralOneCycle X) / 2  (abbrev)
  unfold topologicalGenus
  show analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X) / 2
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]

/--
**Sub-obligation 2.** The analytic genus equals the topological
genus for a compact connected Riemann surface. Classical proof via
de Rham (`H¹_dR ≅ H¹_sing ⊗ ℂ`) + Hodge decomposition
(`H¹_dR ≅ H⁰(Ω¹) ⊕ H¹(𝒪)`) + Serre duality.

Mathlib blockers (all absent in v4.28.0): de Rham theorem on
manifolds, Hodge decomposition, Dolbeault cohomology, Serre
duality.
-/
theorem analyticGenus_eq_topologicalGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = topologicalGenus X :=
  stageB_analytic_eq_topological X

/--
**TOPDOWN helper.** H₁(X, ℤ) of a compact connected Riemann surface
of analytic genus `g` admits a ℤ-basis indexed by `Fin (2g)`.

TOPDOWN assembly (Aristotle 921772f5): combines
`h1_free_of_compact_surface` and `analyticGenus_eq_topologicalGenus`
via `Fin.castOrderIso` reindex.
-/
theorem h1_basis_of_compact_riemann_surface
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ
      (IntegralOneCycle X)) := by
  obtain ⟨b⟩ := h1_free_of_compact_surface X
  exact ⟨b.reindex (Fin.castOrderIso (by rw [analyticGenus_eq_topologicalGenus])).toEquiv⟩

/--
**Sub-obligation 1.** A compact connected Riemann surface of genus
`g` has `2g` integral 1-cycles forming a symplectic basis (encodes
`H₁(X, ℤ) ≅ ℤ^{2g}`).

TOPDOWN assembly (Aristotle e227f244): extracts a ℤ-basis from
`h1_basis_of_compact_riemann_surface` and derives injectivity via
`LinearIndependent.injective`.
-/
theorem symplectic_basis_of_cycles
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X),
      Function.Injective σ := by
  obtain ⟨b⟩ := h1_basis_of_compact_riemann_surface X
  exact ⟨b, b.linearIndependent.injective⟩

/--
**Classical basis provider for the selected symplectic basis.** The cycles
chosen by `symplectic_basis_of_cycles` are the canonical/symplectic period basis
for which the Riemann-bilinear identity plus Hodge positivity produce
basis-aligned period-coordinate nondegeneracy.

This is the genuinely narrower remaining frontier: it is tied to the specific
symplectic basis selected by the surface-classification/H₁ construction, rather
than asserting nondegeneracy for every arbitrary injective family of cycles.
-/
theorem symplectic_basis_of_cycles_riemannClassicalPeriodBasis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X),
      Function.Injective σ ∧ RiemannClassicalPeriodBasis X σ := by
  obtain ⟨B⟩ := h1_basis_of_compact_riemann_surface X
  exact ⟨fun i => B i, B.linearIndependent.injective,
    h1_basis_riemannClassicalPeriodBasis X B⟩

theorem periodVectors_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      ∀ i, b i ∈ (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  obtain ⟨σ, hσ, hσ_classical⟩ :=
    symplectic_basis_of_cycles_riemannClassicalPeriodBasis X
  exact ⟨fun i => (holomorphicOneFormDualEquiv ℂ X) ((periodPairing ℂ X) (σ i)),
         period_vectors_linearIndependent_of_symplectic X σ hσ hσ_classical,
         period_vectors_mem_subgroup X σ⟩

/--
**Sub-obligation 1 (integrality).** The basis-aligned period
subgroup equals the ℤ-span of the `2g` period vectors obtained from
a symplectic basis of cycles.

Bottom-up content: `periodPairing` is an `AddMonoidHom` and
`IntegralOneCycle X` is the free ℤ-module on a basis (the deeper
content of `h1_basis_of_compact_riemann_surface`). The image of a
ℤ-span under a ℤ-linear map is the ℤ-span of the images. Transport
via the ℤ-linear `holomorphicOneFormDualEquiv` preserves this
structure.

1. Get a ℤ-basis `B` of `IntegralOneCycle X` from
   `h1_basis_of_compact_riemann_surface X`.
2. Set `b i := dualEquiv (periodPairing (B i))`.
3. ℝ-linear independence of `b` follows from
   `period_vectors_linearIndependent_of_symplectic` applied to the
   underlying function of `B` (which is injective since `B` is a basis).
4. Range equality:
   * `(periodPairing).range = ⊤.map periodPairing` (definition of range).
   * `⊤ = (Submodule.span ℤ (Set.range B)).toAddSubgroup` because `B`
     is a basis (`Module.Basis.span_eq` + `Submodule.top_toAddSubgroup`).
   * Compose with the dual equivalence via `AddSubgroup.map_map`.
   * The image of a ℤ-span under a ℤ-linear map is the ℤ-span of the
     image (`Submodule.map_span` + `Submodule.map_toAddSubgroup`).
   * Identify `(g ∘ B) '' univ = Set.range b` via `Set.range_comp`.
-/
theorem periodSubgroup_eq_zspan_of_basis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) =
      (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  obtain ⟨B⟩ := h1_basis_of_compact_riemann_surface X
  -- Build the composed `AddMonoidHom`: dualEquiv ∘ periodPairing.
  set φ : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ) :=
    (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom with hφ
  set π : IntegralOneCycle X →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
    periodPairing ℂ X with hπ
  set g : IntegralOneCycle X →+ (Fin (analyticGenus ℂ X) → ℂ) :=
    φ.comp π with hg
  refine ⟨fun i => g (B i), ?_, ?_⟩
  · -- ℝ-linear independence: delegate to
    -- `period_vectors_linearIndependent_of_symplectic` using the
    -- fact that a `Module.Basis` is injective.
    exact period_vectors_linearIndependent_of_symplectic X
      (fun i => B i) B.linearIndependent.injective
      (h1_basis_riemannClassicalPeriodBasis X B)
  · -- Range equality. We route entirely through `AddSubgroup.closure`
    -- (which is module-instance-independent), and only convert back to
    -- `Submodule.span ℤ` on the target side `Fin _ → ℂ` (which has no
    -- module-instance diamond).
    --
    -- Step 1: `AddSubgroup.closure (range B) = ⊤` — the spanning property
    -- of `B` at the `AddSubgroup` level. Provable from `Module.Basis.sum_repr`
    -- + the uniqueness of the `ℤ`-action on an `AddCommGroup`, but the
    -- exact bridge is delegated to a named obligation
    -- (`addSubgroup_closure_basis_eq_top`) to keep this assembly clean.
    have hclosure_B : AddSubgroup.closure (Set.range (fun i => B i))
        = (⊤ : AddSubgroup (IntegralOneCycle X)) :=
      addSubgroup_closure_basis_eq_top B
    -- Step 2: `π.range = π.map ⊤ = π.map (closure (range B)) =
    --          closure (π '' range B) = closure (range (π ∘ B))`.
    have hπrange : π.range
        = AddSubgroup.closure (Set.range (fun i => π (B i))) := by
      rw [AddMonoidHom.range_eq_map, ← hclosure_B, AddMonoidHom.map_closure]
      congr 1
      exact (Set.range_comp π (fun i => B i)).symm
    -- Step 3: `dualEquiv.map (closure s) = closure (dualEquiv '' s)`.
    rw [hπrange, AddMonoidHom.map_closure]
    -- Step 4: identify the image with the range of `g ∘ B`.
    rw [show (φ : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → _) ''
            Set.range (fun i => π (B i))
          = Set.range (fun i => g (B i)) by
      rw [← Set.range_comp]; rfl]
    -- Step 5: convert closure back to `Submodule.span ℤ ... .toAddSubgroup`
    -- on the target side (no diamond there).
    rw [← Submodule.span_int_eq_addSubgroupClosure]

/--
The basis-aligned period subgroup is discrete.

Bottom-up content: integrality of the period pairing image. Equivalently,
the image is a free `ℤ`-module of rank `2g`, spanned by `2g` real-linearly
independent period vectors after transport to the basis-aligned model.

This is the named bottom-up obligation that
`Jacobian.Periods.basisAlignedPeriodSubgroup_isDiscrete` delegates to.

#### TOPDOWN assembly (executed via Aristotle 303edecd)
-/
theorem periodSubgroup_isZLattice
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) := by
  obtain ⟨b, hli, heq⟩ := periodSubgroup_eq_zspan_of_basis X
  rw [heq]
  exact zspan_of_RLinearIndep_isDiscrete (analyticGenus ℂ X) b hli

/--
The basis-aligned period subgroup spans the full ℝ-vector space
`Fin (analyticGenus ℂ X) → ℂ`, viewed as ℝ²ᵍ. Together with
`periodSubgroup_isZLattice`, this is the second half of the
`IsZLattice ℝ` content for the period subgroup.

Bottom-up content: Riemann bilinear nondegeneracy — the period
subgroup contains 2g real-linearly independent vectors. The full
ℤ-rank statement follows from the integrality of the period
pairing on `H₁(X, ℤ)` plus the classical fact that the period
matrix has nonzero imaginary determinant.

This is the named bottom-up obligation that the eventual
construction of an `IsZLattice ℝ` instance for the basis-aligned
period subgroup will delegate to. It is not yet wired into
`PeriodLattice.lean`'s assembly because the surrounding
`IsZLattice` infrastructure (Submodule promotion of the
AddSubgroup, basis extraction) is still being designed.
-/
theorem periodSubgroup_spans_real
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Submodule.span ℝ
      ((AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
        Set (Fin (analyticGenus ℂ X) → ℂ))
      = ⊤ := by
  obtain ⟨b, hli, hmem⟩ := periodVectors_linearIndependent X
  exact span_real_eq_top_of_subset_linearIndependent
    (analyticGenus ℂ X)
    ((AddSubgroup.map
      (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
      ((periodPairing ℂ X).range) :
      AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)) :
      Set (Fin (analyticGenus ℂ X) → ℂ))
    b hli (Set.range_subset_iff.mpr hmem)

/--
`DiscreteTopology` for the `Submodule ℤ`-promoted period subgroup.

Pure type-level transport from `periodSubgroup_isZLattice` (which gives
`DiscreteTopology` on the underlying `AddSubgroup`). The carriers are
the same `Set`, so a `Subtype.mk`-along-the-identity map is continuous
and injective, and `DiscreteTopology.of_continuous_injective` does the
rest. No new bottom-up content.
-/
noncomputable instance basisAlignedPeriodSubmoduleℤ_discreteTopology
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    DiscreteTopology (basisAlignedPeriodSubmoduleℤ X) := by
  haveI hdisc : DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) :=
    periodSubgroup_isZLattice ℂ X
  exact DiscreteTopology.of_continuous_injective
    (β := AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range))
    (f := fun (x : basisAlignedPeriodSubmoduleℤ X) => ⟨x.1, x.2⟩)
    (continuous_induced_rng.mpr continuous_subtype_val)
    (fun _ _ h => Subtype.ext (congr_arg Subtype.val h))

/--
`IsZLattice ℝ` for the `Submodule ℤ`-promoted period subgroup.

Pure assembly: the `span_top` field reduces to
`periodSubgroup_spans_real` after applying `AddSubgroup.coe_toIntSubmodule`
to identify the carriers as `Set`s. The `[DiscreteTopology …]` class
parameter is supplied by `basisAlignedPeriodSubmoduleℤ_discreteTopology`
above. No new bottom-up content.
-/
noncomputable instance basisAlignedPeriodSubmoduleℤ_isZLattice
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    IsZLattice ℝ (basisAlignedPeriodSubmoduleℤ X) where
  span_top := by
    -- `(basisAlignedPeriodSubmoduleℤ X : Set _)` reduces by `rfl` to the
    -- underlying `AddSubgroup.map …` carrier (via
    -- `AddSubgroup.coe_toIntSubmodule`), so the goal is exactly
    -- `periodSubgroup_spans_real X`.
    rw [basisAlignedPeriodSubmoduleℤ, AddSubgroup.coe_toIntSubmodule]
    exact periodSubgroup_spans_real X

/--
Existence of a compact fundamental domain for the basis-aligned
period subgroup.

Bottom-up content: under the `IsZLattice ℝ` witness assembled from
`periodSubgroup_isZLattice` and `periodSubgroup_spans_real`, the set
`closure (ZSpan.fundamentalDomain b)` (for `b` the lifted ℤ-basis) is
compact — by `ZSpan.fundamentalDomain_isBounded` plus
`Bornology.IsBounded.isCompact_closure` in the `ProperSpace`
`Fin (analyticGenus ℂ X) → ℂ` — and its period-subgroup translates
cover the model space via `ZSpan.fract_mem_fundamentalDomain` and
`Module.Basis.ofZLatticeBasis_span`.

This existence statement is the named bottom-up obligation that the
`periodFundamentalDomain` definition (and the
`periodFundamentalDomain_isCompact` / `_covers` lemmas) in
`Jacobian/Periods/PeriodLattice.lean` delegate to. Stating it as
`∃ D, IsCompact D ∧ (covering)` keeps `PeriodLattice.lean` free to
*choose* a concrete `D` via `Classical.choose`, while the
mathematical work — discreteness + full ℝ-rank ⇒ compact
fundamental domain — is centralised here next to its inputs.
-/
theorem exists_compact_periodFundamentalDomain
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ D : Set (Fin (analyticGenus ℂ X) → ℂ),
      IsCompact D ∧
      ∀ v : Fin (analyticGenus ℂ X) → ℂ,
        ∃ g ∈ (AddSubgroup.map
          (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
          ((periodPairing ℂ X).range) :
          AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)),
          v - g ∈ D := by
  haveI : DiscreteTopology (basisAlignedPeriodSubmoduleℤ X) :=
    basisAlignedPeriodSubmoduleℤ_discreteTopology X
  haveI : IsZLattice ℝ (basisAlignedPeriodSubmoduleℤ X) :=
    basisAlignedPeriodSubmoduleℤ_isZLattice X
  haveI := ZLattice.module_free ℝ (basisAlignedPeriodSubmoduleℤ X)
  haveI := ZLattice.module_finite ℝ (basisAlignedPeriodSubmoduleℤ X)
  let bℤ : Module.Basis _ ℤ (basisAlignedPeriodSubmoduleℤ X) :=
    Module.Free.chooseBasis ℤ _
  let bR : Module.Basis _ ℝ (Fin (analyticGenus ℂ X) → ℂ) :=
    bℤ.ofZLatticeBasis ℝ _
  refine ⟨closure (ZSpan.fundamentalDomain bR), ?_, ?_⟩
  · exact (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  · intro v
    refine ⟨(ZSpan.floor bR v : Fin _ → ℂ), ?_, ?_⟩
    · -- The floor lands in `span ℤ (range bR) = basisAlignedPeriodSubmoduleℤ X`,
      -- and `(basisAlignedPeriodSubmoduleℤ X).toAddSubgroup = AddSubgroup.map ...`
      -- by `AddSubgroup.toIntSubmodule_toAddSubgroup`.
      have hmem_span : (ZSpan.floor bR v : Fin _ → ℂ) ∈
          (Submodule.span ℤ (Set.range bR) : Submodule ℤ _) :=
        (ZSpan.floor bR v).property
      have hSub : (basisAlignedPeriodSubmoduleℤ X)
            = Submodule.span ℤ (Set.range bR) :=
        (Module.Basis.ofZLatticeBasis_span (K := ℝ) (b := bℤ)).symm
      have hSubgroup :
          (basisAlignedPeriodSubmoduleℤ X).toAddSubgroup =
          (Submodule.span ℤ (Set.range bR)).toAddSubgroup :=
        congrArg Submodule.toAddSubgroup hSub
      rw [show (AddSubgroup.map
            (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
            ((periodPairing ℂ X).range)) =
          (basisAlignedPeriodSubmoduleℤ X).toAddSubgroup
        from (AddSubgroup.toIntSubmodule_toAddSubgroup _).symm, hSubgroup]
      exact hmem_span
    · have hfract : v - (ZSpan.floor bR v : Fin _ → ℂ) = ZSpan.fract bR v := by
        rw [ZSpan.fract_apply]
      rw [hfract]
      exact subset_closure (ZSpan.fract_mem_fundamentalDomain bR v)

/--
**Classical period-coordinate nondegeneracy provider for an H₁ basis.** A
concrete `Module.Basis` supplied by the surface-classification/H₁ construction
has basis-aligned period-coordinate rows that are ℝ-linearly independent.

This is narrower than #227: it does not assert linear independence for an
arbitrary injective cycle family, only for an H₁ basis carrying the missing
classical symplectic/Stokes/Hodge structure.
-/
theorem h1_basis_periodCoordinate_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (B : Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ
      (IntegralOneCycle X)) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairing ℂ X) (B i))) := by
  sorry

/--
**Classical period-basis provider for an H₁ basis.** This is now only a
structure assembly from the precise coordinate nondegeneracy provider above.
-/
theorem h1_basis_riemannClassicalPeriodBasis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (B : Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ
      (IntegralOneCycle X)) :
    RiemannClassicalPeriodBasis X (fun i => B i) := by
  exact ⟨h1_basis_periodCoordinate_linearIndependent X B⟩
