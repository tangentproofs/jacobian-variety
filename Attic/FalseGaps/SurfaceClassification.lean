/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/SurfaceClassification.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
**Stage A2.a leaf (cut along non-tree edges).** Given a finite
triangulation of a compact connected 2-manifold, the dual graph
contains a maximal spanning tree; cutting `M` along the *non-tree*
edges unfolds the surface into a single 2-cell with side identifications
encoded as an edge-pairing word. The resulting word is *not yet
standardized* — that is the job of A2.b.

Bottom-up content: dual-tree unfolding (Massey, *Algebraic Topology*,
§I.4 / Lee, *Topological Manifolds*, §6.3).
-/
noncomputable def Triangulation.toEdgeWordPresentation
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (T : Triangulation M) : EdgeWordPresentation M :=
  Classical.choice (T.toEdgeWordPresentation_via_cut)

/--
**Stage A2.b leaf (Tietze reduction to standard form).** Any
edge-word presentation of an orientable 2-manifold reduces to the
standard `a₁b₁a₁⁻¹b₁⁻¹⋯` form via finitely many Tietze moves. The
resulting standard presentation is exactly a `PolygonalQuotientPresentation`.

Bottom-up content: classical Brahana / Seifert–Threlfall reduction.
-/
noncomputable def EdgeWordPresentation.toPolygonalQuotient
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) : PolygonalQuotientPresentation M :=
  E.toPolygonalQuotient_via_tietze

/--
**Stage A2 leaf (combinatorial reduction).** Given a triangulation
of a compact connected orientable smooth real 2-manifold, one obtains a
polygonal-quotient presentation. Body assembles
`Triangulation.toEdgeWordPresentation` (A2.a) followed by
`EdgeWordPresentation.toPolygonalQuotient` (A2.b).
-/
noncomputable def Triangulation.toPolygonalQuotient
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (T : Triangulation M) : PolygonalQuotientPresentation M :=
  T.toEdgeWordPresentation.toPolygonalQuotient

/--
**Stage A1+A2 leaf (existence of a polygonal-quotient presentation).**
Every compact connected orientable smooth real 2-manifold admits a
*polygonal-quotient presentation* in standard `4g'`-gon form.

Body: `exists_triangulation_of_compact_2manifold` + `Triangulation.toPolygonalQuotient`.
-/
theorem existsPolygonalQuotientPresentation
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (PolygonalQuotientPresentation M) := by
  obtain ⟨T⟩ := exists_triangulation_of_compact_2manifold M
  exact ⟨T.toPolygonalQuotient⟩

/--
**Stage A1 umbrella (existence form).** Every compact connected
orientable smooth real 2-manifold is homeomorphic to `Polygon4g g'`
for *some* `g' : ℕ`. Identification of that `g'` with the topological
genus is the Stage A umbrella body, *not* this leaf.

Body: assembled from `existsPolygonalQuotientPresentation` and
`polygonalQuotientPresentation_to_homeo`.
-/
theorem existsHomeoToPolygon4g
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    ∃ g' : ℕ, Nonempty (M ≃ₜ Polygon4g g') := by
  obtain ⟨P⟩ := existsPolygonalQuotientPresentation M
  obtain ⟨homeo⟩ := polygonalQuotientPresentation_to_homeo P
  exact ⟨P.genus, ⟨homeo.symm⟩⟩

/--
**Stage A umbrella (surface classification).** A compact connected
orientable smooth real 2-manifold `M` is homeomorphic to the standard
fundamental polygon `Polygon4g (topologicalGenus M)`.
-/
theorem compactOrientableSurface_homeomorph_polygon4g_topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (M ≃ₜ Polygon4g (topologicalGenus M)) := by
  obtain ⟨g', ⟨homeo⟩⟩ := existsHomeoToPolygon4g M
  have hgM : topologicalGenus M = g' := by
    have hinv : topologicalGenus M = topologicalGenus (Polygon4g g') :=
      topologicalGenus_homeo_invariant homeo
    rw [hinv, topologicalGenus_polygon4g]
  exact ⟨hgM ▸ homeo⟩

/--
**Direct corollary (M's singular H₁ is free of rank `2 * topGenus M`).**
For a compact connected orientable smooth real 2-manifold `M` whose
polygonal model is `Polygon4g (topologicalGenus M)`, singular `H₁(M, ℤ)`
is ℤ-linearly isomorphic to the free module `Fin (2 * topologicalGenus M) → ℤ`.
-/
theorem singularH1_iso_freeZ_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (singularH1 M ≃ₗ[ℤ] (Fin (2 * topologicalGenus M) → ℤ)) := by
  obtain ⟨homeo⟩ :=
    compactOrientableSurface_homeomorph_polygon4g_topologicalGenus M
  obtain ⟨polyIso⟩ := polygon4g_singularH1_iso_freeZ (topologicalGenus M)
  exact ⟨(singularH1LinearEquivOfHomeo homeo).trans polyIso⟩

/--
**Finrank corollary.** For a compact connected orientable smooth
real 2-manifold `M`, the ℤ-rank of singular `H₁(M, ℤ)` equals
`2 * topologicalGenus M`.

Body: extract the iso from `singularH1_iso_freeZ_of_compactOrientableSurface`
and finish via `LinearEquiv.finrank_eq` + `Module.finrank_pi` +
`Fintype.card_fin`.
-/
theorem singularH1_finrank_eq_two_mul_topologicalGenus_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Module.finrank ℤ (singularH1 M) = 2 * topologicalGenus M := by
  obtain ⟨e⟩ := singularH1_iso_freeZ_of_compactOrientableSurface M
  rw [e.finrank_eq]
  exact Module.finrank_fin_fun (R := ℤ) (n := 2 * topologicalGenus M)

/--
**Singular `H₁` of a compact orientable smooth real 2-manifold
admits a ℤ-basis indexed by `Fin (2 * topologicalGenus M)`.** Public
companion to `singularH1_iso_freeZ_of_compactOrientableSurface`,
matching the basis-shaped form used by `h1_basis_of_compact_riemann_surface`
on the Riemann-surface side.
-/
theorem singularH1_basis_of_compactOrientableSurface
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (Module.Basis (Fin (2 * topologicalGenus M)) ℤ (singularH1 M)) := by
  obtain ⟨e⟩ := singularH1_iso_freeZ_of_compactOrientableSurface M
  exact ⟨Module.Basis.ofEquivFun e⟩
