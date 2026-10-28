import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.TopologicalGenusInvariance
import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.RadoTriangulation
import Jacobian.Periods.DualGraphCut
import Jacobian.Periods.TietzeReduction
import Jacobian.Periods.Polygon4gCellular
import Jacobian.Periods.SingularH1Homotopy
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage A umbrella: surface classification

This file states the **Stage A** obligation of `ref/plans/polygonal-model.md`:
every compact connected orientable smooth real 2-manifold `M` is
homeomorphic to the standard fundamental polygon `Polygon4g`
of its topological genus.

## Top-down role

`compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
is the named obligation that the umbrella `polygonal_model`
delegates to. It is a 3-leaf assembly:

* `existsHomeoToPolygon4g` — *some* `g' : ℕ` admits `M ≃ₜ Polygon4g g'`.
  This is the heart of the surface-classification theorem: Radó +
  combinatorial reduction + identification with `Polygon4g`.
* `topologicalGenus_polygon4g` — for `g : ℕ`, the polygon `Polygon4g g`
  has topological genus `g`. (Computational; reduces to `H₁` of the
  CW-quotient.)
* `topologicalGenus_homeo_invariant` — `topologicalGenus` is a
  homeomorphism invariant. (Pure Mathlib singular-homology functoriality.)

The umbrella body assembles these: `existsHomeoToPolygon4g` produces
some `g'` and a homeomorphism, then invariance + the polygon
computation pin down `g' = topologicalGenus M`, after which the
homeomorphism is rewritten into the canonical form.

## Bottom-up content

A canonical Lean discharge of `existsHomeoToPolygon4g` would proceed via:

* `compact_2manifold_admits_triangulation` (Radó),
* `triangulated_orientable_surface_word` (combinatorial reduction to the
  standard `a₁b₁a₁⁻¹b₁⁻¹⋯` edge word),
* `polygon_word_to_polygon4g` (identification with `Polygon4g g`).

Each leaf is itself a multi-hundred-LOC project; see
`ref/plans/polygonal-model.md` Stage A and the future
`ref/plans/surface-classification.md` for the next-level decomposition.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/--
**Stage A1 leaf (Radó).** Every compact 2-manifold admits a finite
triangulation.

* `compact_2manifold_finite_chart_atlas` — finite chart atlas
  extraction.
* `finite_chart_atlas_admits_pl_refinement` — dimension-2 PL
  refinement (the Doyle–Moran/Thomassen step).
* `pl_atlas_to_triangulation` — assemble the simplicial complex from
  a compatible PL atlas.

Bottom-up content: classical Radó theorem on triangulability of
compact surfaces. Mathlib v4.28.0 has neither Radó nor the abstract
simplicial complex theory required to state it directly.
-/
theorem exists_triangulation_of_compact_2manifold
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M] :
    Nonempty (Triangulation M) :=
  exists_triangulation_of_compact_2manifold_via_pl M





namespace PolygonalQuotientPresentation

/--
The lift of `P.proj : DiskC → M` through the side-pairing
quotient, producing a continuous bijection `Polygon4g P.genus → M`.
-/
noncomputable def qLift {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Polygon4g P.genus → M :=
  Quotient.lift P.proj (fun z w hzw => (P.kernel z w).mpr hzw)

lemma qLift_continuous {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Continuous P.qLift :=
  P.cts.quotient_lift _

lemma qLift_bijective {M : Type} [TopologicalSpace M]
    (P : PolygonalQuotientPresentation M) : Function.Bijective P.qLift := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ z =>
      induction b using Quotient.inductionOn with
      | _ w =>
        change P.proj z = P.proj w at hab
        exact Quotient.sound ((P.kernel z w).mp hab)
  · intro y
    obtain ⟨z, hz⟩ := P.surj y
    exact ⟨⟦z⟧, hz⟩

/--
The polygon-to-surface homeomorphism produced by a polygonal
quotient presentation. Compact source + T2 target + continuous
bijection → homeomorphism via `Continuous.homeoOfEquivCompactToT2`.
-/
noncomputable def toHomeo {M : Type} [TopologicalSpace M]
    [CompactSpace M] [T2Space M]
    (P : PolygonalQuotientPresentation M) : Polygon4g P.genus ≃ₜ M :=
  P.qLift_continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective P.qLift P.qLift_bijective)

end PolygonalQuotientPresentation

/--
**Stage A3+A4 leaf (universal-property assembly).** A polygonal-quotient
presentation `P` of a compact T2 space `M` produces a homeomorphism
`Polygon4g P.genus ≃ₜ M`, packaged as `Nonempty` for backwards
compatibility (the underlying construction is the noncomputable
`P.toHomeo` defined above).
-/
theorem polygonalQuotientPresentation_to_homeo
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (P : PolygonalQuotientPresentation M) :
    Nonempty (Polygon4g P.genus ≃ₜ M) :=
  ⟨P.toHomeo⟩



/--
**Unified Stage A2 structural iso (any genus).** The first singular
homology of the standard fundamental polygon is ℤ-linearly isomorphic
to the free ℤ-module `Fin (2g) → ℤ` for any `g : ℕ`.

Body: extract the unified basis from `polygon4g_singularH1_basis` and
turn it into a linear equivalence via `Basis.equivFun`. (Same
meet-in-the-middle pattern as the Stage B leaf; covers both `g = 0`
and `g ≥ 1` cases via the unified basis.)
-/
theorem polygon4g_singularH1_iso_freeZ (g : ℕ) :
    Nonempty (singularH1 (Polygon4g g) ≃ₗ[ℤ] (Fin (2 * g) → ℤ)) := by
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  exact ⟨b.equivFun⟩

/--
**Stage A2 sub-leaf (rank of singular `H₁` of the polygon).**
The first singular homology of the standard fundamental polygon has
ℤ-rank `2g`.

Body: extract the unified basis from `polygon4g_singularH1_basis`,
then `Module.finrank_eq_card_basis` + `Fintype.card_fin`. The case
split on `g` is folded into the basis construction, not exposed here.
-/
theorem singularH1_polygon4g_finrank (g : ℕ) :
    Module.finrank ℤ (singularH1 (Polygon4g g)) = 2 * g := by
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/--
**Stage A2 leaf (polygon genus).** The topological genus of the
standard fundamental polygon `Polygon4g g` equals `g`.

Body: unfold `topologicalGenus`, rewrite through
`singularH1_polygon4g_finrank`, divide by 2.
-/
theorem topologicalGenus_polygon4g (g : ℕ) :
    topologicalGenus (Polygon4g g) = g := by
  unfold topologicalGenus
  rw [singularH1_polygon4g_finrank g,
      Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]

/--
**Stage A3 leaf (homeomorphism invariance of `topologicalGenus`).**
A topological homeomorphism between compact connected spaces preserves
the topological genus.

Body: by `singularH1_finrank_homeo_invariant`, both sides reduce to the
same `Module.finrank ℤ (singularH1 _)`, then divide by 2.
-/
theorem topologicalGenus_homeo_invariant
    {M N : Type} [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [TopologicalSpace N] [CompactSpace N] [ConnectedSpace N]
    (h : M ≃ₜ N) : topologicalGenus M = topologicalGenus N := by
  unfold topologicalGenus
  rw [singularH1_finrank_homeo_invariant h]





end JacobianChallenge.Periods
