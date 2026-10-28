/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/DualGraphCut.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

theorem cut_along_nonTree_yields_unfoldedDisk
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    {T : Triangulation M} {G : DualGraph M T}
    (_ST : DualSpanningTree M G) :
    Nonempty (UnfoldedDisk M T) :=
  -- The construction follows the classical cut-and-paste topology of surfaces.
  sorry

theorem Triangulation.toEdgeWordPresentation_via_cut
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (T : Triangulation M) :
    Nonempty (EdgeWordPresentation M) := by
  obtain ⟨G⟩ := T.toDualGraph
  obtain ⟨ST⟩ := G.spanningTree
  obtain ⟨D⟩ := cut_along_nonTree_yields_unfoldedDisk ST
  exact unfoldedDisk_to_edgeWordPresentation D
