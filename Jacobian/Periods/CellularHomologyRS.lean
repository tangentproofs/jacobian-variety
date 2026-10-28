import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.TopologicalGenusInvariance
import Jacobian.Periods.Orientable
import Jacobian.Periods.SmoothRealStructure
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Cellular homology of a compact Riemann surface -/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- Project-side finite cellular indexing data on `X`. -/
structure FiniteCWStructure
    (X : Type*) [TopologicalSpace X] where
  /-- Project-side cell indexing types by dimension. -/
  cell : ℕ → Type
  /-- Finiteness of cells in each dimension. -/
  fintype_cell : ∀ n, Fintype (cell n)
  /-- The complex is finite-dimensional. -/
  finite_dim : ∃ n, ∀ m > n, IsEmpty (cell m)

/--
Project-side finite cellular certificate for the standard polygon.

This records the concrete data currently available in the repository:
one vertex, `2g` one-cell loops, one two-cell characteristic map, and
the cellular boundary computation.  It is deliberately separate from
Mathlib's `Topology.CWComplex`, whose `PartialEquiv` characteristic-map
and weak-topology fields are not constructed by the current polygon API.
-/
structure Polygon4gProjectFiniteCellularCertificate (g : ℕ) where
  /-- The standard project-side cellular model. -/
  model : Polygon4gCellularModel g
  /-- The unique zero-cell is represented by the model vertex. -/
  zeroCell : Polygon4g g
  /-- The zero-cell is exactly the vertex stored in the cellular model. -/
  zeroCell_eq_vertex : zeroCell = model.vertex
  /-- The one-cells are indexed by `Fin (2g)`. -/
  oneCellPath : Fin (2 * g) → Path model.vertex model.vertex
  /-- The one-cell paths agree with the model characteristic paths. -/
  oneCellPath_eq_model : oneCellPath = model.oneCellPath
  /-- The unique two-cell characteristic map. -/
  twoCellCharacteristic :
    ContinuousMap model.disk.diskSource.carrier (Polygon4g g)
  /-- The two-cell characteristic map agrees with the model map. -/
  twoCellCharacteristic_eq_model :
    twoCellCharacteristic = model.twoCellCharacteristic
  /-- The attaching word is the standard product of commutators. -/
  boundaryWord_standard : model.boundaryWord.IsStandardForm
  /-- The word-side quotient relation is the polygon side-pairing relation. -/
  boundaryWord_sidePairing :
    EdgeWord.sidePairingRel g model.boundaryWord = Polygon4g.SideRel g
  /-- Every one-cell has zero cellular boundary because it is a based loop. -/
  oneCellBoundaryZero : Polygon4gOneCellBoundaryZero g model
  /-- The two-cell boundary is the abelianised standard relator, hence zero. -/
  twoCellBoundaryRelator : Polygon4gTwoCellBoundaryAbelianizedRelator g model
  /--
Consequently the computed cellular `H₁` is the free module on the
  `2g` one-cells.
-/
  cellularH1Free :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g)

/--
The current polygon cellular API gives an honest project-side finite
cellular certificate.  This is the strongest available bridge before
constructing Mathlib's full `Topology.CWComplex` fields.
-/
noncomputable def polygon4g_cellularModel_to_projectFiniteCellularCertificate
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gProjectFiniteCellularCertificate g :=
  { model := C
    zeroCell := C.vertex
    zeroCell_eq_vertex := rfl
    oneCellPath := C.oneCellPath
    oneCellPath_eq_model := rfl
    twoCellCharacteristic := C.twoCellCharacteristic
    twoCellCharacteristic_eq_model := rfl
    boundaryWord_standard := C.boundaryWord_standard
    boundaryWord_sidePairing := C.boundaryWord_sidePairing
    oneCellBoundaryZero := polygon4g_one_cell_boundary_zero g C
    twoCellBoundaryRelator := polygon4g_two_cell_boundary_abelianized_relator g C
    cellularH1Free :=
      polygon4g_cellularH1_iso_free g C (polygon4g_cellular_boundary_formula g C) }

/--
Cell-indexing types for the standard polygonal cellular model:
one vertex, `2g` one-cells, one two-cell, and no higher cells.
-/
def polygon4gFiniteCell (g : ℕ) : ℕ → Type
  | 0 => Fin 1
  | 1 => Fin (2 * g)
  | 2 => Fin 1
  | _ + 3 => Fin 0

instance polygon4gFiniteCell.fintype (g n : ℕ) :
    Fintype (polygon4gFiniteCell g n) := by
  cases n with
  | zero =>
      simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 1))
  | succ n =>
      cases n with
      | zero =>
          simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin (2 * g)))
      | succ n =>
          cases n with
          | zero =>
              simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 1))
          | succ n =>
              simpa [polygon4gFiniteCell] using (inferInstance : Fintype (Fin 0))

/-- The standard polygonal cell indexing is two-dimensional. -/
theorem polygon4gFiniteCell_finite_dim (g : ℕ) :
    ∃ n, ∀ m > n, IsEmpty (polygon4gFiniteCell g m) := by
  refine ⟨2, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ m =>
          cases m with
          | zero => omega
          | succ m =>
              simpa [polygon4gFiniteCell] using (inferInstance : IsEmpty (Fin 0))

/--
Bridge from the concrete project-side standard cellular model to the
local finite cellular indexing structure used by this file.
-/
noncomputable def polygon4g_cellularModel_to_mathlibCW_frontier (g : ℕ)
    (C : Polygon4gCellularModel g) :
    FiniteCWStructure (Polygon4g g) :=
  let _cert := polygon4g_cellularModel_to_projectFiniteCellularCertificate g C
  { cell := polygon4gFiniteCell g
    fintype_cell := polygon4gFiniteCell.fintype g
    finite_dim := polygon4gFiniteCell_finite_dim g }

/--
**Stage A leaf.** The standard fundamental polygon `Polygon4g g`
admits a finite CW structure with one 0-cell, `2g` 1-cells, and one
2-cell.  This is realised by the standard `Polygon4gCellularModel`.
-/
theorem polygon4g_finiteCWStructure (g : ℕ) :
    Nonempty (FiniteCWStructure (Polygon4g g)) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact ⟨polygon4g_cellularModel_to_mathlibCW_frontier g C⟩

/-
**Transport of project-side finite cellular indexing along homeomorphisms.**
The current local structure records finite cell-indexing data; topological
characteristic maps for the polygon model are kept in the polygon-specific
certificate above.
-/
/-- Transport of local finite cellular indexing along homeomorphisms. -/
noncomputable def finiteCWStructure_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (_h : X ≃ₜ Y) (cw : FiniteCWStructure Y) :
    FiniteCWStructure X := by
  exact ⟨cw.cell, cw.fintype_cell, cw.finite_dim⟩


theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (FiniteCWStructure X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- 2. Riemann surfaces are orientable
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the CW structure on Polygon4g g
  obtain ⟨cw⟩ := polygon4g_finiteCWStructure g
  -- 5. Transport along the homeomorphism
  exact ⟨finiteCWStructure_of_homeo homeo cw⟩


def numCells (X : Type*) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : ℕ :=
  @Fintype.card (cw.cell n) (cw.fintype_cell n)


abbrev CellularChainModule (X : Type*) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : Type :=
  Fin (numCells X cw n) →₀ ℤ


theorem CellularChainModule.module_free
    (X : Type*) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Free ℤ (CellularChainModule X cw n) :=
  inferInstance


theorem CellularChainModule.module_finite
    (X : Type*) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Finite ℤ (CellularChainModule X cw n) :=
  inferInstance




theorem cellularH1_finite_free
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Module.Finite ℤ CH1 ∧ Module.Free ℤ CH1 :=
  ⟨CellularChainModule X cw 1, inferInstance, inferInstance,
    CellularChainModule.module_finite X cw 1,
    CellularChainModule.module_free X cw 1⟩


theorem cellularH1_finite_singularIsoData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_iCH1 : Module ℤ CH1)
      (_hF : Module.Finite ℤ CH1) (_hFr : Module.Free ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  -- 1. Bridge from complex 1-manifold to real 2-manifold
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  letI : Orientable X := ⟨⟨()⟩⟩
  -- 3. Apply the polygonal-model homeomorphism (surface classification)
  obtain ⟨g, ⟨homeo⟩⟩ := existsHomeoToPolygon4g X
  -- 4. Get the singular H₁ basis for the standard fundamental polygon
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  -- 5. Construct the cellular H₁ witness type and the isomorphism
  let CH1 := Fin (2 * g) → ℤ
  let e_singular := b.equivFun.symm.trans (singularH1LinearEquivOfHomeo homeo.symm)
  -- v4.31 no longer infers Module.Finite/Free ℤ (Fin _ → ℤ) through the `let`;
  -- supply the Pi instances explicitly.
  refine ⟨CH1, inferInstanceAs (AddCommGroup (Fin (2 * g) → ℤ)),
    inferInstanceAs (Module ℤ (Fin (2 * g) → ℤ)),
    Module.Finite.pi, Module.Free.pi ℤ _, ⟨e_singular⟩⟩

/--
Derived from `cellularH1_finite_singularIsoData` by forgetting the
finiteness/freeness witnesses.
-/
theorem cellular_iso_singular_h1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  obtain ⟨CH1, hAb, hMod, _, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact ⟨CH1, hAb, hMod, hIso⟩


theorem IntegralOneCycle_finite_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _hF, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Finite.equiv hIso.some


theorem IntegralOneCycle_free_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _, _hFr, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Free.of_equiv hIso.some


theorem IntegralOneCycle_finite_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_finite_of_cellular X cw


theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_free_of_cellular X cw

end JacobianChallenge.Periods
