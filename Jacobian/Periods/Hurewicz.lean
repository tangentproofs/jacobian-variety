import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.EdgeWord


/-!
# Project-side Hurewicz and cellular-to-singular bridge

This file names the comparison theorem missing from Mathlib v4.28.0:
cellular homology agrees with singular homology for the cellular model
of the fundamental polygon.  It is deliberately stated at the narrow
surface needed by the Jacobian project.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory CategoryTheory.Limits SimplexCategory Opposite
-- NOTE: `open Simplicial` is deliberately NOT used here.  Its `scoped[Simplicial]`
-- geometric-realization notation `|X|` (Mathlib.AlgebraicTopology.SingularSet)
-- registers `|` as a leading term token, which under v4.31's parser conflicts with
-- the `|`-pattern syntax of equation-style `def`s and GADT-style inductive
-- constructors used below.  We use `SimplexCategory.mk n` explicitly instead of the
-- Simplicial-scoped `⦋n⦌` notation.

-- The `TangentSpace`/`ModuleCat.carrier` synonyms in this file are non-reducible
-- (`TangentSpace 𝓘(ℂ,ℂ) x := ℂ`, `ModuleCat.carrier`); v4.31's stricter `instances`
-- transparency in `rw`/`change` rejects defeq-but-not-instance-transparent goals.
-- Relaxing the backward compat flag restores the v4.28 behaviour.
set_option backward.isDefEq.respectTransparency false


def Polygon4gAbelianization (g : ℕ) : Type :=
  Fin (2 * (g + 1)) → ℤ


/--
The cellular zero-chain module for the standard polygon model:
free rank one on the unique vertex.
-/
abbrev Polygon4gCellularC0 (_g : ℕ) : Type :=
  Unit → ℤ

/--
The cellular two-chain module for the standard polygon model:
free rank one on the unique two-cell.
-/
abbrev Polygon4gCellularC2 (_g : ℕ) : Type :=
  Unit → ℤ

instance polygon4gCellularC0_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularC0 g) := by
  unfold Polygon4gCellularC0
  infer_instance

instance polygon4gCellularC0_module (g : ℕ) :
    Module ℤ (Polygon4gCellularC0 g) := by
  unfold Polygon4gCellularC0
  infer_instance

instance polygon4gCellularC2_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularC2 g) := by
  unfold Polygon4gCellularC2
  infer_instance

instance polygon4gCellularC2_module (g : ℕ) :
    Module ℤ (Polygon4gCellularC2 g) := by
  unfold Polygon4gCellularC2
  infer_instance

/-- The unique cellular zero-cell generator. -/
def polygon4gCellularC0Vertex {g : ℕ} : Polygon4gCellularC0 g :=
  fun _ => 1

/-- The unique cellular two-cell generator. -/
def polygon4gCellularC2Face {g : ℕ} : Polygon4gCellularC2 g :=
  fun _ => 1

/--
Project-side singular zero-chains on `Polygon4g g`: finitely
supported integral sums of points.
-/
abbrev Polygon4gSingularC0 (g : ℕ) : Type :=
  Polygon4g g →₀ ℤ


namespace Polygon4gSingularC1


/-- The singular chain complex of `Polygon4g g`. -/
noncomputable abbrev polygonChainComplexOnGenus (g : ℕ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g g))

/-- The singular chain complex of a space, with integral coefficients. -/
noncomputable abbrev singularChainComplexZ (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- The shape relation `(down ℕ).next 1 = 0` used by `cyclesMk`. -/
private lemma next_one_eq_zero_on_genus :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/--
The shape relation `(down ℕ).next 1 = 0` used by degree-one
singular-cycle representatives.
-/
private lemma next_one_eq_zero :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/--
Every singular `H₁` class has a singular one-cycle representative.

This is only homological algebra plumbing: `homologyπ` is an epimorphism
from cycles to homology in `ModuleCat`, hence surjective on underlying
modules, and `iCycles` identifies the chosen cycle object element with
an actual chain killed by `d₁`.
-/
theorem singularH1_exists_cycle_repr
    (X : Type) [TopologicalSpace X]
    (y : singularH1 X) :
    ∃ z : SingularChainCoproduct X 1,
    ∃ hz : (singularChainComplexZ X).d 1 0 z = 0,
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ X).homologyπ 1))
        ((singularChainComplexZ X).cyclesMk z 0 next_one_eq_zero hz) = y := by
  let K := singularChainComplexZ X
  have hπ_surj :
      Function.Surjective
        ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) := by
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hπ_surj y
  let z : SingularChainCoproduct X 1 :=
    ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) x
  have hz : K.d 1 0 z = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
        (((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) x) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, K.iCycles_d]
    simp
  refine ⟨z, hz, ?_⟩
  have hcycles :
      K.cyclesMk z 0 next_one_eq_zero hz = x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    simpa [K, z, singularChainComplexZ] using
      (K.i_cyclesMk z 0 next_one_eq_zero hz)
  simpa [K, hcycles] using hx


end Polygon4gSingularC1

/-- The singular chain complex of a space, with integral coefficients. -/
noncomputable abbrev singularChainComplexZ (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  Polygon4gSingularC1.singularChainComplexZ X

/-- Every singular `H₁` class has a singular one-cycle representative. -/
theorem singularH1_exists_cycle_repr
    (X : Type) [TopologicalSpace X]
    (y : singularH1 X) :
    ∃ z : SingularChainCoproduct X 1,
    ∃ hz : (singularChainComplexZ X).d 1 0 z = 0,
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((singularChainComplexZ X).homologyπ 1))
        ((singularChainComplexZ X).cyclesMk z 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz) = y :=
  Polygon4gSingularC1.singularH1_exists_cycle_repr X y

/-- The homology class of a specified singular one-cycle. -/
noncomputable def singularH1ClassOfCycle
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0) :
    singularH1 X :=
  ((forget₂ (ModuleCat ℤ) Ab).map
    ((singularChainComplexZ X).homologyπ 1))
    ((singularChainComplexZ X).cyclesMk z 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)

/--
Two singular one-cycles represent the same `H₁` class when their
difference is the boundary of an explicit singular two-chain.
-/
theorem singularH1ClassOfCycle_eq_of_boundary
    {X : Type} [TopologicalSpace X]
    {z z' : SingularChainCoproduct X 1}
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hz' : (singularChainComplexZ X).d 1 0 z' = 0)
    (B : SingularChainCoproduct X 2)
    (hB : (singularChainComplexZ X).d 2 1 B = z - z') :
    singularH1ClassOfCycle X z hz =
      singularH1ClassOfCycle X z' hz' := by
  let K := singularChainComplexZ X
  let cz :=
    K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz
  let cz' :=
    K.cyclesMk z' 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz'
  have hcycles :
      cz - cz' = ((forget₂ (ModuleCat ℤ) Ab).map (K.toCycles 2 1)) B := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    change
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1)) (cz - cz') =
        ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
          (((forget₂ (ModuleCat ℤ) Ab).map (K.toCycles 2 1)) B)
    rw [map_sub]
    rw [K.i_cyclesMk, K.i_cyclesMk]
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_i]
    exact hB.symm
  unfold singularH1ClassOfCycle
  change ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) cz =
    ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) cz'
  have hzero :
      ((forget₂ (ModuleCat ℤ) Ab).map (K.homologyπ 1)) (cz - cz') = 0 := by
    rw [hcycles]
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/--
The homology class of the sum of two singular one-cycles is the sum
of their homology classes.
-/
theorem singularH1ClassOfCycle_add
    {X : Type} [TopologicalSpace X]
    (z z' : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hz' : (singularChainComplexZ X).d 1 0 z' = 0)
    (hadd : (singularChainComplexZ X).d 1 0 (z + z') = 0) :
    singularH1ClassOfCycle X (z + z') hadd =
      singularH1ClassOfCycle X z hz + singularH1ClassOfCycle X z' hz' := by
  let K := singularChainComplexZ X
  unfold singularH1ClassOfCycle
  have hcycles :
      K.cyclesMk (z + z') 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hadd =
        K.cyclesMk z 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz +
          K.cyclesMk z' 0
            (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz' := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 1)).1 inferInstance
    change
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk (z + z') 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hadd) =
      ((forget₂ (ModuleCat ℤ) Ab).map (K.iCycles 1))
        (K.cyclesMk z 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz +
        K.cyclesMk z' 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz')
    rw [map_add, K.i_cyclesMk, K.i_cyclesMk, K.i_cyclesMk]
  rw [hcycles, map_add]

/-- The quotient map `DiskC → Polygon4g g` as a continuous map. -/
noncomputable def polygon4gMkContinuousMap (g : ℕ) :
    C(DiskC, Polygon4g g) :=
  ⟨Polygon4g.mk g, Polygon4g.mk_continuous g⟩

/--
Functoriality of the exposed singular-chain basis element: the
singular chain map induced by a continuous map sends a generator to the
generator of the composed singular simplex.
-/
theorem singularChainElement_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f n)
        (singularChainElement σ) =
      singularChainElement (f.comp σ) := by
  rw [show singularChainElement σ =
      (singChain_basis σ).hom (1 : ℤ) by rfl]
  rw [show singularChainElement (f.comp σ) =
      (singChain_basis (f.comp σ)).hom (1 : ℤ) by rfl]
  have h := singChain_map_basis f n σ
  have hh := congrArg ModuleCat.Hom.hom h
  exact congrArg (fun F => F (1 : ℤ)) hh

/--
Naturality of `singularH1ClassOfCycle` for the project-level
`singularH1_inducedLinearMap`, stated at the exposed chain level.
-/
theorem singularH1_inducedLinearMap_classOfCycle
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (hmapz :
      (singularChainComplexZ Y).d 1 0
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 1) z) = 0) :
    singularH1_inducedLinearMap f (singularH1ClassOfCycle X z hz) =
      singularH1ClassOfCycle Y
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 1) z) hmapz := by
  let KX := singularChainComplexZ X
  let KY := singularChainComplexZ Y
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
  change
    ((forget₂ (ModuleCat ℤ) Ab).map (HomologicalComplex.homologyMap F 1))
      (((forget₂ (ModuleCat ℤ) Ab).map (KX.homologyπ 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.homologyπ 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.homologyπ_naturality]
  rw [ConcreteCategory.forget₂_comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (KY.iCycles 1)).1 inferInstance
  change
    ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
      (((forget₂ (ModuleCat ℤ) Ab).map (HomologicalComplex.cyclesMap F 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.forget₂_comp_apply]
  change
    ModuleCat.Hom.hom (F.f 1)
      (((forget₂ (ModuleCat ℤ) Ab).map (KX.iCycles 1))
        (KX.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz)) =
      ((forget₂ (ModuleCat ℤ) Ab).map (KY.iCycles 1))
        (KY.cyclesMk (ModuleCat.Hom.hom (F.f 1) z) 0
          (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hmapz)
  rw [KX.i_cyclesMk, KY.i_cyclesMk]

/-- Constant singular zero-simplex at a point. -/
noncomputable def pointSingularSimplex
    (X : Type) [TopologicalSpace X] (x : X) :
    C(stdSimplex ℝ (Fin 1), X) :=
  ⟨fun _ => x, continuous_const⟩

/-- Singular zero-chain represented by a point. -/
noncomputable def pointChain
    (X : Type) [TopologicalSpace X] (x : X) :
    SingularChainCoproduct X 0 :=
  singularChainElement (pointSingularSimplex X x)

lemma singularSimplexFace_path_zero
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    singularSimplexFace (γ.comp stdSimplexToUnitInterval) 0 =
      pointSingularSimplex X (γ 1) := by
  ext s
  haveI : Subsingleton (stdSimplex ℝ (Fin 1)) := inferInstance
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) := this
  have hs : s = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  rw [hs]
  simp [singularSimplexFace, stdSimplexFaceMap, pointSingularSimplex,
    stdSimplexToUnitInterval]

lemma singularSimplexFace_path_one
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    singularSimplexFace (γ.comp stdSimplexToUnitInterval) 1 =
      pointSingularSimplex X (γ 0) := by
  ext s
  haveI : Subsingleton (stdSimplex ℝ (Fin 1)) := inferInstance
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) := this
  have hs : s = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  rw [hs]
  simp [singularSimplexFace, stdSimplexFaceMap, pointSingularSimplex,
    stdSimplexToUnitInterval]

/-- Boundary of a path-shaped singular one-simplex. -/
theorem singularChainElement_boundary_path
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    (singularChainComplexZ X).d 1 0
        (singularChainElement (γ.comp stdSimplexToUnitInterval) :
          SingularChainCoproduct X 1) =
      pointChain X (γ 1) - pointChain X (γ 0) := by
  rw [singularChainElement_boundary_decomposition X 0
        (γ.comp stdSimplexToUnitInterval)]
  rw [Fin.sum_univ_two]
  rw [singularSimplexFace_path_zero X γ, singularSimplexFace_path_one X γ]
  simp [pointChain, pow_zero, pow_one, one_smul, sub_eq_add_neg]

/--
The inverse parametrisation from the unit interval to the standard
one-simplex.
-/
noncomputable def unitIntervalToStdSimplex :
    C(unitInterval, stdSimplex ℝ (Fin 2)) :=
  ⟨stdSimplexHomeomorphUnitInterval.symm,
    stdSimplexHomeomorphUnitInterval.symm.continuous⟩

@[simp] lemma unitIntervalToStdSimplex_zero :
    unitIntervalToStdSimplex (0 : unitInterval) = stdSimplexVertex 0 := by
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [unitIntervalToStdSimplex]

@[simp] lemma unitIntervalToStdSimplex_one :
    unitIntervalToStdSimplex (1 : unitInterval) = stdSimplexVertex 1 := by
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [unitIntervalToStdSimplex]

lemma singularOneSimplex_asPath_comp
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    (σ.comp unitIntervalToStdSimplex).comp stdSimplexToUnitInterval = σ := by
  ext s
  simp [unitIntervalToStdSimplex, stdSimplexToUnitInterval]

/--
Boundary of an arbitrary singular one-simplex, expressed by its two
standard vertices.
-/
theorem singularChainElement_boundary_one_simplex
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    (singularChainComplexZ X).d 1 0
        (singularChainElement σ : SingularChainCoproduct X 1) =
      pointChain X (σ (stdSimplexVertex 1)) -
        pointChain X (σ (stdSimplexVertex 0)) := by
  rw [← singularOneSimplex_asPath_comp X σ]
  rw [singularChainElement_boundary_path X (σ.comp unitIntervalToStdSimplex)]
  simp [unitIntervalToStdSimplex, stdSimplexToUnitInterval]

/-- Chain-map image of a point zero-chain. -/
theorem pointChain_map
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0)
      (pointChain X x) =
        pointChain Y (f x) := by
  have h := singularChainElement_map f 0 (pointSingularSimplex X x)
  have hcomp : f.comp (pointSingularSimplex X x) = pointSingularSimplex Y (f x) := by
    ext y; rfl
  rw [pointChain, pointChain, h, hcomp]

/-- Orientation for a primitive boundary-edge repair step. -/
inductive BoundaryArcOrientation where
  | forward
  | reverse
  deriving DecidableEq

namespace BoundaryArcOrientation

/-- The integral sign represented by an oriented boundary edge. -/
def sign (o : BoundaryArcOrientation) : ℤ :=
  match o with
  | forward => 1
  | reverse => -1

/-- Reverse an oriented boundary edge. -/
def flip (o : BoundaryArcOrientation) : BoundaryArcOrientation :=
  match o with
  | forward => reverse
  | reverse => forward

lemma sign_eq (o : BoundaryArcOrientation) : sign o = 1 ∨ sign o = -1 := by
  cases o <;> simp [sign]

lemma sign_flip (o : BoundaryArcOrientation) :
    sign (flip o) = - sign o := by
  cases o <;> simp [sign, flip]

end BoundaryArcOrientation

/-- Reversal of the unit interval. -/
noncomputable def unitIntervalReverse : C(unitInterval, unitInterval) where
  toFun := fun t =>
    ⟨1 - t.1, by
      exact ⟨sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_const.sub continuous_subtype_val) _

@[simp] lemma unitIntervalReverse_zero :
    unitIntervalReverse 0 = (1 : unitInterval) := by
  ext
  norm_num [unitIntervalReverse]

@[simp] lemma unitIntervalReverse_one :
    unitIntervalReverse 1 = (0 : unitInterval) := by
  ext
  norm_num [unitIntervalReverse]

/-- The degenerate two-simplex in `[0,1]` filling an interval and its reverse. -/
noncomputable def unitIntervalReversePrismSimplex :
    C(stdSimplex ℝ (Fin 3), unitInterval) where
  toFun := fun p =>
    ⟨p.1 1, mem_Icc_of_mem_stdSimplex p.2 1⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      ((continuous_apply 1).comp continuous_subtype_val) _

/-- Constant singular one-simplex at `0 : unitInterval`. -/
noncomputable def unitIntervalConstantZeroOneSimplex :
    C(stdSimplex ℝ (Fin 2), unitInterval) :=
  ⟨fun _ => (0 : unitInterval), continuous_const⟩

/-- Constant singular two-simplex at `0 : unitInterval`. -/
noncomputable def unitIntervalConstantZeroTwoSimplex :
    C(stdSimplex ℝ (Fin 3), unitInterval) :=
  ⟨fun _ => (0 : unitInterval), continuous_const⟩

lemma unitIntervalConstantZeroTwoSimplex_face (i : Fin 3) :
    singularSimplexFace unitIntervalConstantZeroTwoSimplex i =
      unitIntervalConstantZeroOneSimplex := by
  ext s
  rfl

lemma unitIntervalReversePrismSimplex_face_zero :
    singularSimplexFace unitIntervalReversePrismSimplex (0 : Fin 3) =
      unitIntervalReverse.comp stdSimplexToUnitInterval := by
  ext s
  have hcoord :
      (stdSimplex.map Fin.succ s).val (1 : Fin 3) = s.1 (0 : Fin 2) := by
    exact stdSimplex_map_succ_apply (n := 1) s (0 : Fin 2)
  have hsum : s.1 0 + s.1 1 = 1 := by
    simpa [Fin.sum_univ_two] using s.2.2
  simp [singularSimplexFace, stdSimplexFaceMap, unitIntervalReversePrismSimplex,
    unitIntervalReverse, stdSimplexToUnitInterval, hcoord]
  linarith

lemma unitIntervalReversePrismSimplex_face_one :
    singularSimplexFace unitIntervalReversePrismSimplex (1 : Fin 3) =
      unitIntervalConstantZeroOneSimplex := by
  ext s
  exact stdSimplex_map_succAbove_coord_eq_zero (n := 1) (j := (1 : Fin 3)) s

lemma unitIntervalReversePrismSimplex_face_two :
    singularSimplexFace unitIntervalReversePrismSimplex (2 : Fin 3) =
      stdSimplexToUnitInterval := by
  ext s
  have hcoord :
      (stdSimplex.map (Fin.succAbove (2 : Fin 3)) s).val (1 : Fin 3) =
        s.1 (1 : Fin 2) := by
    have hsucc :
        (Fin.succAbove (2 : Fin 3) : Fin 2 → Fin 3) = Fin.castSucc := by
      funext k
      fin_cases k <;> rfl
    rw [hsucc]
    exact
      stdSimplex_map_castSucc_apply (n := 1) s (1 : Fin 2)
  simp [singularSimplexFace, stdSimplexFaceMap, unitIntervalReversePrismSimplex,
    stdSimplexToUnitInterval, hcoord]

/--
Concrete unit-interval reverse prism boundary.  This is the purely
geometric chain in `[0,1]` whose boundary is the standard interval
simplex plus its reversed parametrization.
-/
theorem unitInterval_reverse_prism_boundary :
    ∃ reverseHomotopy : SingularChainCoproduct unitInterval 2,
      (singularChainComplexZ unitInterval).d 2 1 reverseHomotopy =
        singularChainElement
          (unitIntervalReverse.comp stdSimplexToUnitInterval) +
        singularChainElement stdSimplexToUnitInterval := by
  refine ⟨singularChainElement unitIntervalReversePrismSimplex +
      singularChainElement unitIntervalConstantZeroTwoSimplex, ?_⟩
  rw [map_add]
  rw [singularChainElement_boundary_decomposition unitInterval 1
        unitIntervalReversePrismSimplex]
  rw [singularChainElement_boundary_decomposition unitInterval 1
        unitIntervalConstantZeroTwoSimplex]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [unitIntervalReversePrismSimplex_face_zero,
    unitIntervalReversePrismSimplex_face_one,
    unitIntervalReversePrismSimplex_face_two,
    unitIntervalConstantZeroTwoSimplex_face]
  abel

/--
Local reverse-reparametrization prism for one path-shaped singular
simplex.  This is the exact relative one-simplex leaf needed by
boundary-arc reversal: a path and the same path traversed with
`t ↦ 1 - t` bound a singular two-chain.
-/
theorem singularChainElement_reverse_path_homologous
    (X : Type) [TopologicalSpace X] (γ : C(unitInterval, X)) :
    ∃ reverseHomotopy : SingularChainCoproduct X 2,
      (singularChainComplexZ X).d 2 1 reverseHomotopy =
        singularChainElement
          ((γ.comp unitIntervalReverse).comp stdSimplexToUnitInterval) +
        singularChainElement (γ.comp stdSimplexToUnitInterval) := by
  obtain ⟨B, hB⟩ := unitInterval_reverse_prism_boundary
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ))
  refine ⟨ModuleCat.Hom.hom (F.f 2) B, ?_⟩
  have hcomm :
      ModuleCat.Hom.hom (F.f 1)
          ((singularChainComplexZ unitInterval).d 2 1 B) =
        (singularChainComplexZ X).d 2 1
          (ModuleCat.Hom.hom (F.f 2) B) := by
    rw [← ModuleCat.comp_apply ((singularChainComplexZ unitInterval).d 2 1) (F.f 1)]
    rw [← ModuleCat.comp_apply (F.f 2) ((singularChainComplexZ X).d 2 1)]
    exact congrArg
      (fun φ : (singularChainComplexZ unitInterval).X 2 ⟶
          (singularChainComplexZ X).X 1 =>
        ModuleCat.Hom.hom φ B)
      (F.comm 2 1).symm
  rw [← hcomm, hB, map_add]
  rw [singularChainElement_map γ 1
      (unitIntervalReverse.comp stdSimplexToUnitInterval)]
  rw [singularChainElement_map γ 1 stdSimplexToUnitInterval]
  rw [ContinuousMap.comp_assoc]

/--
The parameter along a partial oriented boundary arc.  The
`startParam` and `endParam` fields are closed-interval points, so this
can represent arbitrary side-interior endpoints, not only full side
endpoints.
-/
noncomputable def boundaryArcOrientedAffineParam
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) : ℝ :=
  match orientation with
  | BoundaryArcOrientation.forward =>
      (1 - t.1) * startParam.1 + t.1 * endParam.1
  | BoundaryArcOrientation.reverse =>
      (1 - t.1) * endParam.1 + t.1 * startParam.1

lemma boundaryArcOrientedAffineParam_flip_reverse
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) :
    boundaryArcOrientedAffineParam (BoundaryArcOrientation.flip orientation)
        startParam endParam t =
      boundaryArcOrientedAffineParam orientation startParam endParam
        (unitIntervalReverse t) := by
  cases orientation <;>
    simp [boundaryArcOrientedAffineParam, BoundaryArcOrientation.flip,
      unitIntervalReverse]
  · ring_nf
  · ring_nf

lemma boundaryArcOrientedAffineParam_swap_reverse
    (orientation : BoundaryArcOrientation)
    (startParam endParam : Set.Icc (0 : ℝ) 1)
    (t : unitInterval) :
    boundaryArcOrientedAffineParam orientation endParam startParam t =
      boundaryArcOrientedAffineParam orientation startParam endParam
        (unitIntervalReverse t) := by
  cases orientation <;>
    simp [boundaryArcOrientedAffineParam, unitIntervalReverse]
  · ring_nf
  · ring_nf

/--
A boundary-arc path in the closed disk, with orientation and a
concrete boundary parametrisation witness.  The side arc may be only a
partial boundary side, and `arcIndex` may be either the canonical
edge-basis side or its paired opposite side.
-/
structure Polygon4gBoundaryArcStep (g : ℕ) where
  source : DiskC
  target : DiskC
  edgeIndex : Fin (2 * (g + 1))
  arcIndex : ℕ
  arcIndex_represents_edge :
    arcIndex = edgeArcIdx g edgeIndex ∨
      arcIndex = edgeArcIdx g edgeIndex + 2
  orientation : BoundaryArcOrientation
  startParam : Set.Icc (0 : ℝ) 1
  endParam : Set.Icc (0 : ℝ) 1
  path : C(unitInterval, DiskC)
  source_eq : path 0 = source
  target_eq : path 1 = target
  path_param :
    ∀ t : unitInterval,
      path t = boundaryParam (g + 1) arcIndex
        (boundaryArcOrientedAffineParam orientation startParam endParam t)

/--
Reverse a boundary-arc step, swapping endpoints and interval
parameters.  The stored edge orientation is left unchanged: the path
itself is reversed, so the signed singular chain has the negated
boundary needed by endpoint repair symmetry.
-/
noncomputable def Polygon4gBoundaryArcStep.reverse
    {g : ℕ} (step : Polygon4gBoundaryArcStep g) :
    Polygon4gBoundaryArcStep g where
  source := step.target
  target := step.source
  edgeIndex := step.edgeIndex
  arcIndex := step.arcIndex
  arcIndex_represents_edge := step.arcIndex_represents_edge
  orientation := step.orientation
  startParam := step.endParam
  endParam := step.startParam
  path := step.path.comp unitIntervalReverse
  source_eq := by
    simp [ContinuousMap.comp_apply, step.target_eq]
  target_eq := by
    simp [ContinuousMap.comp_apply, step.source_eq]
  path_param := by
    intro t
    rw [ContinuousMap.comp_apply, step.path_param]
    exact congrArg (boundaryParam (g + 1) step.arcIndex)
      (boundaryArcOrientedAffineParam_swap_reverse
        step.orientation step.startParam step.endParam t).symm

/-- A finite list of boundary arcs connects two disk endpoints. -/
inductive Polygon4gBoundaryArcListConnects (g : ℕ) :
    DiskC → DiskC → List (Polygon4gBoundaryArcStep g) → Prop
  | nil (p : DiskC) : Polygon4gBoundaryArcListConnects g p p []
  | cons {p q r : DiskC} {step : Polygon4gBoundaryArcStep g}
      {steps : List (Polygon4gBoundaryArcStep g)}
      (hsource : step.source = p)
      (htarget : step.target = q)
      (hrest : Polygon4gBoundaryArcListConnects g q r steps) :
      Polygon4gBoundaryArcListConnects g p r (step :: steps)

/--
Concatenating two connected boundary-arc lists gives a connected
boundary-arc list.
-/
theorem Polygon4gBoundaryArcListConnects.append
    {g : ℕ} {p q r : DiskC}
    {steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)}
    (h₁ : Polygon4gBoundaryArcListConnects g p q steps₁)
    (h₂ : Polygon4gBoundaryArcListConnects g q r steps₂) :
    Polygon4gBoundaryArcListConnects g p r (steps₁ ++ steps₂) := by
  induction h₁ with
  | nil p =>
      simpa using h₂
  | cons hsource htarget hrest ih =>
      exact Polygon4gBoundaryArcListConnects.cons hsource htarget (ih h₂)

/--
Reverse a list of boundary-arc steps in the order needed for a
path reversal.
-/
noncomputable def polygon4gBoundaryArcStepsReverse
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    List (Polygon4gBoundaryArcStep g) :=
  steps.reverse.map Polygon4gBoundaryArcStep.reverse

/--
A connected boundary-arc list remains connected after reversing all
steps and their order.
-/
theorem Polygon4gBoundaryArcListConnects.reverse
    {g : ℕ} {p q : DiskC} {steps : List (Polygon4gBoundaryArcStep g)}
    (h : Polygon4gBoundaryArcListConnects g p q steps) :
    Polygon4gBoundaryArcListConnects g q p
      (polygon4gBoundaryArcStepsReverse steps) := by
  induction h with
  | nil p =>
      simp [polygon4gBoundaryArcStepsReverse,
        Polygon4gBoundaryArcListConnects.nil]
  | cons hsource htarget hrest ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append]
      refine Polygon4gBoundaryArcListConnects.append ih ?_
      exact Polygon4gBoundaryArcListConnects.cons htarget hsource
        (Polygon4gBoundaryArcListConnects.nil _)

/-- The projected singular one-chain of a disk boundary-arc step. -/
noncomputable def polygon4gBoundaryArcStepProjectedChain
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
  singularChainElement
    ((polygon4gMkContinuousMap (g + 1)).comp
      (step.path.comp stdSimplexToUnitInterval))

/--
The disk-side singular one-chain of a list of boundary-arc steps,
with the recorded orientations.
-/
noncomputable def polygon4gBoundaryArcStepsDiskChain
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    SingularChainCoproduct DiskC 1 :=
  (steps.map fun step =>
    step.orientation.sign • singularChainElement
      (step.path.comp stdSimplexToUnitInterval)).sum

/-- Disk-side chains of boundary-arc lists respect append. -/
theorem polygon4gBoundaryArcStepsDiskChain_append
    {g : ℕ} (steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)) :
    polygon4gBoundaryArcStepsDiskChain (steps₁ ++ steps₂) =
      polygon4gBoundaryArcStepsDiskChain steps₁ +
        polygon4gBoundaryArcStepsDiskChain steps₂ := by
  simp [polygon4gBoundaryArcStepsDiskChain, List.map_append]

/--
The projected singular chain of a list of boundary-arc steps, with
the recorded orientations.
-/
noncomputable def polygon4gBoundaryArcStepsProjectedChain
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
  (steps.map fun step =>
    step.orientation.sign • polygon4gBoundaryArcStepProjectedChain g step).sum

/-- Projected chains of boundary-arc lists respect append. -/
theorem polygon4gBoundaryArcStepsProjectedChain_append
    (g : ℕ) (steps₁ steps₂ : List (Polygon4gBoundaryArcStep g)) :
    polygon4gBoundaryArcStepsProjectedChain g (steps₁ ++ steps₂) =
      polygon4gBoundaryArcStepsProjectedChain g steps₁ +
        polygon4gBoundaryArcStepsProjectedChain g steps₂ := by
  simp [polygon4gBoundaryArcStepsProjectedChain, List.map_append]

/--
The disk boundary of a reversed single boundary-arc generator is the
negative of the original disk boundary.
-/
theorem polygon4gBoundaryArcStep_reverse_disk_boundary
    {g : ℕ} (step : Polygon4gBoundaryArcStep g) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          [Polygon4gBoundaryArcStep.reverse step]) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain [step]) := by
  simp [polygon4gBoundaryArcStepsDiskChain, map_zsmul]
  rw [singularChainElement_boundary_path DiskC
    (Polygon4gBoundaryArcStep.reverse step).path]
  rw [singularChainElement_boundary_path DiskC step.path]
  simp [Polygon4gBoundaryArcStep.reverse, ContinuousMap.comp_apply,
    step.source_eq, step.target_eq]
  rcases BoundaryArcOrientation.sign_eq step.orientation with hsign | hsign
  · rw [hsign]
    simp
  · rw [hsign]
    simp

/--
The projected boundary of a reversed single boundary-arc generator
is the negative of the original projected boundary.
-/
theorem polygon4gBoundaryArcStep_reverse_projected_boundary
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          [Polygon4gBoundaryArcStep.reverse step]) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g [step]) := by
  simp [polygon4gBoundaryArcStepsProjectedChain,
    polygon4gBoundaryArcStepProjectedChain, map_zsmul]
  rw [show (polygon4gMkContinuousMap (g + 1)).comp
      ((Polygon4gBoundaryArcStep.reverse step).path.comp stdSimplexToUnitInterval) =
        ((polygon4gMkContinuousMap (g + 1)).comp
          (Polygon4gBoundaryArcStep.reverse step).path).comp
            stdSimplexToUnitInterval by
      rw [ContinuousMap.comp_assoc]]
  rw [show (polygon4gMkContinuousMap (g + 1)).comp
      (step.path.comp stdSimplexToUnitInterval) =
        ((polygon4gMkContinuousMap (g + 1)).comp step.path).comp
          stdSimplexToUnitInterval by
      rw [ContinuousMap.comp_assoc]]
  rw [singularChainElement_boundary_path (Polygon4g (g + 1))
    ((polygon4gMkContinuousMap (g + 1)).comp
      (Polygon4gBoundaryArcStep.reverse step).path)]
  rw [singularChainElement_boundary_path (Polygon4g (g + 1))
    ((polygon4gMkContinuousMap (g + 1)).comp step.path)]
  simp [Polygon4gBoundaryArcStep.reverse, ContinuousMap.comp_apply,
    step.source_eq, step.target_eq]
  rcases BoundaryArcOrientation.sign_eq step.orientation with hsign | hsign
  · rw [hsign]
    simp
  · rw [hsign]
    simp

/-- Reversing a boundary-arc list negates its disk-side boundary. -/
theorem polygon4gBoundaryArcStepsReverse_disk_boundary
    {g : ℕ} (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain steps) := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsDiskChain]
  | cons step steps ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsDiskChain_append, map_add]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [ih]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hstep := polygon4gBoundaryArcStep_reverse_disk_boundary step
      rw [hstep]
      have hcons :
          polygon4gBoundaryArcStepsDiskChain (step :: steps) =
            polygon4gBoundaryArcStepsDiskChain [step] +
              polygon4gBoundaryArcStepsDiskChain steps := by
        simp [polygon4gBoundaryArcStepsDiskChain]
      rw [hcons, map_add]
      abel

/-- Reversing a boundary-arc list negates its projected boundary. -/
theorem polygon4gBoundaryArcStepsReverse_projected_boundary
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g steps) := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsProjectedChain_append, map_add]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [ih]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hstep := polygon4gBoundaryArcStep_reverse_projected_boundary g step
      rw [hstep]
      have hcons :
          polygon4gBoundaryArcStepsProjectedChain g (step :: steps) =
            polygon4gBoundaryArcStepsProjectedChain g [step] +
              polygon4gBoundaryArcStepsProjectedChain g steps := by
        simp [polygon4gBoundaryArcStepsProjectedChain]
      rw [hcons, map_add]
      abel

/--
Remaining one-step local prism leaf: a projected boundary-arc
simplex and its reversed reparametrization bound a singular two-chain.
The list-level statement below is just finite additivity.
-/
theorem polygon4gBoundaryArcStep_reverse_projected_homotopy
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            [Polygon4gBoundaryArcStep.reverse step] +
          polygon4gBoundaryArcStepsProjectedChain g [step] := by
  let γ : C(unitInterval, Polygon4g (g + 1)) :=
    (polygon4gMkContinuousMap (g + 1)).comp step.path
  obtain ⟨B, hB⟩ :=
    singularChainElement_reverse_path_homologous
      (Polygon4g (g + 1)) γ
  refine ⟨step.orientation.sign • B, ?_⟩
  rw [map_zsmul, hB, zsmul_add]
  simp [polygon4gBoundaryArcStepsProjectedChain,
    polygon4gBoundaryArcStepProjectedChain, Polygon4gBoundaryArcStep.reverse,
    γ, ContinuousMap.comp_assoc]

/--
Reversing a finite list of projected boundary-arc chains is
homologous to negation, by summing the one-step reverse prisms.
-/
theorem polygon4gBoundaryArcStepsReverse_projected_homotopy
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            (polygon4gBoundaryArcStepsReverse steps) +
          polygon4gBoundaryArcStepsProjectedChain g steps := by
  induction steps with
  | nil =>
      refine ⟨0, ?_⟩
      simp [polygon4gBoundaryArcStepsReverse,
        polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      obtain ⟨Bsteps, hBsteps⟩ := ih
      obtain ⟨Bstep, hBstep⟩ :=
        polygon4gBoundaryArcStep_reverse_projected_homotopy g step
      refine ⟨Bsteps + Bstep, ?_⟩
      rw [map_add, hBsteps, hBstep]
      dsimp [polygon4gBoundaryArcStepsReverse]
      rw [List.reverse_cons, List.map_append,
        polygon4gBoundaryArcStepsProjectedChain_append]
      rw [show List.map Polygon4gBoundaryArcStep.reverse steps.reverse =
        polygon4gBoundaryArcStepsReverse steps from rfl]
      rw [show List.map Polygon4gBoundaryArcStep.reverse [step] =
        [Polygon4gBoundaryArcStep.reverse step] from rfl]
      have hcons :
          polygon4gBoundaryArcStepsProjectedChain g (step :: steps) =
            polygon4gBoundaryArcStepsProjectedChain g [step] +
              polygon4gBoundaryArcStepsProjectedChain g steps := by
        simp [polygon4gBoundaryArcStepsProjectedChain]
      rw [hcons]
      abel

/--
The list-level chain identities needed to reverse endpoint repair
data.  Boundary reversal is exact, while the comparison between a
singular one-simplex and its reversed reparametrization is supplied by
the standard prism homotopy.
-/
theorem polygon4gBoundaryArcStepsReverse_repair_identities
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ DiskC).d 1 0
        (polygon4gBoundaryArcStepsDiskChain steps) ∧
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g
          (polygon4gBoundaryArcStepsReverse steps)) =
      - (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        (polygon4gBoundaryArcStepsProjectedChain g steps) ∧
    ∃ projectedReverseHomotopy :
        SingularChainCoproduct (Polygon4g (g + 1)) 2,
      (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
          projectedReverseHomotopy =
        polygon4gBoundaryArcStepsProjectedChain g
            (polygon4gBoundaryArcStepsReverse steps) +
          polygon4gBoundaryArcStepsProjectedChain g steps := by
  exact ⟨polygon4gBoundaryArcStepsReverse_disk_boundary steps,
    polygon4gBoundaryArcStepsReverse_projected_boundary g steps,
    polygon4gBoundaryArcStepsReverse_projected_homotopy g steps⟩


/--
Early local copy of the concrete quotient fact needed by the subdivision
leaf: a zero `H₁` class is represented by an explicit degree-one
short-complex boundary.
-/
theorem singularH1ClassOfCycle_eq_zero_sc_boundary
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (h : singularH1ClassOfCycle X z hz = 0) :
    ∃ B : ((singularChainComplexZ X).sc 1).X₁,
      ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B = z := by
  let K := singularChainComplexZ X
  let S := K.sc 1
  let c : K.cycles 1 :=
    K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz
  have hπ :
      ModuleCat.Hom.hom (K.homologyπ 1) c = 0 := by
    change singularH1ClassOfCycle X z hz = 0 at h
    simpa [K, c, singularH1ClassOfCycle] using h
  have hπS :
      ModuleCat.Hom.hom S.homologyπ c = 0 := hπ
  have hq :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) = 0 := by
    have hπiso :
        ModuleCat.Hom.hom (S.homologyπ ≫ S.moduleCatHomologyIso.hom) c = 0 := by
      rw [ModuleCat.comp_apply, hπS, map_zero]
    rwa [S.π_moduleCatCyclesIso_hom] at hπiso
  have hmem :
      ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c ∈
        LinearMap.range S.moduleCatLeftHomologyData.f'.hom := by
    simpa [ShortComplex.moduleCatLeftHomologyData_π_hom] using
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range S.moduleCatLeftHomologyData.f'.hom)).1 hq
  rcases hmem with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  have hBsub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) := by
    rw [hB]
  have hcycleSub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) =
        ModuleCat.Hom.hom S.iCycles c := by
    rw [← ModuleCat.comp_apply, S.moduleCatCyclesIso_hom_i]
  calc
    ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) := by
          change ModuleCat.Hom.hom S.f B =
            ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
              (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B)
          rw [← ModuleCat.comp_apply, S.moduleCatLeftHomologyData.f'_i]
    _ = ModuleCat.Hom.hom S.iCycles c := by
      rw [hBsub, hcycleSub]
    _ = z := by
      exact K.i_cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz

/--
Early local bridge from the degree-one short-complex boundary object
to the displayed degree-two singular-chain differential.
-/
theorem hurewicz_singularBoundary_eq_sc_f_early
    (X : Type) [TopologicalSpace X] :
    let K := singularChainComplexZ X
    let S := K.sc 1
    ∀ (s : S.X₁), ∃ s' : (singularChainComplexZ X).X 2,
      S.f.hom s = ((singularChainComplexZ X).d 2 1).hom s' := by
  intro K S s
  -- `S.f = K.d ((ComplexShape.down ℕ).prev 1) 1` and `(ComplexShape.down ℕ).prev 1 = 2`,
  -- so the short-complex map is the degree-`(2,1)` differential precomposed with the
  -- canonical degree-coincidence isomorphism.
  have hprev : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (rfl : (ComplexShape.down ℕ).Rel 2 1)
  refine ⟨(K.XIsoOfEq hprev).hom s, ?_⟩
  have hcomp := K.XIsoOfEq_hom_comp_d hprev 1
  have h := congrArg (fun (φ : _ ⟶ _) => ModuleCat.Hom.hom φ s) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm


structure SingularOneSimplexSubdivisionData
    (n : ℕ)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))) where
  n_pos : 0 < n
  first_endpoint :
    subSimplex ⟨0, n_pos⟩ (stdSimplexVertex 0) = stdSimplexVertex 0
  last_endpoint :
    subSimplex ⟨n - 1, Nat.sub_lt n_pos zero_lt_one⟩
        (stdSimplexVertex 1) =
      stdSimplexVertex 1
  adjacent_endpoints :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      subSimplex i (stdSimplexVertex 1) =
        subSimplex j (stdSimplexVertex 0)

instance stdSimplex_fin_two_contractibleSpace :
    ContractibleSpace (stdSimplex ℝ (Fin 2)) :=
  (convex_stdSimplex (𝕜 := ℝ) (ι := Fin 2)).contractibleSpace
    ⟨stdSimplexVertex 0, (stdSimplexVertex 0).2⟩

noncomputable def subdivisionVertexChain
    (n : ℕ)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (k : ℕ) : SingularChainCoproduct (stdSimplex ℝ (Fin 2)) 0 :=
  if h : k < n then
    pointChain (stdSimplex ℝ (Fin 2))
      (subSimplex ⟨k, h⟩ (stdSimplexVertex 0))
  else
    pointChain (stdSimplex ℝ (Fin 2)) (stdSimplexVertex 1)

lemma subdivisionVertexChain_zero
    (n : ℕ) (hn : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex) :
    subdivisionVertexChain n subSimplex 0 =
      pointChain (stdSimplex ℝ (Fin 2)) (stdSimplexVertex 0) := by
  simp [subdivisionVertexChain, hn, subdivision_valid.first_endpoint]

lemma subdivisionVertexChain_last
    (n : ℕ)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))) :
    subdivisionVertexChain n subSimplex n =
      pointChain (stdSimplex ℝ (Fin 2)) (stdSimplexVertex 1) := by
  simp [subdivisionVertexChain]

lemma subdivisionVertexChain_succ
    (n : ℕ) (hn : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex)
    (i : Fin n) :
    subdivisionVertexChain n subSimplex (i.1 + 1) =
      pointChain (stdSimplex ℝ (Fin 2))
        (subSimplex i (stdSimplexVertex 1)) := by
  by_cases hsucc : i.1 + 1 < n
  · have hadj :
        subSimplex i (stdSimplexVertex 1) =
          subSimplex ⟨i.1 + 1, hsucc⟩ (stdSimplexVertex 0) :=
      subdivision_valid.adjacent_endpoints i ⟨i.1 + 1, hsucc⟩ rfl
    simp [subdivisionVertexChain, hsucc, hadj]
  · have hi_last : i.1 = n - 1 := by omega
    have hi_eq : i = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      ext
      exact hi_last
    rw [hi_eq]
    have hlast := subdivision_valid.last_endpoint
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp [subdivisionVertexChain, hnsub, hlast]

lemma subdivision_boundary_cycle
    (n : ℕ) (hn : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex) :
    (singularChainComplexZ (stdSimplex ℝ (Fin 2))).d 1 0
        ((∑ i : Fin n, singularChainElement (subSimplex i)) -
          singularChainElement (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) =
      0 := by
  let v := subdivisionVertexChain n subSimplex
  have hpieces :
      (singularChainComplexZ (stdSimplex ℝ (Fin 2))).d 1 0
          (∑ i : Fin n, singularChainElement (subSimplex i)) =
        ∑ i : Fin n, (v (i.1 + 1) - v i.1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [singularChainElement_boundary_one_simplex
      (stdSimplex ℝ (Fin 2)) (subSimplex i)]
    change pointChain (stdSimplex ℝ (Fin 2))
        (subSimplex i (stdSimplexVertex 1)) -
        pointChain (stdSimplex ℝ (Fin 2))
          (subSimplex i (stdSimplexVertex 0)) =
      subdivisionVertexChain n subSimplex (i.1 + 1) -
        subdivisionVertexChain n subSimplex i.1
    rw [subdivisionVertexChain_succ n hn subSimplex subdivision_valid i]
    simp [subdivisionVertexChain, i.2]
  have htel :
      (∑ i : Fin n, (v (i.1 + 1) - v i.1)) =
        pointChain (stdSimplex ℝ (Fin 2)) (stdSimplexVertex 1) -
          pointChain (stdSimplex ℝ (Fin 2)) (stdSimplexVertex 0) := by
    rw [Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun k => v (k + 1))]
    rw [Fin.sum_univ_eq_sum_range (fun k => v k)]
    simpa [v, subdivisionVertexChain_last,
      subdivisionVertexChain_zero n hn subSimplex subdivision_valid] using
      (Finset.sum_range_sub v n)
  rw [map_sub, hpieces, htel]
  rw [singularChainElement_boundary_one_simplex
    (stdSimplex ℝ (Fin 2)) (ContinuousMap.id (stdSimplex ℝ (Fin 2)))]
  simp

/--
Finite local lifting data for a singular one-simplex in the polygon
quotient.  This records an actual finite subdivision by sub-simplices:
each piece has a disk lift, adjacent lifted endpoints are related by
`SideRel`, and the subdivided projected chain is homologous to the
original simplex chain.
-/
structure Polygon4gSingularSimplexDiskLiftData
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) where
  n : ℕ
  n_pos : 0 < n
  subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))
  subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex
  lift : Fin n → C(stdSimplex ℝ (Fin 2), DiskC)
  projects_on_piece :
    ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      Polygon4g.mk (g + 1) (lift i s) = σ (subSimplex i s)
  adjacent_endpoint_rel :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      Polygon4g.SideRel (g + 1)
        (lift i (stdSimplexVertex 1))
        (lift j (stdSimplexVertex 0))
  subdividedChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  subdividedChain_eq :
    subdividedChain =
      ∑ i : Fin n,
        singularChainElement ((polygon4gMkContinuousMap (g + 1)).comp (lift i))
  subdivisionBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  subdivision_homology :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 subdivisionBoundary =
      subdividedChain - singularChainElement σ

/--
Finite local-lift data for a polygon quotient path, before the
pure singular-chain subdivision homology is attached.  This is the
topological part of `polygon4g_singularSimplex_subdivision_lifts_to_disk`:
subdivide the interval into finitely many pieces admitting disk lifts,
and record that adjacent lifted endpoints differ by the polygon side
relation.
-/
structure Polygon4gQuotientPathFiniteLiftSubdivision
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) where
  n : ℕ
  n_pos : 0 < n
  subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2))
  subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex
  lift : Fin n → C(stdSimplex ℝ (Fin 2), DiskC)
  projects_on_piece :
    ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      Polygon4g.mk (g + 1) (lift i s) = σ (subSimplex i s)
  adjacent_endpoint_rel :
    ∀ (i j : Fin n), i.1 + 1 = j.1 →
      Polygon4g.SideRel (g + 1)
        (lift i (stdSimplexVertex 1))
        (lift j (stdSimplexVertex 0))

/--
Interior points of the disk have trivial side-pairing fibres.

Every generator of `Polygon4g.SideRel` lies on the boundary circle
(`‖z‖ = 1`).  Hence an equivalence-chain starting from a point with
`‖z‖ < 1` cannot take a non-reflexive side-pairing step, so the
equivalence class is the singleton `{z}`.  This is the first local
section chart for the quotient map: over the open disk interior,
`Polygon4g.mk` is locally represented by the identity lift.
-/
theorem polygon4g_sideRel_eq_of_norm_lt_one
    (g : ℕ) {z w : DiskC} (hz : ‖(z : ℂ)‖ < 1)
    (hrel : Polygon4g.SideRel g z w) : z = w := by
  let Q : DiskC → DiskC → Prop := fun a b =>
    a = b ∨ (‖(a : ℂ)‖ = 1 ∧ ‖(b : ℂ)‖ = 1)
  have hQ_equiv : Equivalence Q := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b hab
      rcases hab with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with hab | ⟨ha, hb⟩
      · subst b
        exact hbc
      · rcases hbc with hbc | ⟨_hb, hc⟩
        · subst c
          exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩
  have hgenQ : ∀ a b : DiskC, Polygon4g.SideGen g a b → Q a b := by
    intro a b hgen
    cases hgen with
    | a_pair i t ht =>
        exact Or.inr ⟨by
          simpa [boundaryParam, boundaryParam'] using
            boundaryParamC'_norm_eq_one (4 * g) (4 * i.val) t, by
          simpa [boundaryParam, boundaryParam'] using
            boundaryParamC'_norm_eq_one (4 * g) (4 * i.val + 2) (1 - t)⟩
    | b_pair i t ht =>
        exact Or.inr ⟨by
          simpa [boundaryParam, boundaryParam'] using
            boundaryParamC'_norm_eq_one (4 * g) (4 * i.val + 1) t, by
          simpa [boundaryParam, boundaryParam'] using
            boundaryParamC'_norm_eq_one (4 * g) (4 * i.val + 3) (1 - t)⟩
  have hQ : Q z w :=
    (hQ_equiv.eqvGen_iff).mp (Relation.EqvGen.mono hgenQ hrel)
  rcases hQ with h | ⟨hz_boundary, _hw_boundary⟩
  · exact h
  · nlinarith

/--
Interior quotient-kernel form of
`polygon4g_sideRel_eq_of_norm_lt_one`: two disk points in the same
quotient fibre are equal as soon as the first point lies in the open
disk.
-/
theorem polygon4g_mk_eq_of_norm_lt_one
    (g : ℕ) {z w : DiskC} (hz : ‖(z : ℂ)‖ < 1)
    (hmk : Polygon4g.mk g z = Polygon4g.mk g w) : z = w :=
  polygon4g_sideRel_eq_of_norm_lt_one g hz
    ((Polygon4g.mk_eq_mk_iff g z w).mp hmk)

/--
Local topology leaf: every polygon quotient singular one-simplex has
a finite subdivision by pieces that lift to the closed disk, with
adjacent lifted endpoints related by `SideRel`.
-/
theorem polygon4g_quotient_path_finite_lift_subdivision
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) :
    Nonempty (Polygon4gQuotientPathFiniteLiftSubdivision g σ) := by
  -- Missing topology: compactness of the interval plus quotient charts
  -- admitting local disk lifts.
  sorry

/--
Singular-chain subdivision prism leaf for one-simplices in canonical
restricted-piece form.  The finite family of maps is exactly
`σ ∘ subSimplex i`; the wrapper below handles propositionally equal
families.
-/
theorem singular_one_simplex_subdivision_prism_homologous
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X))
    (n : ℕ) (_n_pos : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (_subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex) :
    ∃ subdivisionBoundary : SingularChainCoproduct X 2,
      (singularChainComplexZ X).d 2 1 subdivisionBoundary =
        (∑ i : Fin n,
          singularChainElement (σ.comp (subSimplex i))) -
            singularChainElement σ := by
  let domainCycle : SingularChainCoproduct (stdSimplex ℝ (Fin 2)) 1 :=
    (∑ i : Fin n, singularChainElement (subSimplex i)) -
      singularChainElement (ContinuousMap.id (stdSimplex ℝ (Fin 2)))
  have hdomainCycle :
      (singularChainComplexZ (stdSimplex ℝ (Fin 2))).d 1 0 domainCycle = 0 := by
    dsimp [domainCycle]
    exact subdivision_boundary_cycle n _n_pos subSimplex _subdivision_valid
  have hclass :
      singularH1ClassOfCycle (stdSimplex ℝ (Fin 2)) domainCycle hdomainCycle = 0 := by
    haveI : Subsingleton (singularH1 (stdSimplex ℝ (Fin 2))) :=
      singularH1_subsingleton_of_contractibleSpace
    exact Subsingleton.elim _ _
  obtain ⟨Bsc, hBsc⟩ :=
    singularH1ClassOfCycle_eq_zero_sc_boundary
      (stdSimplex ℝ (Fin 2)) domainCycle hdomainCycle hclass
  obtain ⟨Bdomain, hBdomain⟩ :=
    hurewicz_singularBoundary_eq_sc_f_early (stdSimplex ℝ (Fin 2)) Bsc
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom σ))
  refine ⟨ModuleCat.Hom.hom (F.f 2) Bdomain, ?_⟩
  have hcomm :
      ModuleCat.Hom.hom (F.f 1)
          ((singularChainComplexZ (stdSimplex ℝ (Fin 2))).d 2 1 Bdomain) =
        (singularChainComplexZ X).d 2 1
          (ModuleCat.Hom.hom (F.f 2) Bdomain) := by
    rw [← ModuleCat.comp_apply
      ((singularChainComplexZ (stdSimplex ℝ (Fin 2))).d 2 1) (F.f 1)]
    rw [← ModuleCat.comp_apply (F.f 2) ((singularChainComplexZ X).d 2 1)]
    exact congrArg
      (fun φ => ModuleCat.Hom.hom φ Bdomain)
      (F.comm 2 1).symm
  rw [← hcomm, ← hBdomain, hBsc]
  dsimp [domainCycle]
  rw [map_sub, map_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    exact singularChainElement_map σ 1 (subSimplex i)
  · simpa using
      singularChainElement_map σ 1
        (ContinuousMap.id (stdSimplex ℝ (Fin 2)))

/--
Singular-chain subdivision algebra for one-simplices.  Given the
projected pieces of a finite subdivision, their sum is homologous to
the original singular simplex by an explicit singular two-chain.
-/
theorem singular_one_simplex_subdivision_homologous
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X))
    (n : ℕ) (_n_pos : 0 < n)
    (subSimplex : Fin n → C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 2)))
    (_subdivision_valid : SingularOneSimplexSubdivisionData n subSimplex)
    (τ : Fin n → C(stdSimplex ℝ (Fin 2), X))
    (_hτ : ∀ (i : Fin n) (s : stdSimplex ℝ (Fin 2)),
      τ i s = σ (subSimplex i s)) :
    ∃ subdivisionBoundary : SingularChainCoproduct X 2,
      (singularChainComplexZ X).d 2 1 subdivisionBoundary =
        (∑ i : Fin n, singularChainElement (τ i)) - singularChainElement σ := by
  obtain ⟨subdivisionBoundary, hsubdivision⟩ :=
    singular_one_simplex_subdivision_prism_homologous
      X σ n _n_pos subSimplex _subdivision_valid
  refine ⟨subdivisionBoundary, ?_⟩
  rw [hsubdivision]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  congr 1
  ext s
  exact (_hτ i s).symm

/--
A singular one-simplex in the quotient polygon admits a finite disk
lifting package.  This is the subdivision/lifting leaf of the polygon
spanning proof.
-/
theorem polygon4g_singularSimplex_subdivision_lifts_to_disk
    (g : ℕ) (σ : C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1))) :
    Nonempty (Polygon4gSingularSimplexDiskLiftData g σ) := by
  obtain ⟨lifted⟩ := polygon4g_quotient_path_finite_lift_subdivision g σ
  let projectedPiece : Fin lifted.n →
      C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1)) :=
    fun i => (polygon4gMkContinuousMap (g + 1)).comp (lifted.lift i)
  have hpiece :
      ∀ (i : Fin lifted.n) (s : stdSimplex ℝ (Fin 2)),
        projectedPiece i s = σ (lifted.subSimplex i s) := by
    intro i s
    exact lifted.projects_on_piece i s
  obtain ⟨subdivisionBoundary, hsubdivision⟩ :=
    singular_one_simplex_subdivision_homologous
      (Polygon4g (g + 1)) σ lifted.n lifted.n_pos
      lifted.subSimplex lifted.subdivision_valid projectedPiece hpiece
  refine ⟨{
    n := lifted.n
    n_pos := lifted.n_pos
    subSimplex := lifted.subSimplex
    subdivision_valid := lifted.subdivision_valid
    lift := lifted.lift
    projects_on_piece := lifted.projects_on_piece
    adjacent_endpoint_rel := lifted.adjacent_endpoint_rel
    subdividedChain :=
      ∑ i : Fin lifted.n,
        singularChainElement
          ((polygon4gMkContinuousMap (g + 1)).comp (lifted.lift i))
    subdividedChain_eq := rfl
    subdivisionBoundary := subdivisionBoundary
    subdivision_homology := ?_
  }⟩
  simpa [projectedPiece] using hsubdivision

/--
Endpoint repair data for two disk points identified in the polygon
quotient by `SideRel`.  The repair is a disk-side chain built from
partial boundary-side arcs.  Its projection is required to be homologous
to an edge-chain combination by an explicit singular 2-boundary, not
definitionally equal to full edge chains.
-/
structure Polygon4gEndpointRepairData
    (g : ℕ) (p q : DiskC)
    (_hrel : Polygon4g.SideRel (g + 1) p q) where
  coeff : Polygon4gAbelianization g
  diskRepairChain : SingularChainCoproduct DiskC 1
  projectedRepairChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  edgeChainBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  steps : List (Polygon4gBoundaryArcStep g)
  steps_connect : Polygon4gBoundaryArcListConnects g p q steps
  diskRepairChain_eq :
    diskRepairChain =
      (steps.map fun step =>
        step.orientation.sign • singularChainElement
          (step.path.comp stdSimplexToUnitInterval)).sum
  projectedRepairChain_eq :
    projectedRepairChain = polygon4gBoundaryArcStepsProjectedChain g steps
  diskRepairBoundary :
    (singularChainComplexZ DiskC).d 1 0 diskRepairChain =
      pointChain DiskC q - pointChain DiskC p
  projectedRepairBoundary :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
        projectedRepairChain =
      pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) q) -
        pointChain (Polygon4g (g + 1)) (Polygon4g.mk (g + 1) p)
  projectedRepair_homologous_edge :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 edgeChainBoundary =
      projectedRepairChain -
        ∑ e : Fin (2 * (g + 1)), coeff e • edgeChain g e

/--
The projected chain of one boundary-arc step is the singular-chain
pushforward of its disk chain along the polygon quotient map.
-/
theorem polygon4gBoundaryArcStep_projected_eq_chainMap
    (g : ℕ) (step : Polygon4gBoundaryArcStep g) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      (singularChainElement (step.path.comp stdSimplexToUnitInterval)) =
      polygon4gBoundaryArcStepProjectedChain g step := by
  exact singularChainElement_map (polygon4gMkContinuousMap (g + 1)) 1
    (step.path.comp stdSimplexToUnitInterval)

/--
The projected chain of a list of boundary-arc steps is the
singular-chain pushforward of the corresponding disk-side step chain.
-/
theorem polygon4gBoundaryArcSteps_projected_eq_chainMap
    (g : ℕ) (steps : List (Polygon4gBoundaryArcStep g)) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      ((steps.map fun step =>
        step.orientation.sign • singularChainElement
          (step.path.comp stdSimplexToUnitInterval)).sum) =
      polygon4gBoundaryArcStepsProjectedChain g steps := by
  induction steps with
  | nil =>
      simp [polygon4gBoundaryArcStepsProjectedChain]
  | cons step steps ih =>
      simp [polygon4gBoundaryArcStepsProjectedChain, ih,
        polygon4gBoundaryArcStep_projected_eq_chainMap]

/--
The projected repair chain stored in endpoint-repair data is the
singular-chain pushforward of the disk repair chain.
-/
theorem polygon4gEndpointRepair_projected_eq_chainMap
    (g : ℕ) (p q : DiskC)
    (hrel : Polygon4g.SideRel (g + 1) p q)
    (repair : Polygon4gEndpointRepairData g p q hrel) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      repair.diskRepairChain =
      repair.projectedRepairChain := by
  rw [repair.diskRepairChain_eq, repair.projectedRepairChain_eq]
  exact polygon4gBoundaryArcSteps_projected_eq_chainMap g repair.steps


/-- Edge-basis index corresponding to the `aᵢ` side pair. -/
def polygon4g_aPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    Fin (2 * (g + 1)) :=
  ⟨2 * i.val, by omega⟩

/-- Edge-basis index corresponding to the `bᵢ` side pair. -/
def polygon4g_bPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    Fin (2 * (g + 1)) :=
  ⟨2 * i.val + 1, by omega⟩

lemma edgeArcIdx_aPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    edgeArcIdx g (polygon4g_aPair_edgeIndex g i) = 4 * i.val := by
  unfold edgeArcIdx polygon4g_aPair_edgeIndex
  rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
  simp

lemma edgeArcIdx_bPair_edgeIndex (g : ℕ) (i : Fin (g + 1)) :
    edgeArcIdx g (polygon4g_bPair_edgeIndex g i) = 4 * i.val + 1 := by
  unfold edgeArcIdx polygon4g_bPair_edgeIndex
  have hdiv : (2 * i.val + 1) / 2 = i.val := by
    rw [show 2 * i.val + 1 = 1 + 2 * i.val by omega]
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    simp
  have hmod : (2 * i.val + 1) % 2 = 1 := by
    rw [show 2 * i.val + 1 = 1 + 2 * i.val by omega]
    rw [Nat.add_mul_mod_self_left]
  rw [hdiv, hmod]

/--
Local primitive side-strip repair.  This is the single geometric
leaf behind the `aᵢ` and `bᵢ` generator repairs: for one canonical
edge basis arc and its opposite paired side, build the finite boundary
arc repair and the side-strip two-chain relating its projection to the
edge generator.
-/
theorem polygon4g_partial_side_arc_homologous_to_edge_chain
    (g : ℕ) (e : Fin (2 * (g + 1))) (sideArc : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hside : edgeArcIdx g e = sideArc)
    (hrel : Polygon4g.SideRel (g + 1)
      (boundaryParam (g + 1) sideArc t)
      (boundaryParam (g + 1) (sideArc + 2) (1 - t))) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) sideArc t)
      (boundaryParam (g + 1) (sideArc + 2) (1 - t))
      hrel) := by
  -- Missing primitive side-strip geometry: build the partial boundary
  -- arc chain from `sideArc` through the adjacent edge to `sideArc + 2`,
  -- then construct the projected side-strip two-chain homologous to
  -- `edgeChain g e`.  This lemma is local to one edge and interval
  -- parameter; it contains no arbitrary cycles or Hurewicz spanning data.
  sorry

/-- Primitive endpoint repair for one `aᵢ` side-pairing generator. -/
theorem polygon4g_endpoint_pair_repaired_by_aPair
    (g : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) (4 * i.val) t)
      (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val) t)
        (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
        (Polygon4g.SideGen.a_pair i t ht))) := by
  simpa [edgeArcIdx_aPair_edgeIndex] using
    polygon4g_partial_side_arc_homologous_to_edge_chain
      g (polygon4g_aPair_edgeIndex g i) (4 * i.val) t ht
      (edgeArcIdx_aPair_edgeIndex g i)
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val) t)
        (boundaryParam (g + 1) (4 * i.val + 2) (1 - t))
        (Polygon4g.SideGen.a_pair i t ht))

/-- Primitive endpoint repair for one `bᵢ` side-pairing generator. -/
theorem polygon4g_endpoint_pair_repaired_by_bPair
    (g : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Nonempty (Polygon4gEndpointRepairData g
      (boundaryParam (g + 1) (4 * i.val + 1) t)
      (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val + 1) t)
        (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
        (Polygon4g.SideGen.b_pair i t ht))) := by
  simpa [edgeArcIdx_bPair_edgeIndex] using
    polygon4g_partial_side_arc_homologous_to_edge_chain
      g (polygon4g_bPair_edgeIndex g i) (4 * i.val + 1) t ht
      (edgeArcIdx_bPair_edgeIndex g i)
      (Relation.EqvGen.rel
        (boundaryParam (g + 1) (4 * i.val + 1) t)
        (boundaryParam (g + 1) (4 * i.val + 3) (1 - t))
        (Polygon4g.SideGen.b_pair i t ht))

/--
Primitive endpoint repair for one side-pairing generator, assembled
from the two explicit `aᵢ` and `bᵢ` generator cases.
-/
theorem polygon4g_endpoint_pair_repaired_by_sideGen
    (g : ℕ) (p q : DiskC)
    (hgen : Polygon4g.SideGen (g + 1) p q) :
    Nonempty (Polygon4gEndpointRepairData g p q
      (Relation.EqvGen.rel p q hgen)) := by
  cases hgen with
  | a_pair i t ht =>
      exact polygon4g_endpoint_pair_repaired_by_aPair g i t ht
  | b_pair i t ht =>
      exact polygon4g_endpoint_pair_repaired_by_bPair g i t ht


/--
Disk contractibility package, in the homology-level form needed by
the polygon projection step: every singular one-cycle in `DiskC` has
zero `H₁` class.
-/
theorem diskC_singular_one_cycle_homologyClass_eq_zero
    (z : SingularChainCoproduct DiskC 1)
    (hz : (singularChainComplexZ DiskC).d 1 0 z = 0) :
    singularH1ClassOfCycle DiskC z hz = 0 := by
  haveI : Subsingleton (singularH1 DiskC) :=
    singularH1_subsingleton_of_contractibleSpace
  exact Subsingleton.elim _ _

/--
The homology class of the i-th edge cycle in
`singularH1 (Polygon4g (g+1))`.
-/
noncomputable def edgeHomologyClass (g : ℕ) (i : Fin (2 * (g + 1))) :
    singularH1 (Polygon4g (g + 1)) :=
  ((forget₂ (ModuleCat ℤ) Ab).map
      ((Polygon4gSingularC1.polygonChainComplexOnGenus (g + 1)).homologyπ 1))
    ((Polygon4gSingularC1.polygonChainComplexOnGenus (g + 1)).cyclesMk
      (edgeChain g i) 0
      (ComplexShape.next_eq' _ (by simp [ComplexShape.down]))
      (by
        simpa [Polygon4gSingularC1.polygonChainComplexOnGenus]
          using edgeChain_isCycle g i))

/-- The image set of the edge homology classes. -/
noncomputable def edgeHomologyFamily (g : ℕ) :
    Fin (2 * (g + 1)) → singularH1 (Polygon4g (g + 1)) :=
  edgeHomologyClass g


/--
A finite integral combination of polygon edge chains is a singular
one-cycle.
-/
theorem edgeChain_sum_isCycle
    (g : ℕ) (v : Polygon4gAbelianization g) :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0
      (∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero (fun e _he => ?_)
  rw [map_zsmul, edgeChain_isCycle g e]
  exact zsmul_zero (v e)


/--
A finite-support presentation of a singular one-chain as an
integral sum of singular one-simplices.
-/
structure SingularOneChainSupportDecomposition
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1) where
  Simplex : Type
  simplexFintype : Fintype Simplex
  coeff : Simplex → ℤ
  simplex : Simplex → C(stdSimplex ℝ (Fin 2), X)
  chain_eq :
    z = ∑ s : Simplex, coeff s • singularChainElement (simplex s)

/--
Atomic finite-support algebra leaf: every coproduct singular
one-chain has a finite presentation by basis singular simplices.
-/
theorem singularChainCoproduct_sum_support_decomposition
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1) :
    Nonempty (SingularOneChainSupportDecomposition X z) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 1))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let dz : DirectSum I (fun i => (Z i : Type)) := iso.hom.hom z
  let f : I →₀ ℤ := (finsuppLEquivDirectSum ℤ ℤ I).symm dz
  let Simplex := {i : I // i ∈ f.support}
  refine ⟨{
    Simplex := Simplex
    simplexFintype := inferInstance
    coeff := fun s => f s.1
    simplex := fun s => (singularChainSimplexIndex X 1).symm s.1
    chain_eq := ?_
  }⟩
  change z =
    ∑ s : Simplex,
      f s.1 • singularChainElement ((singularChainSimplexIndex X 1).symm s.1)
  have hinj : Function.Injective iso.hom.hom := by
    intro a b h
    have h2 := congrArg iso.inv.hom h
    simpa [iso, Z] using h2
  apply hinj
  rw [map_sum]
  simp only [map_zsmul]
  have hdz : dz = (finsuppLEquivDirectSum ℤ ℤ I) f := by
    simp [f, dz]
  change dz =
    ∑ x : Simplex,
      f x.1 • iso.hom.hom
        (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))
  rw [hdz]
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hsum :
      (∑ x : Simplex,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    change
      (∑ x ∈ f.support.attach,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X 1).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)
    simpa [singularChainElement, I, Z, iso, hι] using
      (Finset.sum_attach f.support
        (fun i => f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)))
  rw [hsum]
  rw [← Finsupp.sum_of_support_subset f
    (show f.support ⊆ f.support from fun _ h => h)
    (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ))]
  · calc
      (finsuppLEquivDirectSum ℤ ℤ I) f
          = (finsuppLEquivDirectSum ℤ ℤ I)
              (f.sum fun i c => Finsupp.single i c) := by
              rw [Finsupp.sum_single]
      _ = f.sum
            (fun i c => (finsuppLEquivDirectSum ℤ ℤ I) (Finsupp.single i c)) := by
              simp [Finsupp.sum, map_sum]
      _ = f.sum
            (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)) := by
              apply Finsupp.sum_congr
              intro i _hi
              simpa [finsuppLEquivDirectSum_single] using
                ((DirectSum.lof ℤ I (fun _ : I => ℤ) i).map_smul (f i) (1 : ℤ))
  · intro i _hi
    simp

/--
A finite-support presentation of a singular `n`-chain as an integral
sum of singular `n`-simplices.
-/
structure SingularChainSupportDecomposition
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : SingularChainCoproduct X n) where
  Simplex : Type
  simplexFintype : Fintype Simplex
  coeff : Simplex → ℤ
  simplex : Simplex → C(stdSimplex ℝ (Fin (n + 1)), X)
  chain_eq :
    z = ∑ s : Simplex, coeff s • singularChainElement (simplex s)

/--
Atomic finite-support algebra leaf in arbitrary degree: every
coproduct singular chain has a finite presentation by basis singular
simplices.
-/
theorem singularChainCoproduct_sum_support_decomposition_degree
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : SingularChainCoproduct X n) :
    Nonempty (SingularChainSupportDecomposition X n z) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk n))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let dz : DirectSum I (fun i => (Z i : Type)) := iso.hom.hom z
  let f : I →₀ ℤ := (finsuppLEquivDirectSum ℤ ℤ I).symm dz
  let Simplex := {i : I // i ∈ f.support}
  refine ⟨{
    Simplex := Simplex
    simplexFintype := inferInstance
    coeff := fun s => f s.1
    simplex := fun s => (singularChainSimplexIndex X n).symm s.1
    chain_eq := ?_
  }⟩
  change z =
    ∑ s : Simplex,
      f s.1 • singularChainElement ((singularChainSimplexIndex X n).symm s.1)
  have hinj : Function.Injective iso.hom.hom := by
    intro a b h
    have h2 := congrArg iso.inv.hom h
    simpa [iso, Z] using h2
  apply hinj
  rw [map_sum]
  simp only [map_zsmul]
  have hdz : dz = (finsuppLEquivDirectSum ℤ ℤ I) f := by
    simp [f, dz]
  change dz =
    ∑ x : Simplex,
      f x.1 • iso.hom.hom
        (singularChainElement ((singularChainSimplexIndex X n).symm x.1))
  rw [hdz]
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hsum :
      (∑ x : Simplex,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X n).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    change
      (∑ x ∈ f.support.attach,
          f x.1 • iso.hom.hom
            (singularChainElement ((singularChainSimplexIndex X n).symm x.1))) =
        ∑ i ∈ f.support, f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)
    simpa [singularChainElement, I, Z, iso, hι] using
      (Finset.sum_attach f.support
        (fun i => f i • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)))
  rw [hsum]
  rw [← Finsupp.sum_of_support_subset f
    (show f.support ⊆ f.support from fun _ h => h)
    (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ))]
  · calc
      (finsuppLEquivDirectSum ℤ ℤ I) f
          = (finsuppLEquivDirectSum ℤ ℤ I)
              (f.sum fun i c => Finsupp.single i c) := by
              rw [Finsupp.sum_single]
      _ = f.sum
            (fun i c => (finsuppLEquivDirectSum ℤ ℤ I) (Finsupp.single i c)) := by
              simp [Finsupp.sum, map_sum]
      _ = f.sum
            (fun i c => c • DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ)) := by
              apply Finsupp.sum_congr
              intro i _hi
              simpa [finsuppLEquivDirectSum_single] using
                ((DirectSum.lof ℤ I (fun _ : I => ℤ) i).map_smul (f i) (1 : ℤ))
  · intro i _hi
    simp

/--
Lift data summed over a finite-support presentation of a polygon
singular one-chain.  This is still before endpoint repair: it only says
each support simplex has a subdivision/lift package and records the
summed lifted disk chain and projected subdivided chain.
-/
structure Polygon4gLiftedSupportData
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z) where
  simplexLift :
    ∀ s : decomp.Simplex,
      Polygon4gSingularSimplexDiskLiftData g (decomp.simplex s)
  liftedDiskChain : SingularChainCoproduct DiskC 1
  liftedDiskChain_eq :
    liftedDiskChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s •
          (∑ i : Fin ((simplexLift s).n),
            singularChainElement ((simplexLift s).lift i)))
  projectedSubdivisionChain : SingularChainCoproduct (Polygon4g (g + 1)) 1
  projectedSubdivisionChain_eq :
    projectedSubdivisionChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s • (simplexLift s).subdividedChain)
  subdivisionBoundary : SingularChainCoproduct (Polygon4g (g + 1)) 2
  subdivision_homology :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 subdivisionBoundary =
      projectedSubdivisionChain - z

/--
Atomic lift-summation leaf: apply simplex subdivision/lift data over
the finite support of a singular chain and sum the resulting chain
relations.
-/
theorem polygon4g_lift_data_sum_projects_to_subdivision_chain
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z) :
    Nonempty (Polygon4gLiftedSupportData g z decomp) := by
  classical
  let simplexLift :
      ∀ s : decomp.Simplex,
        Polygon4gSingularSimplexDiskLiftData g (decomp.simplex s) :=
    fun s => Classical.choice
      (polygon4g_singularSimplex_subdivision_lifts_to_disk g (decomp.simplex s))
  let liftedDiskChain : SingularChainCoproduct DiskC 1 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s •
        (∑ i : Fin ((simplexLift s).n),
          singularChainElement ((simplexLift s).lift i)))
  let projectedSubdivisionChain :
      SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s • (simplexLift s).subdividedChain)
  let subdivisionBoundary :
      SingularChainCoproduct (Polygon4g (g + 1)) 2 :=
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s => decomp.coeff s • (simplexLift s).subdivisionBoundary)
  refine ⟨{
    simplexLift := simplexLift
    liftedDiskChain := liftedDiskChain
    liftedDiskChain_eq := rfl
    projectedSubdivisionChain := projectedSubdivisionChain
    projectedSubdivisionChain_eq := rfl
    subdivisionBoundary := subdivisionBoundary
    subdivision_homology := ?_
  }⟩
  letI := decomp.simplexFintype
  dsimp [subdivisionBoundary, projectedSubdivisionChain]
  rw [map_sum]
  simp only [map_zsmul]
  calc
    ∑ s : decomp.Simplex,
        decomp.coeff s •
          (singularChainComplexZ (Polygon4g (g + 1))).d 2 1
            (simplexLift s).subdivisionBoundary
        =
      ∑ s : decomp.Simplex,
        decomp.coeff s •
          ((simplexLift s).subdividedChain -
            singularChainElement (decomp.simplex s)) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          exact congrArg (fun c => decomp.coeff s • c)
            (simplexLift s).subdivision_homology
    _ =
      (∑ s : decomp.Simplex, decomp.coeff s • (simplexLift s).subdividedChain) -
        ∑ s : decomp.Simplex,
          decomp.coeff s • singularChainElement (decomp.simplex s) := by
          simp [zsmul_sub, Finset.sum_sub_distrib]
    _ =
      (∑ s : decomp.Simplex, decomp.coeff s • (simplexLift s).subdividedChain) -
        z := by
          exact congrArg
            (fun t =>
              (∑ s : decomp.Simplex,
                decomp.coeff s • (simplexLift s).subdividedChain) - t)
            decomp.chain_eq.symm

/--
The projected subdivision chain is exactly the degree-one singular
chain pushforward of the summed lifted disk chain.
-/
theorem polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
        lifted.liftedDiskChain =
      lifted.projectedSubdivisionChain := by
  classical
  letI := decomp.simplexFintype
  rw [lifted.liftedDiskChain_eq, lifted.projectedSubdivisionChain_eq]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [map_zsmul]
  congr 1
  rw [map_sum, (lifted.simplexLift s).subdividedChain_eq]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact singularChainElement_map (polygon4gMkContinuousMap (g + 1)) 1
    ((lifted.simplexLift s).lift i)

/--
Endpoint pairs extracted from the boundary of the summed lifted
chain.  Each pair is a specific `SideRel` pair and carries the endpoint
repair data for that relation.
-/
structure Polygon4gCycleEndpointPairFamily
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint : Pair → DiskC
  rightEndpoint : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint pair) (rightEndpoint pair)
  repair :
    ∀ pair : Pair,
      Polygon4gEndpointRepairData g (leftEndpoint pair) (rightEndpoint pair)
        (endpointRel pair)
  lifted_boundary_eq_pairs :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint pair) -
            pointChain DiskC (leftEndpoint pair))

/--
Endpoint relation pairs extracted from the boundary of the summed
lifted chain, before endpoint repairs are attached.
-/
structure Polygon4gCycleEndpointRelPairFamily
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint : Pair → DiskC
  rightEndpoint : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint pair) (rightEndpoint pair)
  lifted_boundary_eq_pairs :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint pair) -
            pointChain DiskC (leftEndpoint pair))

/--
The projected boundary of the lifted disk chain vanishes in the
polygon quotient.  This is the chain-map/naturality part of endpoint
pair extraction, before finite endpoint pairing is applied.
-/
structure Polygon4gLiftedBoundaryProjectsToZero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  projected_lifted_boundary_zero :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 0)
        ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) = 0

/--
The boundary of the summed lifted disk chain expanded into the
finite list of endpoints of the lifted subdivided one-simplices.
-/
structure Polygon4gLiftedEndpointBoundaryExpansion
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  lifted_boundary_eq_endpoint_sum :
    (singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain =
      (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
        (fun s => decomp.coeff s •
          ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
            (fun i =>
            pointChain DiskC ((lifted.simplexLift s).lift i (stdSimplexVertex 1)) -
              pointChain DiskC
                ((lifted.simplexLift s).lift i (stdSimplexVertex 0)))))

/--
The quotient image of the expanded lifted endpoint boundary is zero.
This is still before the finite matching/permutation argument.
-/
structure Polygon4gProjectedEndpointBoundaryCancellation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) where
  projected_endpoint_sum_zero :
    (@Finset.univ decomp.Simplex decomp.simplexFintype).sum
      (fun s =>
        decomp.coeff s •
          (((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
              (fun i =>
                pointChain (Polygon4g (g + 1))
                  (Polygon4g.mk (g + 1)
                    ((lifted.simplexLift s).lift i (stdSimplexVertex 1))))) -
            ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
              (fun i =>
                pointChain (Polygon4g (g + 1))
                  (Polygon4g.mk (g + 1)
                    ((lifted.simplexLift s).lift i (stdSimplexVertex 0))))))) = 0

/-- Degree-zero singular chains transported to the concrete Finsupp presentation. -/
noncomputable def singularZeroChainFinsupp
    (X : Type) [TopologicalSpace X] :
    SingularChainCoproduct X 0 →+
      ((TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0)) →₀ ℤ) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  exact ((finsuppLEquivDirectSum ℤ ℤ I).symm.toAddMonoidHom).comp
    iso.hom.hom.toAddMonoidHom

/-- The Finsupp bridge sends a degree-zero singular generator to the corresponding unit vector. -/
theorem singularZeroChainFinsupp_singularChainElement
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 1), X)) :
    singularZeroChainFinsupp X
      (singularChainElement σ : SingularChainCoproduct X 0) =
      Finsupp.single (singularChainSimplexIndex X 0 σ) 1 := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let idx : I := singularChainSimplexIndex X 0 σ
  have hι :
      (ModuleCat.coprodIsoDirectSum Z).hom.hom
        ((Sigma.ι Z idx).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) idx (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z idx
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  change (finsuppLEquivDirectSum ℤ ℤ I).symm
      ((ModuleCat.coprodIsoDirectSum Z).hom.hom ((Sigma.ι Z idx).hom (1 : ℤ))) =
    Finsupp.single idx (1 : ℤ)
  rw [hι]
  exact finsuppLEquivDirectSum_symm_lof ℤ ℤ I idx (1 : ℤ)

/-- Specialization of the bridge generator computation to point zero-chains. -/
theorem singularZeroChainFinsupp_pointChain
    (X : Type) [TopologicalSpace X] (x : X) :
    singularZeroChainFinsupp X (pointChain X x) =
      Finsupp.single
        (singularChainSimplexIndex X 0 (pointSingularSimplex X x)) 1 := by
  exact singularZeroChainFinsupp_singularChainElement X (pointSingularSimplex X x)

/-- Every singular zero-simplex is determined by its unique vertex. -/
lemma zeroSimplex_eq_pointSingularSimplex
    (X : Type) [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 1), X)) :
    σ = pointSingularSimplex X (σ (stdSimplex.vertex (0 : Fin 1))) := by
  ext s
  have hs : s = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  simp [hs, pointSingularSimplex]

/-- The point recovered from a zero-simplex index maps back to that index. -/
theorem singularZeroChainFinsupp_pointChain_of_index
    (X : Type) [TopologicalSpace X]
    (i : (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0))) :
    singularZeroChainFinsupp X
      (pointChain X
        (((singularChainSimplexIndex X 0).symm i)
          (stdSimplex.vertex (0 : Fin 1)))) =
      Finsupp.single i 1 := by
  rw [singularZeroChainFinsupp_pointChain]
  have hσ := zeroSimplex_eq_pointSingularSimplex X
    ((singularChainSimplexIndex X 0).symm i)
  change Finsupp.single
      (singularChainSimplexIndex X 0
        (pointSingularSimplex X
          (((singularChainSimplexIndex X 0).symm i)
            (stdSimplex.vertex (0 : Fin 1))))) 1 =
    Finsupp.single i 1
  rw [← hσ]
  simp

/--
Functoriality of the degree-zero Finsupp presentation, parameterized by an
explicit finite support decomposition to keep elaboration concrete.
-/
theorem singularZeroChainFinsupp_map_of_decomposition
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (c : SingularChainCoproduct X 0)
    (decomp : SingularChainSupportDecomposition X 0 c) :
    singularZeroChainFinsupp Y
      (ModuleCat.Hom.hom
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0) c) =
    Finsupp.mapDomain
      (fun i =>
        singularChainSimplexIndex Y 0
          (f.comp ((singularChainSimplexIndex X 0).symm i)))
      (singularZeroChainFinsupp X c) := by
  classical
  letI := decomp.simplexFintype
  let IX := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0))
  let IY := (TopCat.toSSet.obj (TopCat.of Y)).obj (op (SimplexCategory.mk 0))
  let φ : IX → IY := fun i =>
    singularChainSimplexIndex Y 0
      (f.comp ((singularChainSimplexIndex X 0).symm i))
  let L : (IX →₀ ℤ) →ₗ[ℤ] (IY →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ φ
  have hterm (s : decomp.Simplex) :
      singularZeroChainFinsupp Y
        (ModuleCat.Hom.hom
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0)
          (singularChainElement (decomp.simplex s))) =
        L (singularZeroChainFinsupp X
          (singularChainElement (decomp.simplex s))) := by
    rw [singularChainElement_map]
    rw [singularZeroChainFinsupp_singularChainElement]
    rw [singularZeroChainFinsupp_singularChainElement]
    simp [L, φ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [decomp.chain_eq]
  calc
    singularZeroChainFinsupp Y
      (ModuleCat.Hom.hom
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0)
        (∑ s : decomp.Simplex,
          decomp.coeff s • singularChainElement (decomp.simplex s)))
        = ∑ s : decomp.Simplex,
            decomp.coeff s • singularZeroChainFinsupp Y
              (ModuleCat.Hom.hom
                ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
                  (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f 0)
                (singularChainElement (decomp.simplex s))) := by
          rw [map_sum]
          rw [map_sum]
          simp only [map_zsmul]
    _ = ∑ s : decomp.Simplex,
            decomp.coeff s • L (singularZeroChainFinsupp X
              (singularChainElement (decomp.simplex s))) := by
          exact Finset.sum_congr rfl (fun s _ => by rw [hterm])
    _ = L (∑ s : decomp.Simplex,
            decomp.coeff s • singularZeroChainFinsupp X
              (singularChainElement (decomp.simplex s))) := by
          rw [map_sum]
          simp only [map_zsmul]
    _ = Finsupp.mapDomain φ
          (singularZeroChainFinsupp X
            (∑ s : decomp.Simplex,
              decomp.coeff s • singularChainElement (decomp.simplex s))) := by
          have hxsum :
              singularZeroChainFinsupp X
                (∑ s : decomp.Simplex,
                  decomp.coeff s • singularChainElement (decomp.simplex s)) =
                ∑ s : decomp.Simplex,
                  decomp.coeff s • singularZeroChainFinsupp X
                    (singularChainElement (decomp.simplex s)) := by
            rw [map_sum]
            simp only [map_zsmul]
          rw [hxsum]
          rfl

/-- The Finsupp bridge is injective. -/
theorem singularZeroChainFinsupp_injective
    (X : Type) [TopologicalSpace X] :
    Function.Injective (singularZeroChainFinsupp X) := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of X)).obj (op (SimplexCategory.mk 0))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  intro c d h
  have hdir :
      iso.hom.hom c = iso.hom.hom d := by
    apply (finsuppLEquivDirectSum ℤ ℤ I).symm.injective
    simpa [singularZeroChainFinsupp, I, Z, iso] using h
  have hback := congrArg iso.inv.hom hdir
  simpa [iso, Z] using hback

/--
Subtracting one positive occurrence and one negative occurrence strictly
decreases the sum of absolute coefficients.
-/
lemma finsupp_signed_pair_sub_measure_lt
    {α : Type} [DecidableEq α] (x : α →₀ ℤ) {a b : α}
    (hab : a ≠ b)
    (ha : 0 < x a) (hb : x b < 0) :
    ((x - (Finsupp.single a (1 : ℤ) -
          Finsupp.single b (1 : ℤ))).support.sum
        (fun t => Int.natAbs
          ((x - (Finsupp.single a (1 : ℤ) -
            Finsupp.single b (1 : ℤ))) t))) <
      x.support.sum (fun t => Int.natAbs (x t)) := by
  classical
  let δ : α →₀ ℤ := Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)
  let y : α →₀ ℤ := x - δ
  let S : Finset α := insert a (insert b x.support)
  have hx_support : x.support ⊆ S := by intro t ht; simp [S, ht]
  have hy_support : y.support ⊆ S := by
    intro t ht
    by_contra hnot
    have hta : t ≠ a := by intro h; apply hnot; simp [S, h]
    have htb : t ≠ b := by intro h; apply hnot; simp [S, h]
    have htx : t ∉ x.support := by intro hxmem; apply hnot; simp [S, hxmem]
    have hxzero : x t = 0 := by simpa using (Finsupp.notMem_support_iff.mp htx)
    have hdzero : δ t = 0 := by simp [δ, hta, htb]
    have : y t = 0 := by simp [y, hxzero, hdzero]
    rw [Finsupp.mem_support_iff] at ht
    exact ht this
  have hx_sum :
      x.support.sum (fun t => Int.natAbs (x t)) =
        S.sum (fun t => Int.natAbs (x t)) := by
    exact Finset.sum_subset (s₁ := x.support) (s₂ := S)
      (f := fun t => Int.natAbs (x t)) hx_support (by
        intro t _ ht
        have : x t = 0 := by simpa using (Finsupp.notMem_support_iff.mp ht)
        simp [this])
  have hy_sum :
      y.support.sum (fun t => Int.natAbs (y t)) =
        S.sum (fun t => Int.natAbs (y t)) := by
    exact Finset.sum_subset (s₁ := y.support) (s₂ := S)
      (f := fun t => Int.natAbs (y t)) hy_support (by
        intro t _ ht
        have : y t = 0 := by simpa using (Finsupp.notMem_support_iff.mp ht)
        simp [this])
  have hyt (t : α) (hta : t ≠ a) (htb : t ≠ b) : y t = x t := by
    simp [y, δ, hta, htb]
  rw [hy_sum, hx_sum]
  have hle (t : α) (_ht : t ∈ S) : Int.natAbs (y t) ≤ Int.natAbs (x t) := by
    by_cases hta : t = a
    · subst t
      have hya : y a = x a - 1 := by simp [y, δ, hab]
      exact le_of_lt (Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega))
    · by_cases htb : t = b
      · subst t
        have hyb : y b = x b + 1 := by simp [y, δ, hab]
        exact le_of_lt (by
          simpa [Int.natAbs_neg] using
            Int.natAbs_lt_natAbs_of_nonneg_of_lt
              (show 0 ≤ -y b by omega)
              (show -y b < -x b by omega))
      · rw [hyt t hta htb]
  have hlt_exists : ∃ t ∈ S, Int.natAbs (y t) < Int.natAbs (x t) := by
    refine ⟨a, ?_, ?_⟩
    · simp [S]
    · have hya : y a = x a - 1 := by simp [y, δ, hab]
      exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
  exact Finset.sum_lt_sum hle hlt_exists

lemma finsupp_mapDomain_fiber_sum_zero
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (x : α →₀ ℤ) (hx : Finsupp.mapDomain f x = 0)
    (a : α) :
    (∑ b ∈ x.support.filter (fun b => f b = f a), x b) = 0 := by
  classical
  have h := congrArg (fun y : β →₀ ℤ => y (f a)) hx
  rw [Finsupp.mapDomain] at h
  simp [Finsupp.sum, Finset.sum_filter, eq_comm] at h ⊢
  simpa [Finsupp.single_apply, eq_comm] using h.symm

lemma finsupp_mapDomain_exists_negative_in_fiber
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (x : α →₀ ℤ) (hx : Finsupp.mapDomain f x = 0)
    {a : α} (ha : 0 < x a) :
    ∃ b ∈ x.support, f b = f a ∧ x b < 0 := by
  classical
  have hsum := finsupp_mapDomain_fiber_sum_zero f x hx a
  by_contra hneg
  push Not at hneg
  have h_nonneg : ∀ b ∈ x.support.filter (fun b => f b = f a), 0 ≤ x b := by
    intro b hb
    exact hneg b (Finset.mem_filter.mp hb).1 (by simpa using (Finset.mem_filter.mp hb).2)
  have ha_mem : a ∈ x.support.filter (fun b => f b = f a) := by
    rw [Finset.mem_filter]
    constructor
    · rw [Finsupp.mem_support_iff]; omega
    · rfl
  have hpos : 0 < (∑ b ∈ x.support.filter (fun b => f b = f a), x b) := by
    exact Finset.sum_pos' h_nonneg ⟨a, ha_mem, ha⟩
  omega

def FinsuppFiberKernelDecompAt
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (n : ℕ) : Prop :=
  ∀ x : α →₀ ℤ,
    x.support.sum (fun t => Int.natAbs (x t)) = n →
    Finsupp.mapDomain f x = 0 →
      ∃ (Pair : Type) (_ : Fintype Pair)
        (left right : Pair → α),
          (∀ p, f (left p) = f (right p)) ∧
            x =
              ∑ p : Pair,
                (Finsupp.single (right p) (1 : ℤ) -
                  Finsupp.single (left p) (1 : ℤ))

theorem finsupp_fiberKernelDecomp_strong_induction
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) :
    ∀ n, FinsuppFiberKernelDecompAt f n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hμ hx
      by_cases hxzero : x = 0
      · subst x
        refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ?_, ?_⟩
        · intro p; cases p
        · simp
      · have hsupp_ne : x.support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          exact hxzero ((Finsupp.support_eq_empty).mp h)
        obtain ⟨c, hc⟩ := hsupp_ne
        have hc_ne : x c ≠ 0 := by simpa [Finsupp.mem_support_iff] using hc
        have hc_pos_or_neg : 0 < x c ∨ x c < 0 := by omega
        obtain ⟨a, b, ha_pos, hb_neg, hfab, _ha_mem, _hb_mem⟩ : ∃ a b,
            0 < x a ∧ x b < 0 ∧ f a = f b ∧ a ∈ x.support ∧ b ∈ x.support := by
          cases hc_pos_or_neg with
          | inl hpos =>
              obtain ⟨b, hbmem, hfb, hbneg⟩ :=
                finsupp_mapDomain_exists_negative_in_fiber f x hx hpos
              exact ⟨c, b, hpos, hbneg, hfb.symm, hc, hbmem⟩
          | inr hneg =>
              have hmap_neg : Finsupp.mapDomain f (-x) = 0 := by
                have h := (Finsupp.mapDomain.addMonoidHom (M := ℤ) f).map_neg x
                change Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x at h
                rw [h, hx, neg_zero]
              have hpos_neg : 0 < (-x) c := by simp [hneg]
              obtain ⟨a, hamem_neg, hfa, haneg_neg⟩ :=
                finsupp_mapDomain_exists_negative_in_fiber f (-x) hmap_neg hpos_neg
              have hamem : a ∈ x.support := by
                simpa [Finsupp.mem_support_iff] using hamem_neg
              have hapos : 0 < x a := by
                change -x a < 0 at haneg_neg
                omega
              exact ⟨a, c, hapos, hneg, hfa, hamem, hc⟩
        have hab : a ≠ b := by
          intro h; subst b; omega
        let δ : α →₀ ℤ := Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)
        let y : α →₀ ℤ := x - δ
        have hδ_map : Finsupp.mapDomain f δ = 0 := by
          have h := (Finsupp.mapDomain.addMonoidHom (M := ℤ) f).map_sub
            (Finsupp.single a (1 : ℤ)) (Finsupp.single b (1 : ℤ))
          change Finsupp.mapDomain f (Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)) =
            Finsupp.mapDomain f (Finsupp.single a (1 : ℤ)) -
              Finsupp.mapDomain f (Finsupp.single b (1 : ℤ)) at h
          rw [h]
          simp [Finsupp.mapDomain_single, hfab]
        have hy_map : Finsupp.mapDomain f y = 0 := by
          have h := (Finsupp.mapDomain.addMonoidHom (M := ℤ) f).map_sub x δ
          change Finsupp.mapDomain f (x - δ) = Finsupp.mapDomain f x - Finsupp.mapDomain f δ at h
          rw [h, hx, hδ_map, sub_zero]
        have hy_measure : y.support.sum (fun t => Int.natAbs (y t)) < n := by
          rw [← hμ]
          exact finsupp_signed_pair_sub_measure_lt x hab ha_pos hb_neg
        obtain ⟨Pair, instPair, left, right, hrel, hsum⟩ :=
          ih (y.support.sum (fun t => Int.natAbs (y t))) hy_measure y rfl hy_map
        letI := instPair
        refine ⟨Option Pair, inferInstance,
          (fun p => match p with | none => b | some q => left q),
          (fun p => match p with | none => a | some q => right q),
          ?_, ?_⟩
        · intro p
          cases p with
          | none => exact hfab.symm
          | some q => exact hrel q
        · rw [Fintype.sum_option]
          change x = (Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)) +
            ∑ x : Pair, (Finsupp.single (right x) (1 : ℤ) - Finsupp.single (left x) (1 : ℤ))
          rw [← hsum]
          simp [y, δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem finsupp_mapDomain_zero_fiber_difference_decomposition
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (x : α →₀ ℤ)
    (hx : Finsupp.mapDomain f x = 0) :
    ∃ (Pair : Type) (_ : Fintype Pair)
      (left right : Pair → α),
        (∀ p, f (left p) = f (right p)) ∧
          x =
            ∑ p : Pair,
              (Finsupp.single (right p) (1 : ℤ) -
                Finsupp.single (left p) (1 : ℤ)) := by
  classical
  exact finsupp_fiberKernelDecomp_strong_induction f
    (x.support.sum (fun t => Int.natAbs (x t))) x rfl hx

/--
Pure finite-support endpoint pairing output.  This strips the
cycle-level names away from endpoint matching: a finite signed endpoint
sum in the disk whose projection vanishes is represented as endpoint
differences between disk points with equal quotient images, equivalently
`SideRel`-related endpoints.
-/
structure FiniteProjectedEndpointPairFamily
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (boundary : SingularChainCoproduct DiskC 0) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint' : Pair → DiskC
  rightEndpoint' : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint' pair) (rightEndpoint' pair)
  boundary_eq_pairs :
    boundary =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint' pair) -
            pointChain DiskC (leftEndpoint' pair))

/--
Finite endpoint matching data for a projected-zero endpoint sum.

This is the pure finite-support matching substrate: after expanding the
integer coefficients into endpoint occurrences, vanishing of the projected
endpoint sum pairs each disk endpoint with another endpoint having the same
quotient image, hence related by `Polygon4g.SideRel`.
-/
structure FiniteProjectedEndpointMatchingData
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC) where
  Pair : Type
  pairFintype : Fintype Pair
  leftEndpoint' : Pair → DiskC
  rightEndpoint' : Pair → DiskC
  endpointRel :
    ∀ pair : Pair,
      Polygon4g.SideRel (g + 1) (leftEndpoint' pair) (rightEndpoint' pair)
  endpoint_sum_eq_pairs :
    (@Finset.univ S inferInstance).sum
        (fun s => coeff s •
          ((@Finset.univ (I s) inferInstance).sum
            (fun i =>
              pointChain DiskC (rightEndpoint s i) -
                pointChain DiskC (leftEndpoint s i)))) =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (rightEndpoint' pair) -
            pointChain DiskC (leftEndpoint' pair))

/--
Architectural finite-support matching provider.

Given a finite signed endpoint sum whose quotient projection vanishes,
construct matched disk endpoints whose differences realize the original
disk endpoint sum. This is the finite free-abelian bookkeeping leaf
behind endpoint repair; the surrounding theorem only substitutes an
arbitrary `boundary` known to equal this endpoint sum.
-/
theorem finite_projected_endpoint_matching_data
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (_projected_endpoint_sum_zero :
      (@Finset.univ S inferInstance).sum
        (fun s =>
          coeff s •
            (((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (rightEndpoint s i)))) -
              ((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (leftEndpoint s i)))))) = 0) :
    Nonempty
      (FiniteProjectedEndpointMatchingData
        g S I coeff leftEndpoint rightEndpoint) := by
  classical
  let endpointChain : SingularChainCoproduct DiskC 0 :=
    (@Finset.univ S inferInstance).sum
      (fun s => coeff s •
        ((@Finset.univ (I s) inferInstance).sum
          (fun i =>
            pointChain DiskC (rightEndpoint s i) -
              pointChain DiskC (leftEndpoint s i))))
  let Q := (TopCat.toSSet.obj (TopCat.of (Polygon4g (g + 1)))).obj (op (SimplexCategory.mk 0))
  let D := (TopCat.toSSet.obj (TopCat.of DiskC)).obj (op (SimplexCategory.mk 0))
  let projectIdx : D → Q := fun i =>
    singularChainSimplexIndex (Polygon4g (g + 1)) 0
      ((polygon4gMkContinuousMap (g + 1)).comp
        ((singularChainSimplexIndex DiskC 0).symm i))
  let endpointFinsupp : D →₀ ℤ := singularZeroChainFinsupp DiskC endpointChain
  obtain ⟨decomp⟩ :=
    singularChainCoproduct_sum_support_decomposition_degree DiskC 0 endpointChain
  have hprojected_chain :
      ModuleCat.Hom.hom
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 0)
        endpointChain = 0 := by
    change
      ModuleCat.Hom.hom
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 0)
        ((@Finset.univ S inferInstance).sum
          (fun s => coeff s •
            ((@Finset.univ (I s) inferInstance).sum
              (fun i =>
                pointChain DiskC (rightEndpoint s i) -
                  pointChain DiskC (leftEndpoint s i))))) = 0
    simpa [pointChain_map, polygon4gMkContinuousMap, Finset.sum_sub_distrib]
      using _projected_endpoint_sum_zero
  have hkernel : Finsupp.mapDomain projectIdx endpointFinsupp = 0 := by
    have hbridge :=
      singularZeroChainFinsupp_map_of_decomposition
        (polygon4gMkContinuousMap (g + 1)) endpointChain decomp
    rw [hprojected_chain, map_zero] at hbridge
    simpa [endpointFinsupp, projectIdx, D, Q] using hbridge.symm
  obtain ⟨Pair, pairFintype, leftIdx, rightIdx, hidx, hsum⟩ :=
    finsupp_mapDomain_zero_fiber_difference_decomposition projectIdx endpointFinsupp hkernel
  letI := pairFintype
  let pointOfIdx : D → DiskC := fun i =>
    ((singularChainSimplexIndex DiskC 0).symm i)
      (stdSimplex.vertex (0 : Fin 1))
  refine ⟨{
    Pair := Pair
    pairFintype := pairFintype
    leftEndpoint' := fun pair => pointOfIdx (leftIdx pair)
    rightEndpoint' := fun pair => pointOfIdx (rightIdx pair)
    endpointRel := ?_
    endpoint_sum_eq_pairs := ?_
  }⟩
  · intro pair
    have hsimplex := congrArg
      (fun i : Q => (singularChainSimplexIndex (Polygon4g (g + 1)) 0).symm i)
      (hidx pair)
    change
      (polygon4gMkContinuousMap (g + 1)).comp
          ((singularChainSimplexIndex DiskC 0).symm (leftIdx pair)) =
        (polygon4gMkContinuousMap (g + 1)).comp
          ((singularChainSimplexIndex DiskC 0).symm (rightIdx pair)) at hsimplex
    have hmk :
        Polygon4g.mk (g + 1) (pointOfIdx (leftIdx pair)) =
          Polygon4g.mk (g + 1) (pointOfIdx (rightIdx pair)) := by
      simpa [pointOfIdx, polygon4gMkContinuousMap] using
        congrArg
          (fun σ : C(stdSimplex ℝ (Fin 1), Polygon4g (g + 1)) =>
            σ (stdSimplex.vertex (0 : Fin 1)))
          hsimplex
    exact ((Polygon4g.mk_eq_mk_iff (g + 1)
      (pointOfIdx (leftIdx pair)) (pointOfIdx (rightIdx pair))).mp hmk)
  · change endpointChain =
      (@Finset.univ Pair pairFintype).sum
        (fun pair =>
          pointChain DiskC (pointOfIdx (rightIdx pair)) -
            pointChain DiskC (pointOfIdx (leftIdx pair)))
    apply singularZeroChainFinsupp_injective DiskC
    have hpair_finsupp :
        singularZeroChainFinsupp DiskC
          ((@Finset.univ Pair pairFintype).sum
            (fun pair =>
              pointChain DiskC (pointOfIdx (rightIdx pair)) -
                pointChain DiskC (pointOfIdx (leftIdx pair)))) =
        (@Finset.univ Pair pairFintype).sum
          (fun pair =>
            Finsupp.single (rightIdx pair) (1 : ℤ) -
              Finsupp.single (leftIdx pair) (1 : ℤ)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro pair _hpair
      rw [map_sub]
      rw [singularZeroChainFinsupp_pointChain_of_index]
      rw [singularZeroChainFinsupp_pointChain_of_index]
    change singularZeroChainFinsupp DiskC endpointChain =
      singularZeroChainFinsupp DiskC
        ((@Finset.univ Pair pairFintype).sum
          (fun pair =>
            pointChain DiskC (pointOfIdx (rightIdx pair)) -
              pointChain DiskC (pointOfIdx (leftIdx pair))))
    rw [hpair_finsupp]
    exact hsum

/--
Finite-support quotient bookkeeping provider.  This is the exact
remaining algebraic leaf below cycle-level endpoint extraction: from a
finite signed endpoint expansion and vanishing of its quotient image,
construct a finite family of matched endpoint differences.
-/
theorem finite_projected_endpoint_sum_zero_pairing
    (g : ℕ) (S : Type) [Fintype S]
    (I : S → Type) [∀ s, Fintype (I s)]
    (coeff : S → ℤ)
    (leftEndpoint rightEndpoint : ∀ s, I s → DiskC)
    (boundary : SingularChainCoproduct DiskC 0)
    (_boundary_eq_endpoint_sum :
      boundary =
        (@Finset.univ S inferInstance).sum
          (fun s => coeff s •
            ((@Finset.univ (I s) inferInstance).sum
              (fun i =>
                pointChain DiskC (rightEndpoint s i) -
                  pointChain DiskC (leftEndpoint s i)))))
    (_projected_endpoint_sum_zero :
      (@Finset.univ S inferInstance).sum
        (fun s =>
          coeff s •
            (((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (rightEndpoint s i)))) -
              ((@Finset.univ (I s) inferInstance).sum
                (fun i =>
                  pointChain (Polygon4g (g + 1))
                    (Polygon4g.mk (g + 1) (leftEndpoint s i)))))) = 0) :
    Nonempty
      (FiniteProjectedEndpointPairFamily g S I coeff leftEndpoint rightEndpoint
        boundary) := by
  obtain ⟨pairs⟩ :=
    finite_projected_endpoint_matching_data
      g S I coeff leftEndpoint rightEndpoint _projected_endpoint_sum_zero
  exact ⟨{
    Pair := pairs.Pair
    pairFintype := pairs.pairFintype
    leftEndpoint' := pairs.leftEndpoint'
    rightEndpoint' := pairs.rightEndpoint'
    endpointRel := pairs.endpointRel
    boundary_eq_pairs := by
      rw [_boundary_eq_endpoint_sum, pairs.endpoint_sum_eq_pairs]
  }⟩

/--
Chain-boundary expansion part of endpoint extraction: no quotient
pairing is involved here, only finite-sum algebra and the boundary
formula for singular one-simplices.
-/
theorem polygon4g_lifted_endpoint_boundary_expansion
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted := by
  classical
  refine ⟨?_⟩
  rw [lifted.liftedDiskChain_eq, map_sum]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [map_zsmul, map_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact singularChainElement_boundary_one_simplex DiskC
    ((lifted.simplexLift s).lift i)

/--
Project the expanded lifted endpoint boundary to the polygon
quotient and use the chain-map zero result.
-/
theorem polygon4g_projected_endpoint_boundary_cancellation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (projectedZero :
      Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted)
    (endpointExpansion :
      Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted) :
    Polygon4gProjectedEndpointBoundaryCancellation g z hz decomp lifted := by
  classical
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  have hmap :=
    congrArg (fun c => ModuleCat.Hom.hom (F.f 0) c)
      endpointExpansion.lifted_boundary_eq_endpoint_sum
  have hzero :
      ModuleCat.Hom.hom (F.f 0)
        ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) = 0 := by
    simpa [F] using projectedZero.projected_lifted_boundary_zero
  have hmap' :
      ModuleCat.Hom.hom (F.f 0)
          ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) =
        ModuleCat.Hom.hom (F.f 0)
          ((@Finset.univ decomp.Simplex decomp.simplexFintype).sum
            (fun s => decomp.coeff s •
              ((@Finset.univ (Fin ((lifted.simplexLift s).n)) inferInstance).sum
                (fun i =>
                  pointChain DiskC
                      ((lifted.simplexLift s).lift i (stdSimplexVertex 1)) -
                    pointChain DiskC
                      ((lifted.simplexLift s).lift i (stdSimplexVertex 0)))))) := by
    simpa using hmap
  rw [hzero] at hmap'
  rw [map_sum] at hmap'
  simp only [map_zsmul] at hmap'
  simp [F, pointChain_map] at hmap'
  exact ⟨hmap'.symm⟩

/--
Chain-map part of endpoint extraction: use the projected cycle
condition and subdivision homology to show the projected lifted boundary
is zero.
-/
theorem polygon4g_lifted_boundary_projects_to_zero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Nonempty (Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted) := by
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  let K := singularChainComplexZ (Polygon4g (g + 1))
  have hcomm :
      ModuleCat.Hom.hom (F.f 0)
          ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain) =
        K.d 1 0 (ModuleCat.Hom.hom (F.f 1) lifted.liftedDiskChain) := by
    rw [← ModuleCat.comp_apply ((singularChainComplexZ DiskC).d 1 0) (F.f 0)]
    rw [← ModuleCat.comp_apply (F.f 1) (K.d 1 0)]
    exact congrArg
      (fun φ : (singularChainComplexZ DiskC).X 1 ⟶ K.X 0 =>
        ModuleCat.Hom.hom φ lifted.liftedDiskChain)
      (F.comm 1 0).symm
  have hproj :
      ModuleCat.Hom.hom (F.f 1) lifted.liftedDiskChain =
        lifted.projectedSubdivisionChain := by
    simpa [F] using
      polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain
        g z decomp lifted
  have hboundary_projected :
      K.d 1 0 lifted.projectedSubdivisionChain = 0 := by
    have hdd :
        K.d 1 0 (K.d 2 1 lifted.subdivisionBoundary) = 0 := by
      rw [← ModuleCat.comp_apply (K.d 2 1) (K.d 1 0)]
      exact congrArg
        (fun φ : K.X 2 ⟶ K.X 0 =>
          ModuleCat.Hom.hom φ lifted.subdivisionBoundary)
        (HomologicalComplex.d_comp_d K 2 1 0)
    have hsub := congrArg (fun c => K.d 1 0 c) lifted.subdivision_homology
    change K.d 1 0 (K.d 2 1 lifted.subdivisionBoundary) =
      K.d 1 0 (lifted.projectedSubdivisionChain - z) at hsub
    rw [hdd, map_sub, hz, sub_zero] at hsub
    exact hsub.symm
  refine ⟨{ projected_lifted_boundary_zero := ?_ }⟩
  rw [hcomm, hproj, hboundary_projected]

/--
Finite endpoint-pairing leaf: once the projected boundary of a
finite disk endpoint chain is zero, pair the disk endpoints whose
projections agree, and convert those equal projections to `SideRel`.
-/
theorem finite_projected_endpoint_boundary_zero_pairs
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (_projectedZero :
      Polygon4gLiftedBoundaryProjectsToZero g z hz decomp lifted)
    (_endpointExpansion :
      Polygon4gLiftedEndpointBoundaryExpansion g z decomp lifted)
    (_projectedEndpointCancellation :
      Polygon4gProjectedEndpointBoundaryCancellation g z hz decomp lifted) :
    Nonempty (Polygon4gCycleEndpointRelPairFamily g z hz decomp lifted) := by
  classical
  letI := decomp.simplexFintype
  let I : decomp.Simplex → Type :=
    fun s => Fin ((lifted.simplexLift s).n)
  let leftEndpoint : ∀ s, I s → DiskC :=
    fun s i => (lifted.simplexLift s).lift i (stdSimplexVertex 0)
  let rightEndpoint : ∀ s, I s → DiskC :=
    fun s i => (lifted.simplexLift s).lift i (stdSimplexVertex 1)
  obtain ⟨pairs⟩ :=
    finite_projected_endpoint_sum_zero_pairing
      g decomp.Simplex I decomp.coeff leftEndpoint rightEndpoint
      ((singularChainComplexZ DiskC).d 1 0 lifted.liftedDiskChain)
      (by
        simpa [I, leftEndpoint, rightEndpoint] using
          _endpointExpansion.lifted_boundary_eq_endpoint_sum)
      (by
        simpa [I, leftEndpoint, rightEndpoint] using
          _projectedEndpointCancellation.projected_endpoint_sum_zero)
  exact ⟨{
    Pair := pairs.Pair
    pairFintype := pairs.pairFintype
    leftEndpoint := pairs.leftEndpoint'
    rightEndpoint := pairs.rightEndpoint'
    endpointRel := pairs.endpointRel
    lifted_boundary_eq_pairs := pairs.boundary_eq_pairs
  }⟩

/--
Atomic endpoint-pair extraction leaf: the polygon cycle condition
forces the boundary of the lifted disk chain to be a finite sum of
`SideRel` endpoint pairs.  Endpoint repairs are attached separately.
-/
theorem polygon4g_cycle_endpoint_rel_pairs_from_boundary_zero
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp) :
    Nonempty (Polygon4gCycleEndpointRelPairFamily g z hz decomp lifted) := by
  obtain ⟨projectedZero⟩ :=
    polygon4g_lifted_boundary_projects_to_zero g z hz decomp lifted
  let endpointExpansion :=
    polygon4g_lifted_endpoint_boundary_expansion g z decomp lifted
  let projectedEndpointCancellation :=
    polygon4g_projected_endpoint_boundary_cancellation
      g z hz decomp lifted projectedZero endpointExpansion
  exact finite_projected_endpoint_boundary_zero_pairs
    g z hz decomp lifted projectedZero endpointExpansion
      projectedEndpointCancellation


/--
The chain-algebra output of summing a finite family of endpoint
repairs.  This is separated from the final homology statement so the
remaining obstruction, if any, is only the passage from explicit
chain-boundary relations to equality in `H₁`.
-/
structure Polygon4gRepairSumAlgebraData
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted) where
  edgeCoeffs : Polygon4gAbelianization g
  diskRepairSum : SingularChainCoproduct DiskC 1
  diskCycle : SingularChainCoproduct DiskC 1
  diskCycle_eq : diskCycle = lifted.liftedDiskChain - diskRepairSum
  diskCycle_isCycle : (singularChainComplexZ DiskC).d 1 0 diskCycle = 0
  projectedRepairSum : SingularChainCoproduct (Polygon4g (g + 1)) 1
  projectedRepairSum_eq_chainMap_diskRepairSum :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      diskRepairSum =
      projectedRepairSum
  projectedRepairBoundary :
    (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 projectedRepairSum =
      (@Finset.univ pairs.Pair pairs.pairFintype).sum
        (fun pair =>
          pointChain (Polygon4g (g + 1))
              (Polygon4g.mk (g + 1) (pairs.rightEndpoint pair)) -
            pointChain (Polygon4g (g + 1))
              (Polygon4g.mk (g + 1) (pairs.leftEndpoint pair)))
  edgeChainBoundarySum : SingularChainCoproduct (Polygon4g (g + 1)) 2
  projectedRepair_homologous_edge :
    (singularChainComplexZ (Polygon4g (g + 1))).d 2 1 edgeChainBoundarySum =
      projectedRepairSum -
        ∑ e : Fin (2 * (g + 1)), edgeCoeffs e • edgeChain g e


/--
The quotient-map pushforward of the repaired disk cycle is the
projected lifted subdivision chain minus the projected repair chain.
-/
theorem polygon4g_repair_sum_diskCycle_chainMap_eq
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted)
    (algebra : Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs) :
    ModuleCat.Hom.hom
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (polygon4gMkContinuousMap (g + 1)))).f 1)
      algebra.diskCycle =
      lifted.projectedSubdivisionChain - algebra.projectedRepairSum := by
  rw [algebra.diskCycle_eq, map_sub,
    polygon4g_projectedSubdivisionChain_eq_chainMap_liftedDiskChain g z decomp lifted,
    algebra.projectedRepairSum_eq_chainMap_diskRepairSum]

/--
Narrow remaining projection/naturality bridge for the repair-sum
package.  It no longer mentions the edge-basis map: it only says that
the quotient-map image of the repaired disk cycle, together with the
explicit repaired edge-chain cycle, represents the original polygon
cycle.
-/
theorem polygon4g_repair_sum_projected_diskCycle_relation
    (g : ℕ) (z : SingularChainCoproduct (Polygon4g (g + 1)) 1)
    (hz : (singularChainComplexZ (Polygon4g (g + 1))).d 1 0 z = 0)
    (decomp : SingularOneChainSupportDecomposition (Polygon4g (g + 1)) z)
    (lifted : Polygon4gLiftedSupportData g z decomp)
    (pairs : Polygon4gCycleEndpointPairFamily g z hz decomp lifted)
    (algebra : Polygon4gRepairSumAlgebraData g z hz decomp lifted pairs) :
    singularH1ClassOfCycle (Polygon4g (g + 1)) z hz =
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
        (singularH1ClassOfCycle DiskC algebra.diskCycle algebra.diskCycle_isCycle) +
        singularH1ClassOfCycle (Polygon4g (g + 1))
          (∑ e : Fin (2 * (g + 1)), algebra.edgeCoeffs e • edgeChain g e)
          (edgeChain_sum_isCycle g algebra.edgeCoeffs) := by
  let X := Polygon4g (g + 1)
  let K := singularChainComplexZ X
  let F :=
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (polygon4gMkContinuousMap (g + 1))))
  let pushedDiskCycle : SingularChainCoproduct X 1 :=
    ModuleCat.Hom.hom (F.f 1) algebra.diskCycle
  let edgeCycle : SingularChainCoproduct X 1 :=
    ∑ e : Fin (2 * (g + 1)), algebra.edgeCoeffs e • edgeChain g e
  have hpushedCycle : K.d 1 0 pushedDiskCycle = 0 := by
    change ((forget₂ (ModuleCat ℤ) Ab).map (K.d 1 0))
      (((forget₂ (ModuleCat ℤ) Ab).map (F.f 1)) algebra.diskCycle) = 0
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.Hom.comm,
      ConcreteCategory.forget₂_comp_apply]
    change ModuleCat.Hom.hom (F.f 0)
      (ModuleCat.Hom.hom ((singularChainComplexZ DiskC).d 1 0) algebra.diskCycle) = 0
    rw [algebra.diskCycle_isCycle]
    exact map_zero (ModuleCat.Hom.hom (F.f 0))
  have hedgeCycle : K.d 1 0 edgeCycle = 0 := by
    exact edgeChain_sum_isCycle g algebra.edgeCoeffs
  have hsumCycle : K.d 1 0 (pushedDiskCycle + edgeCycle) = 0 := by
    rw [map_add, hpushedCycle, hedgeCycle, add_zero]
  have hnat :
      singularH1_inducedLinearMap (polygon4gMkContinuousMap (g + 1))
          (singularH1ClassOfCycle DiskC algebra.diskCycle algebra.diskCycle_isCycle) =
        singularH1ClassOfCycle X pushedDiskCycle hpushedCycle := by
    exact singularH1_inducedLinearMap_classOfCycle
      (polygon4gMkContinuousMap (g + 1))
      algebra.diskCycle algebra.diskCycle_isCycle hpushedCycle
  rw [hnat]
  rw [← singularH1ClassOfCycle_add pushedDiskCycle edgeCycle
    hpushedCycle hedgeCycle hsumCycle]
  have hpushedEq :
      pushedDiskCycle =
        lifted.projectedSubdivisionChain - algebra.projectedRepairSum := by
    exact polygon4g_repair_sum_diskCycle_chainMap_eq
      g z hz decomp lifted pairs algebra
  refine singularH1ClassOfCycle_eq_of_boundary
    hz hsumCycle (algebra.edgeChainBoundarySum - lifted.subdivisionBoundary) ?_
  calc
    K.d 2 1 (algebra.edgeChainBoundarySum - lifted.subdivisionBoundary)
        = K.d 2 1 algebra.edgeChainBoundarySum -
            K.d 2 1 lifted.subdivisionBoundary := by
            rw [map_sub]
    _ = (algebra.projectedRepairSum - edgeCycle) -
          (lifted.projectedSubdivisionChain - z) := by
          rw [algebra.projectedRepair_homologous_edge,
            lifted.subdivision_homology]
    _ = z - ((lifted.projectedSubdivisionChain -
          algebra.projectedRepairSum) + edgeCycle) := by
          abel
    _ = z - (pushedDiskCycle + edgeCycle) := by
          rw [← hpushedEq]


/--
Zero homology class means an explicit singular two-boundary.

This is the concrete `ModuleCat` quotient form of first singular
homology specialized to one-cycles.
-/
theorem singularH1ClassOfCycle_eq_zero_boundary
    (X : Type) [TopologicalSpace X]
    (z : SingularChainCoproduct X 1)
    (hz : (singularChainComplexZ X).d 1 0 z = 0)
    (h : singularH1ClassOfCycle X z hz = 0) :
    ∃ B : ((singularChainComplexZ X).sc 1).X₁,
      ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B = z := by
  let K := singularChainComplexZ X
  let S := K.sc 1
  let c : K.cycles 1 :=
    K.cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz
  have hπ :
      ModuleCat.Hom.hom (K.homologyπ 1) c = 0 := by
    change singularH1ClassOfCycle X z hz = 0 at h
    simpa [K, c, singularH1ClassOfCycle] using h
  have hπS :
      ModuleCat.Hom.hom S.homologyπ c = 0 := hπ
  have hq :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) = 0 := by
    have hπiso :
        ModuleCat.Hom.hom (S.homologyπ ≫ S.moduleCatHomologyIso.hom) c = 0 := by
      rw [ModuleCat.comp_apply, hπS, map_zero]
    rwa [S.π_moduleCatCyclesIso_hom] at hπiso
  have hmem :
      ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c ∈
        LinearMap.range S.moduleCatLeftHomologyData.f'.hom := by
    simpa [ShortComplex.moduleCatLeftHomologyData_π_hom] using
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range S.moduleCatLeftHomologyData.f'.hom)).1 hq
  rcases hmem with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  have hBsub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) := by
    rw [hB]
  have hcycleSub :
      ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom c) =
        ModuleCat.Hom.hom S.iCycles c := by
    rw [← ModuleCat.comp_apply, S.moduleCatCyclesIso_hom_i]
  calc
    ModuleCat.Hom.hom (((singularChainComplexZ X).sc 1).f) B =
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
          (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B) := by
          change ModuleCat.Hom.hom S.f B =
            ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
              (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' B)
          rw [← ModuleCat.comp_apply, S.moduleCatLeftHomologyData.f'_i]
    _ = ModuleCat.Hom.hom S.iCycles c := by
      rw [hBsub, hcycleSub]
    _ = z := by
      exact K.i_cyclesMk z 0 (ComplexShape.next_eq' _ (by simp [ComplexShape.down])) hz

/--
Bridge from the short-complex boundary object in degree one to the
displayed degree-two singular-chain object.
-/
theorem hurewicz_singularBoundary_eq_sc_f
    (X : Type) [TopologicalSpace X] :
    let K := singularChainComplexZ X
    let S := K.sc 1
    ∀ (s : S.X₁), ∃ s' : (singularChainComplexZ X).X 2,
      S.f.hom s = ((singularChainComplexZ X).d 2 1).hom s' := by
  intro K S s
  -- `S.f = K.d ((ComplexShape.down ℕ).prev 1) 1` and `(ComplexShape.down ℕ).prev 1 = 2`,
  -- so the short-complex map is the degree-`(2,1)` differential precomposed with the
  -- canonical degree-coincidence isomorphism.
  have hprev : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (rfl : (ComplexShape.down ℕ).Rel 2 1)
  refine ⟨(K.XIsoOfEq hprev).hom s, ?_⟩
  have hcomp := K.XIsoOfEq_hom_comp_d hprev 1
  have h := congrArg (fun (φ : _ ⟶ _) => ModuleCat.Hom.hom φ s) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

noncomputable def signedFaceTargetEdgeCoefficient
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1))) :
    ℤ := by
  classical
  exact
    ∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
        (Finset.univ : Finset (Fin 3)),
      (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) *
        if singularSimplexFace (simplex si.1) si.2 = edgeSimplex g target then
          (1 : ℤ)
        else
          0

noncomputable def edgeSimplexTargetCoefficient
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g) :
    ℤ := by
  classical
  exact
    ∑ e : Fin (2 * (g + 1)),
      v e *
        if edgeSimplex g e = edgeSimplex g target then
          (1 : ℤ)
        else
          0

/--
Concrete edge singular simplices are distinct for distinct edge indices.
-/
theorem edgeArcIdx_injective
    (g : ℕ) :
    Function.Injective (edgeArcIdx g) := by
  intro i j h
  apply Fin.ext
  unfold edgeArcIdx at h
  have hi := Nat.div_add_mod i.val 2
  have hj := Nat.div_add_mod j.val 2
  omega

/--
An arc index is one of the canonical representatives used by the
edge-basis loops.
-/
def IsCanonicalEdgeArcIdx (g : ℕ) (a : ℕ) : Prop :=
  ∃ i : Fin (2 * (g + 1)), a = edgeArcIdx g i

/--
Concrete arithmetic shape of the boundary arcs used as canonical
edge representatives: they lie in the polygon side range and occupy
residue slots `0` or `1` modulo `4`.
-/
def IsCanonicalEdgeArcResidue (g : ℕ) (a : ℕ) : Prop :=
  a < 4 * (g + 1) ∧ a % 4 < 2

/-- Canonical edge arc indices lie among the `4 * (g + 1)` polygon sides. -/
lemma IsCanonicalEdgeArcIdx.lt_four_mul
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    a < 4 * (g + 1) := by
  obtain ⟨i, rfl⟩ := ha
  unfold edgeArcIdx
  have hi := i.2
  have hdiv := Nat.div_add_mod i.val 2
  omega

/-- Canonical edge arc indices are exactly the first two side slots in each block of four. -/
lemma IsCanonicalEdgeArcIdx.mod_four_lt_two
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    a % 4 < 2 := by
  obtain ⟨i, rfl⟩ := ha
  unfold edgeArcIdx
  have hmod2 : i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- Canonical edge arc indices have the concrete residue-range shape. -/
lemma IsCanonicalEdgeArcIdx.residue
    {g a : ℕ} (ha : IsCanonicalEdgeArcIdx g a) :
    IsCanonicalEdgeArcResidue g a :=
  ⟨ha.lt_four_mul, ha.mod_four_lt_two⟩

/-- Every arc in the canonical residue range is represented by an edge index. -/
lemma IsCanonicalEdgeArcResidue.to_edgeArcIdx
    {g a : ℕ} (ha : IsCanonicalEdgeArcResidue g a) :
    IsCanonicalEdgeArcIdx g a := by
  refine ⟨⟨2 * (a / 4) + a % 4, ?_⟩, ?_⟩
  · have hdecomp : a = 4 * (a / 4) + a % 4 := by
      have h0 : 4 * (a / 4) + a % 4 = a := by
        simpa [Nat.mul_comm] using Nat.div_add_mod a 4
      exact h0.symm
    have hmod4 : a % 4 < 4 := Nat.mod_lt a (by norm_num : 0 < 4)
    have ha_lt : a < 4 * (g + 1) := ha.1
    have hrem_lt : a % 4 < 2 := ha.2
    have hq_lt : a / 4 < g + 1 := by
      have hblock_le : 4 * (a / 4) ≤ a := by
        omega
      omega
    have hstep : 2 * (a / 4) + a % 4 < 2 * ((a / 4) + 1) := by
      omega
    have hbound : 2 * ((a / 4) + 1) ≤ 2 * (g + 1) := by
      omega
    omega
  · unfold edgeArcIdx
    have hdiv :
        (2 * (a / 4) + a % 4) / 2 = a / 4 := by
      rw [show 2 * (a / 4) + a % 4 = a % 4 + 2 * (a / 4) by omega]
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      rw [Nat.div_eq_of_lt ha.2]
      simp
    have hmod :
        (2 * (a / 4) + a % 4) % 2 = a % 4 := by
      rw [show 2 * (a / 4) + a % 4 = a % 4 + 2 * (a / 4) by omega]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt ha.2
    change a = 4 * ((2 * (a / 4) + a % 4) / 2) +
      (2 * (a / 4) + a % 4) % 2
    rw [hdiv, hmod]
    have hdecomp : a = 4 * (a / 4) + a % 4 := by
      have h0 : 4 * (a / 4) + a % 4 = a := by
        simpa [Nat.mul_comm] using Nat.div_add_mod a 4
      exact h0.symm
    omega

/--
The source-side boundary equality for an `aᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_aPair_source_angle_eq
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t) :
    (a : ℝ) + 1 / 2 = (4 * i.val : ℝ) + t := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val) t := by
    exact congrArg Subtype.val _ha_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val) t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val) t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    positivity
  have htarget_lt_one :
      ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the source side of an `aᵢ`
pairing recovers the concrete source arc index.
-/
theorem boundary_midpoint_aPair_source_arc_index
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t) :
    a = 4 * i.val := by
  have hangle :=
    boundary_midpoint_aPair_source_angle_eq g a i t _ha _ht _ha_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have ha_lt_succ : (a : ℝ) < (4 * i.val : ℝ) + 1 := by
    linarith
  have hi_lt_succ : (4 * i.val : ℝ) < (a : ℝ) + 1 := by
    linarith
  have ha_le : a ≤ 4 * i.val := by
    by_contra hle
    have hlt : 4 * i.val < a := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 1 ≤ a := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have hi_le : 4 * i.val ≤ a := by
    by_contra hle
    have hlt : a < 4 * i.val := Nat.lt_of_not_ge hle
    have hsucc : a + 1 ≤ 4 * i.val := Nat.succ_le_of_lt hlt
    have hsuccR : (a : ℝ) + 1 ≤ (4 * i.val : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
The target-side boundary equality for an `aᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_aPair_target_angle_eq
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    (b : ℝ) + 1 / 2 = (4 * i.val + 2 : ℝ) + (1 - t) := by
  have hval :
      boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 2) (1 - t) := by
    exact congrArg Subtype.val _hb_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 2) (1 - t) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 2) (1 - t) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hb_nonneg : (0 : ℝ) ≤ ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · nlinarith
    · positivity
  have htarget_lt_one :
      ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 2 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the reversed target side of an
`aᵢ` pairing recovers the concrete target arc index.
-/
theorem boundary_midpoint_aPair_target_arc_index
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    b = 4 * i.val + 2 := by
  have hangle :=
    boundary_midpoint_aPair_target_angle_eq g b i t _hb _ht _hb_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_lt_succ :
      (b : ℝ) < (4 * i.val + 2 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 2 : ℝ) < (b : ℝ) + 1 := by
    linarith
  have hb_le : b ≤ 4 * i.val + 2 := by
    by_contra hle
    have hlt : 4 * i.val + 2 < b := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 2 + 1 ≤ b := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 2 : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 2 ≤ b := by
    by_contra hle
    have hlt : b < 4 * i.val + 2 := Nat.lt_of_not_ge hle
    have hsucc : b + 1 ≤ 4 * i.val + 2 := Nat.succ_le_of_lt hlt
    have hsuccR : (b : ℝ) + 1 ≤ (4 * i.val + 2 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
At a canonical midpoint, an `aᵢ` side-pairing source/target equality
recovers the concrete source and reversed target arc indices.
-/
theorem boundary_midpoint_aPair_arc_indices
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    a = 4 * i.val ∧ b = 4 * i.val + 2 := by
  exact ⟨
    boundary_midpoint_aPair_source_arc_index g a i t _ha _ht _ha_eq,
    boundary_midpoint_aPair_target_arc_index g b i t _hb _ht _hb_eq⟩

/--
The midpoint of a canonical-residue arc cannot be the reversed endpoint
of an `aᵢ` side-pairing generator.
-/
theorem boundary_midpoint_aPair_target_residue_absurd
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 2) (1 - t)) :
    False := by
  obtain ⟨_ha_idx, hb_idx⟩ :=
    boundary_midpoint_aPair_arc_indices
      g a b i t _ha _hb _ht _ha_eq _hb_eq
  have hb_mod : (4 * i.val + 2) % 4 < 2 := by
    simpa [hb_idx] using _hb.2
  omega

/--
The source-side boundary equality for a `bᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_bPair_source_angle_eq
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t) :
    (a : ℝ) + 1 / 2 = (4 * i.val + 1 : ℝ) + t := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 1) t := by
    exact congrArg Subtype.val _ha_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 1) t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 1) t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    positivity
  have htarget_lt_one :
      ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) < 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_lt_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 1 : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the source side of a `bᵢ`
pairing recovers the concrete source arc index.
-/
theorem boundary_midpoint_bPair_source_arc_index
    (g : ℕ) (a : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t) :
    a = 4 * i.val + 1 := by
  have hangle :=
    boundary_midpoint_bPair_source_angle_eq g a i t _ha _ht _ha_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have ha_lt_succ :
      (a : ℝ) < (4 * i.val + 1 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 1 : ℝ) < (a : ℝ) + 1 := by
    linarith
  have ha_le : a ≤ 4 * i.val + 1 := by
    by_contra hle
    have hlt : 4 * i.val + 1 < a := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 1 + 1 ≤ a := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 1 : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 1 ≤ a := by
    by_contra hle
    have hlt : a < 4 * i.val + 1 := Nat.lt_of_not_ge hle
    have hsucc : a + 1 ≤ 4 * i.val + 1 := Nat.succ_le_of_lt hlt
    have hsuccR : (a : ℝ) + 1 ≤ (4 * i.val + 1 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
The target-side boundary equality for a `bᵢ` pairing at a canonical
midpoint yields equality of the unwrapped boundary coordinates.
-/
theorem boundary_midpoint_bPair_target_angle_eq
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    (b : ℝ) + 1 / 2 = (4 * i.val + 3 : ℝ) + (1 - t) := by
  have hval :
      boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) (4 * i.val + 3) (1 - t) := by
    exact congrArg Subtype.val _hb_eq
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) (4 * i.val + 3) (1 - t) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) (4 * i.val + 3) (1 - t) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ)) +
              (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hb_pos : (0 : ℝ) < ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · nlinarith
    · positivity
  have htarget_le_one :
      ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) ≤ 1 := by
    have hi_succ_le : (i.val : ℝ) + 1 ≤ (g : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    rw [div_le_iff₀ hGpos]
    nlinarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((4 * i.val + 3 : ℝ) + (1 - t)) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
  field_simp [hGpos.ne'] at hmul
  linarith

/--
At a canonical midpoint, equality with the reversed target side of a
`bᵢ` pairing recovers the concrete target arc index.
-/
theorem boundary_midpoint_bPair_target_arc_index
    (g : ℕ) (b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    b = 4 * i.val + 3 := by
  have hangle :=
    boundary_midpoint_bPair_target_angle_eq g b i t _hb _ht _hb_eq
  have ht0 : 0 ≤ t := _ht.1
  have ht1 : t ≤ 1 := _ht.2
  have htarget_lt_succ :
      (b : ℝ) < (4 * i.val + 3 : ℝ) + 1 := by
    linarith
  have htarget_gt_pred :
      (4 * i.val + 3 : ℝ) < (b : ℝ) + 1 := by
    linarith
  have hb_le : b ≤ 4 * i.val + 3 := by
    by_contra hle
    have hlt : 4 * i.val + 3 < b := Nat.lt_of_not_ge hle
    have hsucc : 4 * i.val + 3 + 1 ≤ b := Nat.succ_le_of_lt hlt
    have hsuccR : (4 * i.val + 3 : ℝ) + 1 ≤ (b : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have htarget_le : 4 * i.val + 3 ≤ b := by
    by_contra hle
    have hlt : b < 4 * i.val + 3 := Nat.lt_of_not_ge hle
    have hsucc : b + 1 ≤ 4 * i.val + 3 := Nat.succ_le_of_lt hlt
    have hsuccR : (b : ℝ) + 1 ≤ (4 * i.val + 3 : ℝ) := by
      exact_mod_cast hsucc
    linarith
  omega

/--
At a canonical midpoint, a `bᵢ` side-pairing source/target equality
recovers the concrete source and reversed target arc indices.
-/
theorem boundary_midpoint_bPair_arc_indices
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    a = 4 * i.val + 1 ∧ b = 4 * i.val + 3 := by
  exact ⟨
    boundary_midpoint_bPair_source_arc_index g a i t _ha _ht _ha_eq,
    boundary_midpoint_bPair_target_arc_index g b i t _hb _ht _hb_eq⟩

/--
The midpoint of a canonical-residue arc cannot be the reversed endpoint
of a `bᵢ` side-pairing generator.
-/
theorem boundary_midpoint_bPair_target_residue_absurd
    (g : ℕ) (a b : ℕ) (i : Fin (g + 1)) (t : ℝ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (_ha_eq :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 1) t)
    (_hb_eq :
      boundaryParam (g + 1) b (1 / 2 : ℝ) =
        boundaryParam (g + 1) (4 * i.val + 3) (1 - t)) :
    False := by
  obtain ⟨_ha_idx, hb_idx⟩ :=
    boundary_midpoint_bPair_arc_indices
      g a b i t _ha _hb _ht _ha_eq _hb_eq
  have hb_mod : (4 * i.val + 3) % 4 < 2 := by
    simpa [hb_idx] using _hb.2
  omega

/--
No direct side-pairing generator relates two midpoint arcs that both lie
in the canonical residue range.
-/
theorem boundary_midpoint_sideGen_residue_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Polygon4g.SideGen (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    False := by
  generalize hx :
      boundaryParam (g + 1) a (1 / 2 : ℝ) = x at _h
  generalize hy :
      boundaryParam (g + 1) b (1 / 2 : ℝ) = y at _h
  cases _h with
  | a_pair i t ht =>
      exact boundary_midpoint_aPair_target_residue_absurd
        g a b i t _ha _hb ht hx hy
  | b_pair i t ht =>
      exact boundary_midpoint_bPair_target_residue_absurd
        g a b i t _ha _hb ht hx hy

/--
The direct `EqvGen.rel` case cannot identify distinct canonical-residue
midpoint arcs once direct side-generator steps have been ruled out.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_rel_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hstep :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        False)
    (_h :
      Polygon4g.SideGen (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exfalso
  exact _hstep _ha _hb _h

/--
Equality of two canonical-residue midpoint boundary parameters recovers
the raw boundary arc index.
-/
theorem boundary_midpoint_residue_eq_of_param_eq
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  have hval :
      boundaryParamC' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) b (1 / 2 : ℝ) := by
    exact congrArg Subtype.val _h
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) a (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) b (1 / 2 : ℝ) : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have ha_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have ha_lt_one : ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have ha_succ_le : (a : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _ha.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hb_nonneg : (0 : ℝ) ≤ ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hb_lt_one : ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hb_succ_le : (b : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt _hb.1)
    rw [div_lt_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((a : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((b : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hab_real : (a : ℝ) = b := by
    have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
    field_simp [hGpos.ne'] at hmul
    linarith
  exact_mod_cast hab_real

/--
The reflexive constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_refl
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hpt :
      boundaryParam (g + 1) a (1 / 2 : ℝ) =
        boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  exact boundary_midpoint_residue_eq_of_param_eq g a b _ha _hb _hpt

private theorem boundaryParam_midpoint_inj_of_lt
    (g : ℕ) {j j' : ℕ}
    (hj : j < 4 * (g + 1)) (hj' : j' < 4 * (g + 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h :
      boundaryParam (g + 1) j (1 / 2 : ℝ) =
        boundaryParam (g + 1) j' t) :
    t = 1 / 2 ∧ j = j' := by
  have hval :
      boundaryParamC' (4 * (g + 1)) j (1 / 2 : ℝ) =
        boundaryParamC' (4 * (g + 1)) j' t := by
    exact congrArg Subtype.val h
  have hperiod :=
    Complex.exp_eq_exp_iff_exists_int.mp (by
      simpa [boundaryParamC', boundaryParam', boundaryParam] using hval)
  obtain ⟨n, hn⟩ := hperiod
  have hangle :
      boundaryAngle' (4 * (g + 1)) j (1 / 2 : ℝ) =
        boundaryAngle' (4 * (g + 1)) j' t +
          (n : ℝ) * (2 * Real.pi) := by
    have hmul :
        (boundaryAngle' (4 * (g + 1)) j (1 / 2 : ℝ) : ℂ) * Complex.I =
          ((boundaryAngle' (4 * (g + 1)) j' t : ℂ) +
              (n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hcancel :=
      mul_right_cancel₀ (show (Complex.I : ℂ) ≠ 0 from Complex.I_ne_zero) hmul
    exact_mod_cast hcancel
  have hGpos : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by
    positivity
  have hcoord :
      ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) + (n : ℝ) := by
    have hmul :
        (2 * Real.pi) *
            (((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ)) =
          (2 * Real.pi) *
            ((((j' : ℝ) + t) / (4 * (g + 1) : ℝ)) + (n : ℝ)) := by
      simpa [boundaryAngle', div_eq_mul_inv, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] using hangle
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hmul
  have hj_pos : (0 : ℝ) < ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) := by
    positivity
  have hj_lt_one : ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) < 1 := by
    have hj_succ_le : (j : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    rw [div_lt_iff₀ hGpos]
    linarith
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have htarget_nonneg :
      (0 : ℝ) ≤ ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    apply div_nonneg
    · positivity
    · positivity
  have htarget_le_one :
      ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) ≤ 1 := by
    have hj'_succ_le : (j' : ℝ) + 1 ≤ 4 * ((g : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt hj')
    rw [div_le_iff₀ hGpos]
    linarith
  have hn_zero : n = 0 := by
    have hn_lt_one : (n : ℝ) < 1 := by linarith
    have hn_gt_neg_one : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
    have hn_int_gt : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    omega
  have hcoord0 :
      ((j : ℝ) + 1 / 2) / (4 * (g + 1) : ℝ) =
        ((j' : ℝ) + t) / (4 * (g + 1) : ℝ) := by
    simpa [hn_zero] using hcoord
  have hreal : (j : ℝ) + 1 / 2 = (j' : ℝ) + t := by
    have hmul := congrArg (fun x : ℝ => x * (4 * (g + 1) : ℝ)) hcoord0
    field_simp [hGpos.ne'] at hmul
    linarith
  have hj_eq : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsucc : j + 1 ≤ j' := Nat.succ_le_of_lt hlt
      have hsuccR : (j : ℝ) + 1 ≤ (j' : ℝ) := by exact_mod_cast hsucc
      linarith
    · have hsucc : j' + 1 ≤ j := Nat.succ_le_of_lt hgt
      have hsuccR : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hsucc
      linarith
  have ht_half : t = 1 / 2 := by
    subst hj_eq
    linarith
  exact ⟨ht_half, hj_eq⟩

private theorem boundary_midpoint_sideGen_image_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      y = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  cases h with
  | a_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val) t := by
        rw [← hx]
      obtain ⟨ht_half, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      refine ⟨4 * i.val + 2, by omega, ?_⟩
      norm_num [ht_half]
  | b_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 1) t := by
        rw [← hx]
      obtain ⟨ht_half, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      refine ⟨4 * i.val + 3, by omega, ?_⟩
      norm_num [ht_half]

private theorem boundary_midpoint_sideGen_preimage_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hy : y = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      x = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  cases h with
  | a_pair i t ht =>
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 2) (1 - t) := by
        rw [← hy]
      obtain ⟨hone_minus_t, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht_rev hy_param
      have ht_half : t = 1 / 2 := by linarith
      refine ⟨4 * i.val, by omega, ?_⟩
      simp [ht_half]
  | b_pair i t ht =>
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 3) (1 - t) := by
        rw [← hy]
      obtain ⟨hone_minus_t, _hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht_rev hy_param
      have ht_half : t = 1 / 2 := by linarith
      refine ⟨4 * i.val + 1, by omega, ?_⟩
      simp [ht_half]

private theorem boundary_midpoint_eqvGen_image_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      y = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  have midpoint_iff :
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          x = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            y = boundaryParam (g + 1) k (1 / 2 : ℝ)) ∧
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          y = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            x = boundaryParam (g + 1) k (1 / 2 : ℝ)) := by
    clear hj hx
    induction h with
    | refl p =>
        exact ⟨
          (fun hj hp => ⟨_, hj, hp⟩),
          (fun hj hp => ⟨_, hj, hp⟩)⟩
    | rel p q hrel =>
        exact ⟨
          (fun hj hp => boundary_midpoint_sideGen_image_is_midpoint g hrel hj hp),
          (fun hj hq => boundary_midpoint_sideGen_preimage_is_midpoint g hrel hj hq)⟩
    | symm p q _ ih =>
        exact ⟨ih.2, ih.1⟩
    | trans p mid q _ _ ih_left ih_right =>
        exact ⟨
          (fun hj hp => by
            obtain ⟨m, hm, hmid⟩ := ih_left.1 hj hp
            exact ih_right.1 hm hmid),
          (fun hj hq => by
            obtain ⟨m, hm, hmid⟩ := ih_right.2 hj hq
            exact ih_left.2 hm hmid)⟩
  exact midpoint_iff.1 hj hx

private theorem boundary_midpoint_eqvGen_preimage_is_midpoint
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j : ℕ} (hj : j < 4 * (g + 1))
    (hy : y = boundaryParam (g + 1) j (1 / 2 : ℝ)) :
    ∃ k : ℕ, k < 4 * (g + 1) ∧
      x = boundaryParam (g + 1) k (1 / 2 : ℝ) := by
  have midpoint_iff :
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          x = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            y = boundaryParam (g + 1) k (1 / 2 : ℝ)) ∧
      (∀ {j : ℕ}, j < 4 * (g + 1) →
          y = boundaryParam (g + 1) j (1 / 2 : ℝ) →
          ∃ k : ℕ, k < 4 * (g + 1) ∧
            x = boundaryParam (g + 1) k (1 / 2 : ℝ)) := by
    clear hj hy
    induction h with
    | refl p =>
        exact ⟨
          (fun hj hp => ⟨_, hj, hp⟩),
          (fun hj hp => ⟨_, hj, hp⟩)⟩
    | rel p q hrel =>
        exact ⟨
          (fun hj hp => boundary_midpoint_sideGen_image_is_midpoint g hrel hj hp),
          (fun hj hq => boundary_midpoint_sideGen_preimage_is_midpoint g hrel hj hq)⟩
    | symm p q _ ih =>
        exact ⟨ih.2, ih.1⟩
    | trans p mid q _ _ ih_left ih_right =>
        exact ⟨
          (fun hj hp => by
            obtain ⟨m, hm, hmid⟩ := ih_left.1 hj hp
            exact ih_right.1 hm hmid),
          (fun hj hq => by
            obtain ⟨m, hm, hmid⟩ := ih_right.2 hj hq
            exact ih_left.2 hm hmid)⟩
  exact midpoint_iff.2 hj hy

private def boundaryMidpointCanonicalRep (n : ℕ) : ℕ :=
  if n % 4 < 2 then n else n - 2

private theorem boundaryMidpointCanonicalRep_of_residue
    {g n : ℕ} (hn : IsCanonicalEdgeArcResidue g n) :
    boundaryMidpointCanonicalRep n = n := by
  simp [boundaryMidpointCanonicalRep, hn.2]

private theorem boundary_midpoint_sideGen_canonicalRep_eq
    (g : ℕ) {x y : DiskC}
    (h : Polygon4g.SideGen (g + 1) x y)
    {j k : ℕ} (hj : j < 4 * (g + 1)) (hk : k < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ))
    (hy : y = boundaryParam (g + 1) k (1 / 2 : ℝ)) :
    boundaryMidpointCanonicalRep j = boundaryMidpointCanonicalRep k := by
  cases h with
  | a_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val) t := by
        rw [← hx]
      obtain ⟨ht_half, hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) k (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 2) (1 - t) := by
        rw [← hy]
      obtain ⟨_hone_minus_t, hk_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hk (by omega) ht_rev hy_param
      rw [hj_eq, hk_eq]
      simp [boundaryMidpointCanonicalRep]
  | b_pair i t ht =>
      have hx_param :
          boundaryParam (g + 1) j (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 1) t := by
        rw [← hx]
      obtain ⟨ht_half, hj_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hj (by omega) ht hx_param
      have ht_rev : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hy_param :
          boundaryParam (g + 1) k (1 / 2 : ℝ) =
            boundaryParam (g + 1) (4 * i.val + 3) (1 - t) := by
        rw [← hy]
      obtain ⟨_hone_minus_t, hk_eq⟩ :=
        boundaryParam_midpoint_inj_of_lt g hk (by omega) ht_rev hy_param
      rw [hj_eq, hk_eq]
      simp [boundaryMidpointCanonicalRep]

private theorem boundary_midpoint_eqvGen_canonicalRep_eq
    (g : ℕ) {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {j k : ℕ} (hj : j < 4 * (g + 1)) (hk : k < 4 * (g + 1))
    (hx : x = boundaryParam (g + 1) j (1 / 2 : ℝ))
    (hy : y = boundaryParam (g + 1) k (1 / 2 : ℝ)) :
    boundaryMidpointCanonicalRep j = boundaryMidpointCanonicalRep k := by
  revert j k
  induction h with
  | refl p =>
      intro j k hj hk hx hy
      have hidx :=
        boundaryParam_midpoint_inj_of_lt g hj hk
          (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
          (by rw [← hx, ← hy])
      simp [hidx.2]
  | rel p q hrel =>
      intro j k hj hk hx hy
      exact boundary_midpoint_sideGen_canonicalRep_eq g hrel hj hk hx hy
  | symm p q _ ih =>
      intro j k hj hk hx hy
      exact (ih hk hj hy hx).symm
  | trans p mid q hpq hqr ih_left ih_right =>
      intro j k hj hk hx hy
      obtain ⟨m, hm, hmid⟩ :=
        boundary_midpoint_eqvGen_image_is_midpoint g hpq hj hx
      exact (ih_left hj hm hx hmid).trans (ih_right hm hk hmid hy)

theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    {g : ℕ} {x y : DiskC}
    (h : Relation.EqvGen (Polygon4g.SideGen (g + 1)) x y)
    {a b : ℕ}
    (ha : IsCanonicalEdgeArcResidue g a)
    (hb : IsCanonicalEdgeArcResidue g b)
    (hxa : x = boundaryParam (g + 1) a (1 / 2 : ℝ))
    (hyb : y = boundaryParam (g + 1) b (1 / 2 : ℝ)) :
    a = b := by
  have hrep :=
    boundary_midpoint_eqvGen_canonicalRep_eq g h ha.1 hb.1 hxa hyb
  simpa [boundaryMidpointCanonicalRep_of_residue ha,
    boundaryMidpointCanonicalRep_of_residue hb] using hrep

/--
The remaining reversed-closure content for the symmetric constructor case.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm_core
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))) :
    a = b := by
  exact (boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    _h _hb _ha rfl rfl).symm

/--
The symmetric constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm_core
    g a b _ha _hb _h

/--
The transitive constructor case for canonical-residue midpoint `EqvGen`
separation.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_trans
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (mid : DiskC)
    (_hleft :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ)) mid)
    (_hright :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        mid (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_aux
    (Relation.EqvGen.trans _ _ _ _hleft _hright) _ha _hb rfl rfl

/--
The remaining transitive-closure content for midpoint `EqvGen` separation,
assuming the one-step canonical-residue midpoint case has already been
handled.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_closure
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hrel :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        a = b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  generalize hx :
      boundaryParam (g + 1) a (1 / 2 : ℝ) = x at _h
  generalize hy :
      boundaryParam (g + 1) b (1 / 2 : ℝ) = y at _h
  cases _h with
  | refl p =>
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_refl g a b _ha _hb
        (by rw [hx, hy])
  | rel p q hrel =>
      rw [← hx, ← hy] at hrel
      exact _hrel _ha _hb hrel
  | symm p q hrel =>
      rw [← hy, ← hx] at hrel
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_symm
        g a b _ha _hb hrel
  | trans p mid q hleft hright =>
      rw [← hx] at hleft
      rw [← hy] at hright
      exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_trans
        g a b _ha _hb mid hleft hright

/--
Midpoint `EqvGen` separation for canonical-residue arcs, assuming the
direct side-generator obstruction for canonical-residue endpoints.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen_and_sideGen_absurd
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_hstep :
      ∀ {a b : ℕ},
        IsCanonicalEdgeArcResidue g a →
        IsCanonicalEdgeArcResidue g b →
        Polygon4g.SideGen (g + 1)
          (boundaryParam (g + 1) a (1 / 2 : ℝ))
          (boundaryParam (g + 1) b (1 / 2 : ℝ)) →
        False)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_closure g a b _ha _hb
    (fun ha hb hrel =>
      boundary_midpoint_sideRel_residue_eq_of_eqvGen_rel_absurd
        g _ _ ha hb _hstep hrel)
    _h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_residue_eq_of_eqvGen
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcResidue g a)
    (_hb : IsCanonicalEdgeArcResidue g b)
    (_h :
      Relation.EqvGen (Polygon4g.SideGen (g + 1))
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen_and_sideGen_absurd
    g a b _ha _hb
    (fun ha hb hstep =>
      boundary_midpoint_sideGen_residue_absurd g _ _ ha hb hstep)
    _h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_residue_eq
    (g : ℕ) (a b : ℕ)
    (ha : IsCanonicalEdgeArcResidue g a)
    (hb : IsCanonicalEdgeArcResidue g b)
    (h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq_of_eqvGen g a b ha hb h

/--
Midpoint `SideRel` between two boundary-arc indices in the canonical
residue range forces the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_canonical_residue_eq
    (g : ℕ) (a b : ℕ)
    (ha_lt : a < 4 * (g + 1)) (ha_mod : a % 4 < 2)
    (hb_lt : b < 4 * (g + 1)) (hb_mod : b % 4 < 2)
    (h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_residue_eq g a b
    ⟨ha_lt, ha_mod⟩ ⟨hb_lt, hb_mod⟩ h

/--
Midpoint `SideRel` between two canonical boundary-arc indices forces
the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_isCanonicalArc_eq
    (g : ℕ) (a b : ℕ)
    (_ha : IsCanonicalEdgeArcIdx g a)
    (_hb : IsCanonicalEdgeArcIdx g b)
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_canonical_residue_eq g a b
    _ha.lt_four_mul _ha.mod_four_lt_two _hb.lt_four_mul _hb.mod_four_lt_two _h

/--
Midpoint `SideRel` between two canonical boundary-arc indices forces
the raw arc indices to agree.
-/
theorem boundary_midpoint_sideRel_canonical_arc_eq
    (g : ℕ) (a b : ℕ)
    (_ha : ∃ i : Fin (2 * (g + 1)), a = edgeArcIdx g i)
    (_hb : ∃ j : Fin (2 * (g + 1)), b = edgeArcIdx g j)
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) a (1 / 2 : ℝ))
        (boundaryParam (g + 1) b (1 / 2 : ℝ))) :
    a = b := by
  exact boundary_midpoint_sideRel_isCanonicalArc_eq g a b _ha _hb _h

/--
The side-pairing relation at midpoints of canonical boundary-edge
representatives separates the edge-basis arc index.
-/
theorem edgeArcIdx_eq_of_boundary_midpoint_sideRel
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (_h :
      Polygon4g.SideRel (g + 1)
        (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ))
        (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))) :
    edgeArcIdx g i = edgeArcIdx g j := by
  exact boundary_midpoint_sideRel_canonical_arc_eq g
    (edgeArcIdx g i) (edgeArcIdx g j) ⟨i, rfl⟩ ⟨j, rfl⟩ _h

/--
The quotient midpoint of a canonical boundary-edge representative
separates the edge-basis arc index.
-/
theorem edgeArcIdx_eq_of_boundary_midpoint_mk_eq
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (h :
      Polygon4g.mk (g + 1)
          (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ)) =
        Polygon4g.mk (g + 1)
          (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))) :
    edgeArcIdx g i = edgeArcIdx g j := by
  exact edgeArcIdx_eq_of_boundary_midpoint_sideRel g
    ((Polygon4g.mk_eq_mk_iff (g + 1)
      (boundaryParam (g + 1) (edgeArcIdx g i) (1 / 2 : ℝ))
      (boundaryParam (g + 1) (edgeArcIdx g j) (1 / 2 : ℝ))).mp h)

/--
Equality of concrete edge interval maps determines the boundary arc
index used by the parametrization.
-/
theorem edgeArcIdx_eq_of_edgeContMap_eq
    (g : ℕ) {i j : Fin (2 * (g + 1))}
    (h : edgeContMap g i = edgeContMap g j) :
    edgeArcIdx g i = edgeArcIdx g j := by
  apply edgeArcIdx_eq_of_boundary_midpoint_mk_eq g
  let mid : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩
  have happ := congrFun (congrArg DFunLike.coe h) mid
  simpa [edgeContMap, mid] using happ

/--
Concrete edge interval maps are distinct for distinct edge indices.
-/
theorem edgeContMap_injective
    (g : ℕ) :
    Function.Injective (edgeContMap g) := by
  intro i j h
  exact edgeArcIdx_injective g (edgeArcIdx_eq_of_edgeContMap_eq g h)

/--
Concrete edge singular simplices are distinct for distinct edge indices.
-/
theorem edgeSimplex_injective
    (g : ℕ) :
    Function.Injective (edgeSimplex g) := by
  intro i j h
  apply edgeContMap_injective g
  ext t
  let s : stdSimplex ℝ (Fin 2) := stdSimplexHomeomorphUnitInterval.symm t
  have hs : stdSimplexToUnitInterval s = t := by
    exact stdSimplexHomeomorphUnitInterval.apply_symm_apply t
  have happ := congrFun (congrArg DFunLike.coe h) s
  simpa [edgeSimplex, s, hs] using happ

/--
Reading the coefficient of the target concrete edge simplex in a chain
equality between signed face terms and the concrete edge-simplex sum
identifies the explicit face coefficient with the corresponding
coefficient of the edge-simplex sum.
-/
theorem signedFaceTargetEdgeCoefficient_eq_edgeSimplexTargetCoefficient_of_sum
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (_hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex =
      edgeSimplexTargetCoefficient g target v := by
  classical
  let I := (TopCat.toSSet.obj (TopCat.of (Polygon4g (g + 1)))).obj (op (SimplexCategory.mk 1))
  let Z : I → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let iso := ModuleCat.coprodIsoDirectSum Z
  let targetIdx : I := singularChainSimplexIndex (Polygon4g (g + 1)) 1
    (edgeSimplex g target)
  let coeffAt : SingularChainCoproduct (Polygon4g (g + 1)) 1 →ₗ[ℤ] ℤ :=
    (DirectSum.component ℤ I (fun _ : I => ℤ) targetIdx).comp iso.hom.hom
  have hι (i : I) :
      iso.hom.hom ((Sigma.ι Z i).hom (1 : ℤ)) =
        DirectSum.lof ℤ I (fun _ : I => ℤ) i (1 : ℤ) := by
    have hm := ModuleCat.ι_coprodIsoDirectSum_hom Z i
    have hh := congrArg ModuleCat.Hom.hom hm
    exact congrArg (fun f => f (1 : ℤ)) hh
  have hcoeff := congrArg coeffAt _hB
  have hleft :
      coeffAt
        (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        signedFaceTargetEdgeCoefficient g target Simplex coeff simplex := by
    simp [signedFaceTargetEdgeCoefficient, coeffAt, targetIdx,
      singularChainElement, I, Z, iso, hι, map_sum, DirectSum.component.of]
  have hright :
      coeffAt
        (∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        edgeSimplexTargetCoefficient g target v := by
    simp [edgeSimplexTargetCoefficient, coeffAt, targetIdx,
      singularChainElement, I, Z, iso, hι, map_sum, DirectSum.component.of]
  rw [hleft, hright] at hcoeff
  exact hcoeff

/--
The target coefficient of the concrete edge-simplex sum is the target
coordinate of the coefficient vector.
-/
theorem edgeSimplexTargetCoefficient_eq_of_injective
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (hinj : Function.Injective (edgeSimplex g)) :
    edgeSimplexTargetCoefficient g target v = v target := by
  classical
  unfold edgeSimplexTargetCoefficient
  calc
    (∑ e : Fin (2 * (g + 1)),
        v e *
          if edgeSimplex g e = edgeSimplex g target then
            (1 : ℤ)
          else
            0) =
        v target *
          if edgeSimplex g target = edgeSimplex g target then
            (1 : ℤ)
          else
            0 := by
        apply Finset.sum_eq_single target
        · intro e _he hne
          have hneq : edgeSimplex g e ≠ edgeSimplex g target := by
            intro h
            exact hne (hinj h)
          simp [hneq]
        · intro htarget
          simp at htarget
    _ = v target := by
      simp

/--
The target coefficient of the concrete edge-simplex sum is the target
coordinate of the coefficient vector.
-/
theorem edgeSimplexTargetCoefficient_eq
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g) :
    edgeSimplexTargetCoefficient g target v = v target :=
  edgeSimplexTargetCoefficient_eq_of_injective g target v (edgeSimplex_injective g)

/--
Reading the coefficient of the target concrete edge simplex in a chain
equality between signed face terms and the concrete edge-simplex sum
gives the corresponding coordinate of the edge vector.
-/
theorem signedFaceTargetEdgeCoefficient_eq_of_edgeSimplex_sum
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = v target := by
  rw [signedFaceTargetEdgeCoefficient_eq_edgeSimplexTargetCoefficient_of_sum
    g target v Simplex coeff simplex hB]
  exact edgeSimplexTargetCoefficient_eq g target v

/-- Read an explicit target-edge cancellation input as the zero statement. -/
theorem signedFaceTargetEdgeCoefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0) :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0 :=
  hcancel

/--
Scalar target-edge coefficient comparison for a finite signed face sum.

The fields are stated directly for the explicit signed count of those
face terms whose induced one-simplex is the target concrete edge
simplex. The `targetCoeff_eq` field says that reading this coefficient
in the chain equality gives `v target`, and `targetCoeff_zero` is the
remaining geometric assertion that this coefficient vanishes for the
signed face-boundary sum.
-/
structure EdgeBoundarySignedFaceCoefficientComparison
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1))) where
  targetCoeff_eq :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = v target
  targetCoeff_zero :
    signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0

/--
Construct the scalar coefficient comparison data for the target edge
from equality of a signed face-boundary sum with an edge-simplex sum.
-/
theorem edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_coefficient_comparison
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (_hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    Nonempty
      (EdgeBoundarySignedFaceCoefficientComparison
        g target v Simplex coeff simplex) := by
  exact
    ⟨{
      targetCoeff_eq :=
        signedFaceTargetEdgeCoefficient_eq_of_edgeSimplex_sum
          g target v Simplex coeff simplex _hB
      targetCoeff_zero :=
        signedFaceTargetEdgeCoefficient_zero
          g target Simplex coeff simplex hcancel
    }⟩

/--
Finite individual-face coefficient form with combined signed integer
coefficients.

This is the local geometric leaf after each face term has one integer
coefficient rather than nested scalar actions.
-/
theorem edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  obtain ⟨data⟩ :=
    edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_coefficient_comparison
      g target v Simplex coeff simplex hcancel hB
  rw [← data.targetCoeff_eq]
  exact data.targetCoeff_zero

/--
Finite individual-face coefficient form against explicit edge simplex
generators.

This is the local geometric leaf after flattening the finite
two-simplex boundary sum into its signed one-face terms.
-/
theorem edgeChain_sum_singular_boundary_face_terms_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
        (Finset.univ : Finset (Fin 3)),
        (coeff si.1 * ((-1 : ℤ) ^ (si.2 : ℕ))) •
          (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) =
        (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
        refine Finset.sum_congr rfl ?_
        intro si _hsi
        rw [mul_zsmul]
    _ = ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1) := hB

/--
Finite face-sum coefficient form against explicit edge simplex
generators.

This is the local geometric leaf after expanding the right-hand edge
chains to the singular one-simplices that generate them.
-/
theorem edgeChain_sum_singular_boundary_faces_edgeSimplex_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1)) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_face_terms_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
          (Finset.univ : Finset (Fin 3)),
          coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
        symm
        calc
          (∑ s : Simplex, coeff s •
              (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
                (singularChainElement (singularSimplexFace (simplex s) i) :
                  SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
              ∑ s : Simplex, ∑ i : Fin 3,
                coeff s • (((-1 : ℤ) ^ (i : ℕ)) •
                  (singularChainElement (singularSimplexFace (simplex s) i) :
                    SingularChainCoproduct (Polygon4g (g + 1)) 1)) := by
              refine Finset.sum_congr rfl ?_
              intro s _hs
              exact (Finset.sum_zsmul
                (fun i : Fin 3 =>
                  ((-1 : ℤ) ^ (i : ℕ)) •
                    (singularChainElement (singularSimplexFace (simplex s) i) :
                      SingularChainCoproduct (Polygon4g (g + 1)) 1))
                Finset.univ (coeff s)).symm
          _ = (∑ si ∈ (Finset.univ : Finset Simplex) ×ˢ
                  (Finset.univ : Finset (Fin 3)),
                coeff si.1 • (((-1 : ℤ) ^ (si.2 : ℕ)) •
                  (singularChainElement (singularSimplexFace (simplex si.1) si.2) :
                    SingularChainCoproduct (Polygon4g (g + 1)) 1))) := by
              rw [← Finset.sum_product']
    _ = ∑ e : Fin (2 * (g + 1)), v e •
          (singularChainElement (edgeSimplex g e) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1) := hB

/--
Finite face-sum coefficient form of edge-chain singular-boundary
independence.

This is the local geometric leaf after expanding each singular
two-simplex boundary into its alternating face sum.
-/
theorem edgeChain_sum_singular_boundary_faces_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace (simplex s) i) :
              SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_faces_edgeSimplex_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  simpa [edgeChain] using hB

/--
Finite-simplex coefficient form of edge-chain singular-boundary
independence.

This is the local finite-support leaf behind the concrete singular
two-boundary statement: a finite integral combination of singular
two-simplex boundaries cannot equal a nonzero target edge combination.
-/
theorem edgeChain_sum_singular_boundary_decomposition_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (Simplex : Type) [Fintype Simplex]
    (coeff : Simplex → ℤ)
    (simplex : Simplex → C(stdSimplex ℝ (Fin 3), Polygon4g (g + 1)))
    (hcancel :
      signedFaceTargetEdgeCoefficient g target Simplex coeff simplex = 0)
    (hB :
      (∑ s : Simplex, coeff s •
          ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom
            (singularChainElement (simplex s))) =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  apply
    edgeChain_sum_singular_boundary_faces_scalar_coefficient_zero
      g target v Simplex coeff simplex hcancel
  calc
    (∑ s : Simplex, coeff s •
        (∑ i : Fin 3, ((-1 : ℤ) ^ (i : ℕ)) •
          (singularChainElement (singularSimplexFace (simplex s) i) :
            SingularChainCoproduct (Polygon4g (g + 1)) 1))) =
        ∑ s : Simplex, coeff s •
          ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom
            (singularChainElement (simplex s)) := by
        refine Finset.sum_congr rfl ?_
        intro s _hs
        rw [singularChainElement_boundary_decomposition
          (Polygon4g (g + 1)) 1 (simplex s)]
    _ = ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e := hB

/--
Architectural axiom: edge-chain singular-boundary independence.

If a singular 2-chain `B` has boundary
`∂B = ∑ e, v e • edgeChain g e`, then each target coordinate of `v`
vanishes. This is the homological fact that the concrete polygon edge
chains form the free basis of `H₁ (Polygon4g (g + 1); ℤ)`, specialized to
one coordinate.

This replaces the previously circular substrate axiom
`signedFaceTargetEdgeCoefficient_zero_of_singular_boundary`: `d ∘ d = 0`
only proves the signed face one-chain is a cycle, not that a particular
edge coefficient in that cycle is zero.
-/
theorem edgeChain_sum_singular_boundary_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (B : (singularChainComplexZ (Polygon4g (g + 1))).X 2)
    (hB :
      ((singularChainComplexZ (Polygon4g (g + 1))).d 2 1).hom B =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  sorry

/--
Pointwise coefficient form of edge-chain boundary independence.

This is the remaining scalar-coordinate geometric input needed for
edge independence: if a singular two-boundary is a finite sum of
concrete edge chains, then the coefficient of each target edge is zero.
-/
theorem edgeChain_sum_boundary_scalar_coefficient_zero
    (g : ℕ) (target : Fin (2 * (g + 1)))
    (v : Polygon4gAbelianization g)
    (B : ((singularChainComplexZ (Polygon4g (g + 1))).sc 1).X₁)
    (hB :
      ModuleCat.Hom.hom (((singularChainComplexZ (Polygon4g (g + 1))).sc 1).f) B =
        ∑ e : Fin (2 * (g + 1)), v e • edgeChain g e) :
    v target = 0 := by
  obtain ⟨B', hB'⟩ :=
    hurewicz_singularBoundary_eq_sc_f (Polygon4g (g + 1)) B
  exact
    edgeChain_sum_singular_boundary_scalar_coefficient_zero
      g target v B' (hB' ▸ hB)


end JacobianChallenge.Periods
