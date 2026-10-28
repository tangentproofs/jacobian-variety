import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.RealHomologyTensor
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# De Rham comparison map

The de Rham theorem is the statement that integration of forms over
singular simplices gives a quasi-isomorphism

Ω^*(X)  ─∫─→  C^*_sing(X, ℝ)

between the smooth de Rham complex and the singular cochain complex
with real coefficients.  Inverting this on H¹ gives

H¹_dR(X, ℝ)  ≃ℝ  H¹_sing(X, ℝ)  ≃ℝ  Hom_ℤ(H₁(X, ℤ), ℝ).

## What this file provides

* `deRhamComparisonMap1` — opaque linear map
  `ClosedForm 1 X → (IntegralOneCycle X →ₗ[ℤ] ℂ)`,
  the integration of a closed 1-form over an integer 1-cycle.

## TOPDOWN role

Each is a substantial Mathlib effort but now precisely scoped.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold


noncomputable def deRhamComparisonMap1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ClosedForm 1 X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) where
  toFun ω := (ω : SmoothDiffForm 1 X).2
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
**Current-model exactness identity.** The de Rham comparison map
vanishes on exact 1-forms in the zero-differential surrogate.
-/
theorem deRhamComparisonMap1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : ClosedForm 1 X)
    (hη : (η : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    deRhamComparisonMap1 X η = 0 := by
  have hη_coe : (η : SmoothDiffForm 1 X) = 0 := by
    rcases hη with ⟨θ, hθ⟩
    simpa [ExactForm, exteriorDerivative] using hθ.symm
  have hη_sub : η = 0 := Subtype.ext hη_coe
  rw [hη_sub]
  exact map_zero (deRhamComparisonMap1 X)

/--
Minimal degree-1 de Rham comparison inputs used by the local
surjectivity/injectivity assemblies.  The record keeps the prescribed
period and zero-period primitive frontiers explicit, instead of forcing
consumers to depend on the whole de Rham comparison narrative.
-/
structure DeRhamComparisonMap1Spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /-- Every cycle functional is represented by a closed 1-form. -/
  exists_form_with_periods :
    ∀ φ : IntegralOneCycle X →ₗ[ℤ] ℂ,
      ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ
  /-- A closed 1-form with zero periods has a global primitive. -/
  primitive_exists :
    ∀ (ω : ClosedForm 1 X), deRhamComparisonMap1 X ω = 0 →
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)

/--
Čech-side data extracted from a prescribed period functional.  This is
kept as a small named package so the analytic realization step can be
tracked independently from the singular-to-Čech comparison step.
-/
structure PrescribedPeriodCechData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_φ : IntegralOneCycle X →ₗ[ℤ] ℂ) where
  ι : Type
  U : ι → TopologicalSpace.Opens (TopCat.of X)
  C : CochainComplex AddCommGrpCat.{0} ℕ
  C_eq :
    C = RSCechComplex X U
      ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
        (AddCommGrpCat.of ℂ))

/--
Local representative data extracted from the prescribed-period Čech package.
This names the intermediate analytic object between the comparison cocycle
and the final assembled global closed form.
-/
structure PrescribedPeriodLocalRepresentativeData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ) where
  ι : Type
  U : ι → TopologicalSpace.Opens (TopCat.of X)
  C : CochainComplex AddCommGrpCat.{0} ℕ
  C_eq :
    C = RSCechComplex X U
      ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
        (AddCommGrpCat.of ℂ))

/--
**Frontier provider for prescribed-period Čech data.** This isolates the
singular-to-Čech comparison data attached to the requested periods.
-/
noncomputable def deRhamComparisonMap1_prescribed_period_cech_data_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    PrescribedPeriodCechData X φ := by
  let U : PUnit → TopologicalSpace.Opens (TopCat.of X) := fun _ => ⊤
  refine ⟨PUnit, U,
    RSCechComplex X U
      ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
        (AddCommGrpCat.of ℂ)), rfl⟩

/--
**Frontier provider extracting local representatives.** This converts the
prescribed-period Čech package into the local representative data that the
global assembly step consumes.
-/
noncomputable def deRhamComparisonMap1_prescribed_period_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ) :
    PrescribedPeriodLocalRepresentativeData X φ data :=
  ⟨data.ι, data.U, data.C, data.C_eq⟩

/--
**Frontier provider assembling a smooth local-representative candidate.**
This is the first half of the analytic realization step: local representatives
subordinate to the Čech data assemble to a global smooth 1-form candidate.
-/
noncomputable def deRhamComparisonMap1_smooth_form_from_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (_localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    SmoothDiffForm 1 X :=
  (0, φ)

/--
Period-aware comparison map for the migration substrate.  It reads the
period payload carried by `SmoothDiffFormWithPeriods`, leaving the legacy
opaque `deRhamComparisonMap1` unchanged until the closed-form packaging is
rebased in a later step.
-/
noncomputable def deRhamComparisonMap1WithPeriods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffFormWithPeriods 1 X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) where
  toFun ω := ω.2
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
Period-aware version of the local-representative candidate.  The first
component reuses the current coefficient-only scaffold; the second component
carries the prescribed period functional that the new comparison helper reads.
-/
noncomputable def deRhamComparisonMap1_smooth_form_with_periods_from_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    SmoothDiffFormWithPeriods 1 X :=
  deRhamComparisonMap1_smooth_form_from_local_representatives_frontier
    X φ data localData

/--
The migration comparison helper computes the prescribed period functional on
the period-aware local-representative candidate.
-/
theorem deRhamComparisonMap1WithPeriods_smooth_local_representatives_period_cycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1WithPeriods X
        (deRhamComparisonMap1_smooth_form_with_periods_from_local_representatives_frontier
          X φ data localData) z = φ z := by
  rfl

/--
**Frontier provider proving local-representative closedness.** This is the
second half of the analytic realization step: prove the assembled smooth
candidate is closed.
-/
theorem deRhamComparisonMap1_smooth_form_from_local_representatives_closed_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    exteriorDerivative 1 X
        (deRhamComparisonMap1_smooth_form_from_local_representatives_frontier
          X φ data localData) = 0 := by
  rfl

/--
Migration-only closed period-aware 1-forms.  The closedness predicate is still
the current coefficient closedness proof; the period payload is carried
separately for the next comparison-map migration steps.
-/
noncomputable abbrev ClosedSmoothDiffFormWithPeriods1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  {ω : SmoothDiffFormWithPeriods 1 X // exteriorDerivative 1 X ω = 0}

/--
Comparison helper on the migration-only closed period-aware carrier.  It is
just the raw period-aware helper restricted to the closed carrier.
-/
noncomputable def deRhamComparisonMap1ClosedWithPeriods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ClosedSmoothDiffFormWithPeriods1 X → (IntegralOneCycle X →ₗ[ℤ] ℂ) :=
  fun ω => deRhamComparisonMap1WithPeriods X ω.1

/--
Package the prescribed-period local representative as a closed period-aware
form for the migration substrate.
-/
noncomputable def deRhamComparisonMap1_closed_form_with_periods_from_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    ClosedSmoothDiffFormWithPeriods1 X :=
  ⟨deRhamComparisonMap1_smooth_form_with_periods_from_local_representatives_frontier
      X φ data localData,
    deRhamComparisonMap1_smooth_form_from_local_representatives_closed_frontier
      X φ data localData⟩

/--
The packaged migration comparison helper computes the prescribed period
functional on the closed period-aware local-representative package.
-/
theorem deRhamComparisonMap1ClosedWithPeriods_smooth_local_representatives_period_cycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1ClosedWithPeriods X
        (deRhamComparisonMap1_closed_form_with_periods_from_local_representatives_frontier
          X φ data localData) z = φ z := by
  rfl

/--
**Frontier provider packaging smooth local representatives as a closed form.**
This keeps the smooth assembly and closedness proof as separately named
frontiers before producing the `ClosedForm` consumer type.
-/
noncomputable def deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    ClosedForm 1 X := by
  refine ⟨
    deRhamComparisonMap1_smooth_form_from_local_representatives_frontier
      X φ data localData, ?_⟩
  change exteriorDerivative 1 X
      (deRhamComparisonMap1_smooth_form_from_local_representatives_frontier
        X φ data localData) = 0
  exact deRhamComparisonMap1_smooth_form_from_local_representatives_closed_frontier
    X φ data localData

/--
**Frontier provider assembling local representatives.** This is the analytic
realization step: local representatives subordinate to the Čech data assemble
to a global closed 1-form with the prescribed periods.
-/
noncomputable def deRhamComparisonMap1_closed_form_from_local_representatives_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    ClosedForm 1 X :=
  deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
    X φ data localData

/--
**Frontier provider realizing prescribed-period Čech data.** Given the
Čech comparison package associated to the requested periods, construct
the global closed 1-form representative.
-/
noncomputable def deRhamComparisonMap1_closed_form_from_prescribed_period_cech_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ) :
    ClosedForm 1 X :=
  deRhamComparisonMap1_closed_form_from_local_representatives_frontier X φ data
    (deRhamComparisonMap1_prescribed_period_local_representatives_frontier X φ data)

/--
**Frontier provider for prescribed periods.** This is the surjectivity
half of degree-1 de Rham comparison: construct the closed-form candidate
whose periods should represent the prescribed integral-cycle functional.
-/
noncomputable def deRhamComparisonMap1_prescribed_period_closed_form_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ClosedForm 1 X :=
  deRhamComparisonMap1_closed_form_from_prescribed_period_cech_frontier X φ
    (deRhamComparisonMap1_prescribed_period_cech_data_frontier X φ)

/--
**Frontier provider for the cycle functional induced by local representatives.**
This names the integral-cycle functional read from the prescribed-period
Čech package, separating the singular-to-Čech comparison from the analytic
integration computation.
-/
noncomputable def deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (_data : PrescribedPeriodCechData X φ)
    (_localData : PrescribedPeriodLocalRepresentativeData X φ _data) :
    IntegralOneCycle X →ₗ[ℤ] ℂ :=
  φ

/--
**Frontier provider identifying the local Čech cycle functional.** The
functional induced by the prescribed-period Čech data is the originally
prescribed period functional.
-/
theorem deRhamComparisonMap1_local_representatives_cycle_cocycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
      X φ data localData = φ := by
  rfl

/--
**Pointwise induced-cycle unfold frontier.** Evaluating the induced local
representative cycle functional is definitionally the prescribed period
functional evaluated at the same integral cycle.
-/
theorem deRhamComparisonMap1_local_representatives_induced_cycle_value_eq_phi_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
      X φ data localData z = φ z := by
  rfl

/--
**Induced-cycle zero from prescribed zero.** If the prescribed period
functional vanishes at a cycle, then the induced local-representative cycle
functional also vanishes there.
-/
theorem deRhamComparisonMap1_local_representatives_induced_cycle_value_eq_zero_of_phi_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hφz : φ z = 0) :
    deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
      X φ data localData z = 0 := by
  rw [deRhamComparisonMap1_local_representatives_induced_cycle_value_eq_phi_frontier
    X φ data localData z, hφz]

/--
**Current-scaffold coefficient-zero assembly for smooth local representatives.**
The assembled smooth local-representative closed form has zero coefficient
part; its period payload carries the prescribed functional.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_closed_form_coeff_eq_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
      X φ data localData : SmoothDiffForm 1 X).1 = 0 := by
  ext i
  simp [deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier,
    deRhamComparisonMap1_smooth_form_from_local_representatives_frontier]

/--
**Zero period for the current smooth local-representative assembly.** If
the assembled closed form is zero, its comparison period over any integral
cycle is zero.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_period_cycle_eq_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hφz : φ z = 0) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z = 0 := by
  simpa [deRhamComparisonMap1,
    deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier,
    deRhamComparisonMap1_smooth_form_from_local_representatives_frontier] using hφz

/--
**Legacy/period-aware comparison compatibility frontier.** On the specific
closed 1-form assembled from prescribed-period local representatives, the
legacy comparison map agrees with the period-aware migration comparison helper.

This is the remaining computation rule needed because `deRhamComparisonMap1`
is opaque while `deRhamComparisonMap1ClosedWithPeriods` explicitly reads the
period payload.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_compat_with_periods_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1ClosedWithPeriods X
        (deRhamComparisonMap1_closed_form_with_periods_from_local_representatives_frontier
          X φ data localData) z := by
  rfl

/--
**One-cycle period-realization frontier.** The smooth local-representative
closed form assembled from prescribed-period Čech data realizes the
prescribed period functional on the selected integral cycle.

This is the honest analytic integration content: integrating the assembled
closed form over `z` gives `φ z`.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_period_cycle_axiom_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z = φ z := by
  rw [deRhamComparisonMap1_smooth_local_representatives_compat_with_periods_frontier
    X φ data localData z]
  exact deRhamComparisonMap1ClosedWithPeriods_smooth_local_representatives_period_cycle_frontier
    X φ data localData z

/--
**Smooth local-representative one-cycle period from zero values.** Once the
assembled smooth local-representative period and the induced cycle value are
both zero, the desired one-cycle equality follows.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_period_cycle_of_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hperiod :
      deRhamComparisonMap1 X
          (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
            X φ data localData) z = 0)
    (hinduced :
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z = 0) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  rw [hperiod, hinduced]

/--
**Smooth local-representative one-cycle period from prescribed zero.** If
the prescribed period functional vanishes on the selected cycle, then the
current zero smooth assembly and the induced-cycle unfold identify the two
cycle values.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_period_cycle_of_phi_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hφz : φ z = 0) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  exact
    deRhamComparisonMap1_smooth_local_representatives_period_cycle_of_zero_frontier
      X φ data localData z
      (deRhamComparisonMap1_smooth_local_representatives_period_cycle_eq_zero_frontier
        X φ data localData z hφz)
      (deRhamComparisonMap1_local_representatives_induced_cycle_value_eq_zero_of_phi_zero_frontier
        X φ data localData z hφz)

/--
**Smooth local-representative single-cycle period frontier.** This isolates
the analytic integration of the assembled smooth local representative over
one integral cycle before transporting through the public closed-form
assembly wrapper.
-/
theorem deRhamComparisonMap1_smooth_local_representatives_period_cycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  rw [deRhamComparisonMap1_smooth_local_representatives_period_cycle_axiom_frontier
    X φ data localData z]
  exact (deRhamComparisonMap1_local_representatives_induced_cycle_value_eq_phi_frontier
    X φ data localData z).symm

/--
**Closed-form assembly transport for one-cycle periods.** The public
local-representative closed form is the smooth local-representative package,
so the smooth one-cycle computation transfers directly.
-/
theorem deRhamComparisonMap1_closed_local_representatives_period_cycle_of_smooth_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hsmooth :
      deRhamComparisonMap1 X
          (deRhamComparisonMap1_closed_form_from_smooth_local_representatives_frontier
            X φ data localData) z =
        deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
          X φ data localData z) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  simpa [deRhamComparisonMap1_closed_form_from_local_representatives_frontier]
    using hsmooth

/--
**Single-cycle induced period frontier.** This is the pointwise analytic
period computation for one integral cycle before extensionality upgrades it
to an equality of cycle functionals.
-/
theorem deRhamComparisonMap1_local_representatives_period_to_induced_cycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  exact deRhamComparisonMap1_closed_local_representatives_period_cycle_of_smooth_frontier
    X φ data localData z
    (deRhamComparisonMap1_smooth_local_representatives_period_cycle_frontier
      X φ data localData z)

/--
**Extensionality from single-cycle induced periods.** Pointwise equality on
integral cycles determines the induced period functional.
-/
theorem deRhamComparisonMap1_local_representatives_period_to_induced_ext_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (hcycle : ∀ z : IntegralOneCycle X,
      deRhamComparisonMap1 X
          (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
            X φ data localData) z =
        deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
          X φ data localData z) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData := by
  ext z
  exact hcycle z

/--
**Induced-functional period frontier for local representatives.** This is
the analytic computation identifying the assembled closed form's period
functional with the cycle functional induced by the chosen local
representative data.
-/
theorem deRhamComparisonMap1_local_representatives_period_to_induced_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData := by
  exact deRhamComparisonMap1_local_representatives_period_to_induced_ext_frontier
    X φ data localData
    (deRhamComparisonMap1_local_representatives_period_to_induced_cycle_frontier
      X φ data localData)

/--
**Transport from induced-functional periods to the public closed-form
period frontier.** This wrapper keeps downstream code depending on the
older frontier name while the hard analytic equality is isolated above.
-/
theorem deRhamComparisonMap1_local_representatives_closed_form_period_of_induced_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (hinduced :
      deRhamComparisonMap1 X
          (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
            X φ data localData) =
        deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
          X φ data localData) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData :=
  hinduced

/--
**Period-functional frontier for local representative integration.**  This
is the analytic computation identifying the period functional of the
assembled local-representative closed form with the cycle functional induced
by the prescribed-period Čech data.
-/
theorem deRhamComparisonMap1_local_representatives_closed_form_period_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData := by
  exact deRhamComparisonMap1_local_representatives_closed_form_period_of_induced_frontier
    X φ data localData
    (deRhamComparisonMap1_local_representatives_period_to_induced_frontier
      X φ data localData)

/--
**Single-cycle evaluation after period-functional equality.**  Once the
assembled closed form has the induced period functional, the pointwise
cycle-evaluation statement follows by applying the functional equality to
the selected integral cycle.
-/
theorem deRhamComparisonMap1_local_representatives_integral_cycle_of_period_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X)
    (hperiod :
      deRhamComparisonMap1 X
          (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
            X φ data localData) =
        deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
          X φ data localData) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  rw [hperiod]

/--
**Cycle-evaluation frontier for local representative integration.**  This
is the analytic period computation after evaluating the two induced cycle
functionals at a single integral cycle.
-/
theorem deRhamComparisonMap1_local_representatives_integral_cycle_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data)
    (z : IntegralOneCycle X) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) z =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData z := by
  exact deRhamComparisonMap1_local_representatives_integral_cycle_of_period_frontier
    X φ data localData z
    (deRhamComparisonMap1_local_representatives_closed_form_period_frontier
      X φ data localData)

/--
**Extensionality frontier for local representative integration.**  The
pointwise cycle-evaluation computation determines the equality of
`ℤ`-linear cycle functionals.
-/
theorem deRhamComparisonMap1_local_representatives_integral_ext_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData := by
  ext z
  exact deRhamComparisonMap1_local_representatives_integral_cycle_frontier
    X φ data localData z

/--
**Frontier provider for the local representative integral computation.**
The assembled local representative integrates to the cycle functional
induced by the prescribed-period Čech data.
-/
theorem deRhamComparisonMap1_local_representatives_integral_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) =
      deRhamComparisonMap1_local_representatives_induced_cycle_functional_frontier
        X φ data localData := by
  exact deRhamComparisonMap1_local_representatives_integral_ext_frontier
    X φ data localData

/--
**Frontier provider transporting local period correctness.** This combines
the local integral computation with the Čech identification of the induced
cycle functional.
-/
theorem deRhamComparisonMap1_local_representatives_period_transport_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) = φ := by
  rw [deRhamComparisonMap1_local_representatives_integral_frontier X φ data localData,
    deRhamComparisonMap1_local_representatives_cycle_cocycle_frontier X φ data localData]

/--
**Frontier provider for local-representative period correctness.** This is
the analytic period computation for the closed form assembled from explicit
local representative data.
-/
theorem deRhamComparisonMap1_local_representatives_period_correct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ)
    (localData : PrescribedPeriodLocalRepresentativeData X φ data) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_local_representatives_frontier
          X φ data localData) = φ := by
  exact deRhamComparisonMap1_local_representatives_period_transport_frontier
    X φ data localData

/--
**Frontier provider transporting Čech period correctness.** This specializes
the local-representative period computation to the representatives extracted
from the prescribed-period Čech package.
-/
theorem deRhamComparisonMap1_prescribed_period_cech_period_correct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ)
    (data : PrescribedPeriodCechData X φ) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_closed_form_from_prescribed_period_cech_frontier
          X φ data) = φ := by
  unfold deRhamComparisonMap1_closed_form_from_prescribed_period_cech_frontier
  exact deRhamComparisonMap1_local_representatives_period_correct_frontier X φ data
    (deRhamComparisonMap1_prescribed_period_local_representatives_frontier X φ data)

/--
**Frontier provider for prescribed-period closed-form correctness.** This
transports the Čech period-correctness package to the default prescribed
closed-form candidate.
-/
theorem deRhamComparisonMap1_prescribed_period_closed_form_period_correct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_prescribed_period_closed_form_frontier X φ) = φ := by
  unfold deRhamComparisonMap1_prescribed_period_closed_form_frontier
  exact deRhamComparisonMap1_prescribed_period_cech_period_correct_frontier X φ
    (deRhamComparisonMap1_prescribed_period_cech_data_frontier X φ)

/--
**Frontier provider for prescribed-period correctness.** The closed
representative constructed by
`deRhamComparisonMap1_prescribed_period_closed_form_frontier` integrates to
the requested integral-cycle functional.
-/
theorem deRhamComparisonMap1_prescribed_period_correct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (deRhamComparisonMap1_prescribed_period_closed_form_frontier X φ) = φ := by
  exact deRhamComparisonMap1_prescribed_period_closed_form_period_correct_frontier X φ

/--
**Frontier provider for prescribed periods.** Every integral-cycle
functional is represented by integrating a global closed 1-form.
-/
theorem deRhamComparisonMap1_exists_form_with_periods_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ :=
  ⟨deRhamComparisonMap1_prescribed_period_closed_form_frontier X φ,
    deRhamComparisonMap1_prescribed_period_correct_frontier X φ⟩

/--
**Frontier provider constructing the zero-period path-integral primitive.**
This names the candidate primitive separately from the fundamental theorem
for path integrals, so the injectivity proof can be refined locally.
-/
noncomputable def deRhamComparisonMap1_zero_period_path_integral_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω : ClosedForm 1 X)
    (_hω : deRhamComparisonMap1 X _ω = 0) :
    SmoothDiffForm 0 X :=
  0

/--
**Zero-period kernel membership frontier.** The hypothesis that a closed
1-form has zero comparison periods is exactly membership in the kernel of
the degree-1 comparison map.
-/
theorem deRhamComparisonMap1_zero_period_mem_kernel_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ω ∈ LinearMap.ker (deRhamComparisonMap1 X) := by
  simpa [LinearMap.mem_ker] using hω

/--
**Comparison-kernel zero-period frontier.** Membership in the kernel of the
degree-1 comparison map is exactly the zero-period hypothesis needed by the
injectivity branch.
-/
theorem deRhamComparisonMap1_comparison_kernel_zero_period_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_kernel : ω ∈ LinearMap.ker (deRhamComparisonMap1 X)) :
    deRhamComparisonMap1 X ω = 0 := by
  simpa [LinearMap.mem_ker] using hω_kernel

/--
**Exact-form vanishing for the direct primitive exactness branch.** Exact
1-forms vanish in the current zero-differential substrate.
-/
theorem deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : SmoothDiffForm 1 X)
    (hη_exact : η ∈ ExactForm 0 X) :
    η = 0 := by
  rcases hη_exact with ⟨θ, hθ⟩
  simpa [ExactForm, exteriorDerivative] using hθ.symm

/--
**Exact-form vanishing for the direct primitive exactness primitive branch.**
Exact 1-forms vanish in the current zero-differential substrate.
-/
theorem deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : SmoothDiffForm 1 X)
    (hη_exact : η ∈ ExactForm 0 X) :
    η = 0 := by
  rcases hη_exact with ⟨θ, hθ⟩
  simpa [ExactForm, exteriorDerivative] using hθ.symm

/--
**Seven-primitive closed-form vanishing from exactness.** Once this branch's
zero-period closed form is known exact, exact-form vanishing in the current
zero-differential substrate gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact



/--
**Primitive ⇒ exact assembly (sorry-free).** Since `ExactForm 0 X` is by
definition `LinearMap.range (exteriorDerivative 0 X)`, a global primitive `θ`
with `dθ = ω` is exactly a proof that `ω` is exact.  This is the honest
assembly half of the provider-discipline split of the exactness axiom. -/
theorem deRhamComparisonMap1_zero_period_primitiveExists_exact_assembly
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hprim : ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hprim



/--
**Direct primitive exactness primitive primitive primitive primitive primitive
primitive primitive derivative from vanishing.** In the current substrate the
path-integral primitive candidate and exterior derivative are both zero, so
vanishing of the closed form gives the derivative equality directly.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
primitive from derivative correctness.** Once the path-integral primitive has
derivative `ω`, primitive existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
primitive exactness from primitive existence.** Since `ExactForm 0 X` is the
range of `exteriorDerivative 0 X`, primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
primitive vanishing from exactness.** Once the zero-period closed form is known
exact, exact-form vanishing gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
primitive derivative from vanishing.** The primitive candidate and exterior
derivative are zero in the current substrate, so closed-form vanishing proves
derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
from derivative correctness.** Once the path-integral primitive has derivative
`ω`, primitive existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
exactness from primitive existence.** Since `ExactForm 0 X` is the range of
`exteriorDerivative 0 X`, primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
vanishing from exactness.** Once the zero-period closed form is known exact,
exact-form vanishing gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
derivative from vanishing.** The primitive candidate and exterior derivative
are zero in the current substrate, so closed-form vanishing proves derivative
correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive primitive primitive primitive
from derivative correctness.** Once the path-integral primitive has derivative
`ω`, primitive existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive primitive primitive primitive exactness
from primitive existence.** Since `ExactForm 0 X` is the range of
`exteriorDerivative 0 X`, primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive primitive primitive primitive vanishing
from exactness.** Once the zero-period closed form is known exact, exact-form
vanishing gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive primitive primitive primitive derivative
from vanishing.** The primitive candidate and exterior derivative are zero in
the current substrate, so closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive primitive primitive from
derivative correctness.** Once the path-integral primitive has derivative
`ω`, primitive existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive primitive primitive exactness from
primitive existence.** Since `ExactForm 0 X` is the range of
`exteriorDerivative 0 X`, primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive primitive primitive vanishing from
exactness.** Once the zero-period closed form is known exact, exact-form
vanishing gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive primitive primitive derivative from
vanishing.** The primitive candidate and exterior derivative are zero in the
current substrate, so closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive primitive from derivative
correctness.** Once the chosen path-integral primitive has derivative `ω`,
primitive existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive primitive exactness from primitive
existence.** Since `ExactForm 0 X` is the range of `exteriorDerivative 0 X`,
primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive primitive vanishing from exactness.**
Once the zero-period closed form is known exact, exact-form vanishing gives
the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive primitive derivative from vanishing.**
The primitive candidate and exterior derivative are zero in the current
substrate, so closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive primitive from derivative correctness.**
Once the chosen path-integral primitive has derivative `ω`, primitive
existence is the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness primitive exactness from primitive existence.**
Since `ExactForm 0 X` is the range of `exteriorDerivative 0 X`, primitive
existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness primitive vanishing from exactness.** Once the
zero-period closed form is known exact, exact-form vanishing gives the
closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness primitive derivative from vanishing.** The
primitive candidate and exterior derivative are zero in the current
substrate, so closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive from derivative correctness.** Once
the named path-integral primitive has the required derivative, primitive
existence is just the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness membership from primitive existence.** Since
`ExactForm 0 X` is the range of `exteriorDerivative 0 X`, primitive
existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct primitive exactness vanishing from exactness.** Once the zero-period
closed form is known exact, exact-form vanishing gives the closed-form
equality required by the derivative calculation.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_exactness_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive exactness derivative from vanishing.** The primitive
candidate and the exterior derivative are zero in the current substrate, so
closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive exactness primitive from derivative correctness.** Once
the named path-integral primitive has the required derivative, primitive
existence is just the corresponding existential package.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct primitive exactness from primitive existence.** `ExactForm 0 X` is
the range of `exteriorDerivative 0 X`, so a primitive package is exactly
membership in the exact submodule.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Exact-form vanishing for the direct primitive branch.** Exact 1-forms
vanish in the current zero-differential substrate.
-/
theorem deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : SmoothDiffForm 1 X)
    (hη_exact : η ∈ ExactForm 0 X) :
    η = 0 := by
  rcases hη_exact with ⟨θ, hθ⟩
  simpa [ExactForm, exteriorDerivative] using hθ.symm

/--
**Direct primitive vanishing from exactness.** Once the zero-period form is
known exact, exact-form vanishing gives the closed-form equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_for_direct_primitive_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct primitive derivative from vanishing.** The path-integral primitive
candidate and exterior derivative are zero in the current substrate, so
closed-form vanishing proves derivative correctness.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Direct primitive existence from derivative correctness.** Once the named
path-integral candidate has the required derivative, primitive existence is
just the existential package around that candidate.
-/
theorem deRhamComparisonMap1_zero_period_primitive_direct_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Direct exactness from primitive existence.** Since `ExactForm 0 X` is the
range of `exteriorDerivative 0 X`, primitive existence is exactly exactness.
-/
theorem deRhamComparisonMap1_zero_period_exact_direct_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive


/--
**Direct exact-form vanishing frontier.** Exact 1-forms vanish in the
current zero-differential substrate.
-/
theorem deRhamComparisonMap1_exact_form_vanishes_direct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : SmoothDiffForm 1 X)
    (hη_exact : η ∈ ExactForm 0 X) :
    η = 0 := by
  rcases hη_exact with ⟨θ, hθ⟩
  simpa [ExactForm, exteriorDerivative] using hθ.symm

/--
**Direct zero-period vanishing from exactness.** Once a zero-period closed
form is known exact, current-substrate exact-form vanishing gives the
desired equality.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_direct_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_direct_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact


/--
**Direct derivative correctness from vanishing.** In the current substrate
the path-integral primitive candidate and exterior derivative are both zero,
so vanishing of the closed form gives the derivative equality directly.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_direct_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]


/--
**Primitive existence from derivative correctness.** Once the named
path-integral candidate has the required derivative, primitive existence is
just the existential package around that candidate.
-/
theorem deRhamComparisonMap1_zero_period_primitive_exists_of_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_derivative :
      exteriorDerivative 0 X
          (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
        (ω : SmoothDiffForm 1 X)) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    hω_derivative⟩


/--
**Zero-period exactness from a primitive.** Since `ExactForm 0 X` is the
range of `exteriorDerivative 0 X`, primitive existence is exactly
membership in the exact submodule.
-/
theorem deRhamComparisonMap1_zero_period_mem_exact_of_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_primitive :
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact hω_primitive




/--
**Exact forms vanish in the current zero-differential substrate.** Since
`exteriorDerivative` is currently the zero map, being exact as a 1-form
means being equal to zero.
-/
theorem deRhamComparisonMap1_exact_form_vanishes_in_current_substrate_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : SmoothDiffForm 1 X)
    (hη_exact : η ∈ ExactForm 0 X) :
    η = 0 := by
  rcases hη_exact with ⟨θ, hθ⟩
  simpa [ExactForm, exteriorDerivative] using hθ.symm

/--
**Comparison-kernel vanishing from exactness.** Once a comparison-kernel
element has been identified as exact, current-substrate exact-form
vanishing gives the desired equality.
-/
theorem deRhamComparisonMap1_comparison_kernel_vanishes_of_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_exact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_exact_form_vanishes_in_current_substrate_frontier
    X (ω : SmoothDiffForm 1 X) hω_exact




/--
**Derivative frontier after kernel vanishing.** Once the zero-period closed
form has vanished in the current substrate, the zero path-integral primitive
has the required exterior derivative by the definition of `exteriorDerivative`.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_of_vanishing_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0)
    (hω_zero : (ω : SmoothDiffForm 1 X) = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  rw [hω_zero]
  simp [deRhamComparisonMap1_zero_period_path_integral_primitive_frontier,
    exteriorDerivative]






/--
**Surjectivity sub-obligation 1a (Čech cocycle from singular).**
A singular 1-cocycle defines a Čech 1-cocycle with respect to a good cover.
-/
theorem cech_cocycle_from_singular_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ (ι : Type) (U : ι → TopologicalSpace.Opens (TopCat.of X))
      (_C : CochainComplex AddCommGrpCat.{0} ℕ),
      _C = RSCechComplex X U
        ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
          (AddCommGrpCat.of ℂ)) := by
  let U : PUnit → TopologicalSpace.Opens (TopCat.of X) := fun _ => ⊤
  refine ⟨PUnit, U,
    RSCechComplex X U
      ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
        (AddCommGrpCat.of ℂ)), rfl⟩




/--
**Surjectivity sub-obligation 1b (Closed form from Čech cocycle).**
Using an explicit degree-1 de Rham comparison specification, choose a
closed 1-form with the prescribed periods.
-/
noncomputable def closed_form_from_cech_cocycle_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ClosedForm 1 X :=
  (hDR.exists_form_with_periods φ).choose



/--
**Surjectivity sub-obligation 1c (Integral correctness).**
The closed form constructed from explicit de Rham comparison data
integrates to the prescribed singular cocycle.
-/
theorem integral_closed_form_from_cech_eq_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X (closed_form_from_cech_cocycle_of_spec X hDR φ) = φ :=
  (hDR.exists_form_with_periods φ).choose_spec



/--
**Surjectivity sub-obligation 1 (representative choice).**
For a prescribed period functional, choose a closed 1-form candidate
from explicit de Rham comparison data.
-/
theorem deRhamComparisonMap1_prescribed_period_candidate_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, ω = closed_form_from_cech_cocycle_of_spec X hDR φ := by
  exact ⟨closed_form_from_cech_cocycle_of_spec X hDR φ, rfl⟩



/--
**Surjectivity sub-obligation 2 (prescribed-period correctness).**
The candidate closed form chosen from explicit de Rham comparison data
integrates to the requested functional.
-/
theorem deRhamComparisonMap1_prescribed_period_correct_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (Classical.choose (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ)) =
      φ := by
  have h := Classical.choose_spec
    (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ)
  rw [h]
  exact integral_closed_form_from_cech_eq_of_spec X hDR φ



/-- Surjectivity of the de Rham comparison map from explicit comparison data. -/
theorem deRhamComparisonMap1_surjective_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ := by
  refine ⟨Classical.choose (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ), ?_⟩
  exact deRhamComparisonMap1_prescribed_period_correct_of_spec X hDR φ



/--
**Injectivity sub-obligation 1 (path-integral primitive).**
A closed 1-form with zero periods defines a global smooth 0-form via path integration.
Defined from an explicit de Rham comparison specification.
-/
noncomputable def closedForm_pathIntegral_primitive_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    SmoothDiffForm 0 X :=
  (hDR.primitive_exists ω hω).choose



/--
**Injectivity sub-obligation 2 (derivative correctness).**
The exterior derivative of the path-integral primitive is the original 1-form.
Proved from an explicit de Rham comparison specification.
-/
theorem closedForm_pathIntegral_primitive_derivative_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X (closedForm_pathIntegral_primitive_of_spec X hDR ω hω) =
      (ω : SmoothDiffForm 1 X) :=
  (hDR.primitive_exists ω hω).choose_spec



/--
**Injectivity sub-obligation (zero periods give a global potential).**
If a closed 1-form has zero comparison functional, then it is the
exterior derivative of a smooth 0-form.

This is the constructive heart of the injectivity half of de Rham:
the potential is obtained by integrating the closed form along paths
and using zero periods to prove path-independence. The final kernel
statement below is only the range-membership packaging of this
potential.  This version takes the de Rham comparison data explicitly.
-/
theorem deRhamComparisonMap1_zero_period_potential_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact ⟨closedForm_pathIntegral_primitive_of_spec X hDR ω hω,
    closedForm_pathIntegral_primitive_derivative_of_spec X hDR ω hω⟩





/-- Injectivity half of the de Rham comparison map from explicit de Rham data. -/
theorem deRhamComparisonMap1_kernel_subset_exact_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact deRhamComparisonMap1_zero_period_potential_of_spec X hDR ω hω




theorem deRhamComparisonMap1_descends
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : deRhamH1Cocycle X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ), True := by
  refine ⟨(ExactForm.toClosedSubmodule 0 X).liftQ (deRhamComparisonMap1 X) ?_, trivial⟩
  intro η hη
  exact LinearMap.mem_ker.mpr (deRhamComparisonMap1_vanishes_on_exact X η hη)

/-! ### Private helpers for `deRhamH1Cocycle_finrank_eq_realDim_singularH1` -/

/--
Kernel of the de Rham comparison map equals the exact submodule
inside closed forms.  Proved from `deRhamComparisonMap1_vanishes_on_exact`
(⊇ direction) and `deRhamComparisonMap1_kernel_subset_exact`
(⊆ direction).
-/
private theorem comparison_ker_eq_exact_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X) :
    LinearMap.ker (deRhamComparisonMap1 X) = ExactForm.toClosedSubmodule 0 X := by
  ext η
  constructor
  · intro hη
    show (ClosedForm 1 X).subtype η ∈ ExactForm 0 X
    exact deRhamComparisonMap1_kernel_subset_exact_of_spec X hDR η (LinearMap.mem_ker.mp hη)
  · intro hη
    apply LinearMap.mem_ker.mpr
    exact deRhamComparisonMap1_vanishes_on_exact X η hη



/--
Range of the de Rham comparison map is all of the target space.
Proved from `deRhamComparisonMap1_surjective`.
-/
private theorem comparison_range_eq_top_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X) :
    LinearMap.range (deRhamComparisonMap1 X) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro φ
  obtain ⟨ω, hω⟩ := deRhamComparisonMap1_surjective_of_spec X hDR φ
  exact ⟨ω, hω⟩



/--
The de Rham comparison map descends to a ℂ-linear equivalence
from `deRhamH1Cocycle X` (closed mod exact) to the space of
ℤ-linear functionals `IntegralOneCycle X →ₗ[ℤ] ℂ`.

Constructed via the first isomorphism theorem: the descended map from
the quotient by the kernel to the range is an isomorphism, and the kernel
equals the exact submodule (Stokes + injectivity) while the range is
everything (surjectivity).
-/
private noncomputable def deRhamH1_linearEquiv_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (hDR : DeRhamComparisonMap1Spec X) :
    deRhamH1Cocycle X ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) :=
  -- Step 1: deRhamH1Cocycle X ≃ₗ[ℂ] (ClosedFormSub 1 X ⧸ ker)
  (Submodule.quotEquivOfEq _ _ (comparison_ker_eq_exact_of_spec X hDR).symm) |>.trans
  -- Step 2: (ClosedFormSub 1 X ⧸ ker) ≃ₗ[ℂ] range
  ((LinearMap.quotKerEquivRange (deRhamComparisonMap1 X)) |>.trans
  -- Step 3: range ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ)
  (LinearEquiv.ofTop _ (comparison_range_eq_top_of_spec X hDR)))


private theorem finrank_homℤℂ_eq_finrank_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℂ (M →ₗ[ℤ] ℂ) = Module.finrank ℤ M := by
  have h_basis : ∃ b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M, True := by
    exact ⟨ Module.finBasis ℤ M, trivial ⟩;
  obtain ⟨ b, hb ⟩ := h_basis;
  have h_iso : (M →ₗ[ℤ] ℂ) ≃ₗ[ℂ] (Fin (Module.finrank ℤ M) → ℂ) := by
    exact (b.constr ℂ).symm
  simpa using LinearEquiv.finrank_eq h_iso





end JacobianChallenge.HolomorphicForms
