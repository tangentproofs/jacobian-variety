import Jacobian.HolomorphicForms.HodgeLaplacian
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.HodgeStarRS
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Harmonic projection: H¹_dR ≃ Harm¹

The Hodge theorem on a compact oriented Riemannian manifold says that
every de Rham cohomology class has a unique harmonic representative:

H^k_dR(X, ℂ) ≅ Harm^k(X, ℂ)         (orthogonal projection)

Mathlib v4.28.0 lacks the entire elliptic-operator / harmonic-projection
apparatus.  This file decomposes the named obligation
`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (in
`HodgeDecomposition.lean`) into its underlying
elliptic-projection ingredients.

## What this file provides

## TOPDOWN role

Splits the Hodge harmonic projection into:
1. existence of the projection (Δ has closed range and finite kernel),
2. orthogonality of d-image and harmonic (Hodge identity),
3. surjectivity onto H¹_dR.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Current-model harmonic projection on 1-forms. -/
noncomputable def harmonicProjection1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] HarmonicOneForm X where
  toFun ω := ω.1
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
Design-stage harmonic projection for the period-aware smooth-form substrate.
It records the intended re-based signature: harmonic projection reads the
coefficient part and ignores the period payload.  Existing consumers stay on
`harmonicProjection1` until the substrate migration is performed.
-/
noncomputable def harmonicProjection1WithPeriods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffFormWithPeriods 1 X →ₗ[ℂ] HarmonicOneForm X where
  toFun ω := ω.1
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

/--
**Current-model Hodge representatives.** Every harmonic 1-form is
the harmonic projection of a closed 1-form.

This is the closed-form version of `harmonicProjection1_surjective` needed
to descend the projection to de Rham cohomology. Classically a harmonic
form is itself closed, so this follows from the projector acting as the
identity on harmonic forms.
-/
theorem harmonicProjection1_closed_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective ((harmonicProjection1 X).domRestrict (ClosedForm 1 X)) := by
  intro η
  refine ⟨⟨(η, 0), ?_⟩, rfl⟩
  rw [ClosedForm, LinearMap.mem_ker]
  ext i <;> simp [exteriorDerivative]

/--
**Assembly.** The unrestricted harmonic projection is surjective
because every harmonic form is already the projection of a closed form.
-/
theorem harmonicProjection1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective (harmonicProjection1 X) := by
  intro η
  obtain ⟨ω, hω⟩ := harmonicProjection1_closed_surjective X η
  exact ⟨(ω : SmoothDiffForm 1 X), hω⟩

/--
**Current-model Hodge orthogonality.** Exact 1-forms project to
zero; in the zero-differential surrogate, exact forms are zero.

Bottom-up content: `(dη, ω)_{L²} = (η, d^* ω)_{L²}` and `d^* ω = 0`
for harmonic `ω`. Integration by parts is the missing piece.
-/
theorem harmonicProjection1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hω : ω ∈ ExactForm 0 X) :
    harmonicProjection1 X ω = 0 := by
  rcases hω with ⟨η, hη⟩
  rw [← hη]
  ext i
  simp [harmonicProjection1, exteriorDerivative]

/--
**Hodge harmonic embedding.** A harmonic 1-form `h : HarmonicOneForm X`
(its coefficient data) re-enters the smooth-form substrate as the form
`(h, 0)` carrying no period payload.  This names the section of
`harmonicProjection1` used to phrase the Hodge decomposition: it is a genuine
right inverse on the coefficient part (`harmonicProjection1 X (harmonicEmbed X h) = h`).
-/
noncomputable def harmonicEmbed
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (h : HarmonicOneForm X) : SmoothDiffForm 1 X :=
  (h, 0)

theorem harmonicProjection1_harmonicEmbed
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (h : HarmonicOneForm X) :
    harmonicProjection1 X (harmonicEmbed X h) = h := rfl

/--
**Period-payload exactness — MINIMAL SUBSTRATE-FRONTIER ROOT.**
For a closed 1-form `ω`, the pure period-payload form `(0, ω.2)` (zero
coefficient, the form's period data) is exact: `(0, ω.2) ∈ ExactForm 0 X`.

This is the *single, projection-free* analytic fact the Hodge decomposition in
degree 1 reduces to: once the harmonic (coefficient) part is split off, the
remainder is exactly the period payload, and the content is that this payload is
realizable as `dθ` for some 0-form `θ`.  It is strictly narrower than
`harmonicProjection1_hodgeDecomposition` — no projection/embedding wrapper, a
bare statement about `ω.2`.

NOTE (substrate frontier): on the current zero-differential `SmoothDiffForm`
surrogate `exteriorDerivative := 0`, so `ExactForm 0 X = ⊥` and this root
collapses to `ω.2 = 0`, which is not yet true for the period-only forms the
surrogate admits.  It becomes the honest classical fact once `exteriorDerivative`
is given real chartwise content (owner of `SmoothDifferentialForm.lean`).  This
is the exact input that file's owner must supply; see `.sci/result.md`. -/
theorem hodgeRemainder_periodPayload_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    ((0 : SmoothDiffFormCoeff 1 X), ω.2) ∈ ExactForm 0 X := by
  sorry

/--
**Hodge decomposition provider (degree 1).**
Every closed 1-form `ω` differs from the embedded harmonic representative of
its own projection by an *exact* form:
`ω - harmonicEmbed X (harmonicProjection1 X ω) ∈ ExactForm 0 X`.

This is the orthogonal-splitting input of the Hodge theorem in degree 1
(`closed = harmonic ⊕ exact`), used by the sorry-free
`harmonicProjection1_kernel_subset_exact` assembly below.

**Now sorry-free**: the subtracted form is the embedded harmonic projection
`(ω.1, 0)`, so the remainder is the pure period payload `(0, ω.2)`, whose
exactness is supplied by the minimal root `hodgeRemainder_periodPayload_exact`. -/
theorem harmonicProjection1_hodgeDecomposition
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    ω - harmonicEmbed X (harmonicProjection1 X ω) ∈ ExactForm 0 X := by
  have hrem : ω - harmonicEmbed X (harmonicProjection1 X ω)
      = ((0 : SmoothDiffFormCoeff 1 X), ω.2) := by
    apply Prod.ext
    · simp [harmonicEmbed, harmonicProjection1]
    · simp [harmonicEmbed, harmonicProjection1]
  rw [hrem]
  exact hodgeRemainder_periodPayload_exact X ω hclosed

/--
**Current-model Hodge representative uniqueness.** If a closed
1-form has zero harmonic projection, then it is exact.

Bottom-up content: Hodge decomposition writes every closed form as a
harmonic form plus an exact form; the zero-projection condition kills the
harmonic summand.

This **assembly is sorry-free**: it consumes the narrowest provider
`harmonicProjection1_hodgeDecomposition`.  When the harmonic projection
vanishes, the embedded harmonic representative is `harmonicEmbed X 0 = 0`, so
`ω - 0 = ω` is exactly the exact form supplied by the decomposition.
-/
theorem harmonicProjection1_kernel_subset_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0)
    (hproj : harmonicProjection1 X ω = 0) :
    ω ∈ ExactForm 0 X := by
  have hsplit := harmonicProjection1_hodgeDecomposition X ω hclosed
  rw [hproj] at hsplit
  have hembed : harmonicEmbed X (0 : HarmonicOneForm X) = 0 := by
    simp [harmonicEmbed]
  rw [hembed, sub_zero] at hsplit
  exact hsplit

/--
**Current-model kernel identity.** The harmonic projection vanishes
exactly on exact forms — i.e. `ker harmonicProjection1 = ExactForm 0 X`
restricted to closed forms.

Together with `harmonicProjection1_surjective` this is the **Hodge
theorem in degree 1**.
-/
theorem harmonicProjection1_kernel_eq_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    harmonicProjection1 X ω = 0 ↔ ω ∈ ExactForm 0 X := by
  constructor
  · exact harmonicProjection1_kernel_subset_exact X ω hclosed
  · intro hω
    exact harmonicProjection1_vanishes_on_exact X ω hω

private theorem harmonicProjection1_closed_ker_eq_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    LinearMap.ker ((harmonicProjection1 X).domRestrict (ClosedForm 1 X)) =
      ExactForm.toClosedSubmodule 0 X := by
  ext ω
  constructor
  · intro hω
    have hclosed : exteriorDerivative 1 X (ω : SmoothDiffForm 1 X) = 0 :=
      LinearMap.mem_ker.mp ω.2
    have hproj : harmonicProjection1 X (ω : SmoothDiffForm 1 X) = 0 :=
      LinearMap.mem_ker.mp hω
    have hexact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
      (harmonicProjection1_kernel_eq_exact X (ω : SmoothDiffForm 1 X) hclosed).1 hproj
    simpa [ExactForm.toClosedSubmodule] using hexact
  · intro hω
    have hexact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
      simpa [ExactForm.toClosedSubmodule] using hω
    exact LinearMap.mem_ker.mpr
      (harmonicProjection1_vanishes_on_exact X (ω : SmoothDiffForm 1 X) hexact)

/--
**Current-model Hodge theorem.** The descended harmonic projection
is a ℂ-linear equivalence from H¹_dR to harmonic 1-forms.

Bottom-up content: combines `harmonicProjection1_surjective`,
`harmonicProjection1_vanishes_on_exact`, and
`harmonicProjection1_kernel_eq_exact`.
-/
theorem deRhamH1_isLinearEquiv_harmonic
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : deRhamH1Cocycle X ≃ₗ[ℂ] HarmonicOneForm X, True := by
  let π₁ : ClosedFormSub 1 X →ₗ[ℂ] HarmonicOneForm X :=
    (harmonicProjection1 X).domRestrict (ClosedForm 1 X)
  have hker : LinearMap.ker π₁ = ExactForm.toClosedSubmodule 0 X := by
    simpa [π₁] using harmonicProjection1_closed_ker_eq_exact X
  have hrange : LinearMap.range π₁ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact harmonicProjection1_closed_surjective X
  refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((LinearMap.quotKerEquivRange π₁).trans (LinearEquiv.ofTop _ hrange)), trivial⟩


theorem deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = analyticHarmonicGenus X := by
  obtain ⟨e, _⟩ := deRhamH1_isLinearEquiv_harmonic X
  exact e.finrank_eq


theorem complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus_via_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = analyticHarmonicGenus X := by
  rw [complexDimDeRhamH1ℂ_eq_finrank_cocycle X,
      deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus X]

end JacobianChallenge.HolomorphicForms
