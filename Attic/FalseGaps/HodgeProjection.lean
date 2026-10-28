/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/HolomorphicForms/HodgeProjection.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

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
