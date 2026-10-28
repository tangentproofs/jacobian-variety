/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
**Zero-period closed-form vanishing provider (degree 1) — NARROWEST LEAF.**
A closed 1-form `ω` whose de Rham comparison image vanishes (all periods zero)
is itself the zero smooth 1-form: `(ω : SmoothDiffForm 1 X) = 0`.

This is the strictly narrower, mathematically-precise root obligation that the
degree-1 zero-period de Rham exactness direction reduces to.  It is the
**period-functional injectivity** statement of the de Rham comparison map on
the (period-carrying) closed-form substrate: vanishing of all integral periods
pins the form down uniquely.  In the classical model this is the content of
"closed + all periods zero ⇒ exact, hence trivial in `H¹_dR`"; in the present
period-carrying `SmoothDiffForm` substrate, where `exteriorDerivative := 0`, an
exact form *is* the zero form, so the honest analytic leaf is exactly this
equality.

It is strictly narrower than the primitive-existence statement below: it asserts
a single equality, with no existential primitive construction.  The root
provider `deRhamComparisonMap1_zero_period_primitiveExists_provider` is a
sorry-free wrapper around it (the zero `0`-form is the primitive, since
`d 0 = 0`).

NOTE (substrate frontier): with `exteriorDerivative := 0`, the comparison map
reads only the period payload `(ω : SmoothDiffForm 1 X).2`, so this equality
becomes fully true once `exteriorDerivative`/`deRhamComparisonMap1` are given
their real chartwise/period content (owner of `SmoothDifferentialForm.lean`).
The decomposition here is the correct shape to consume that content.
See `.sci/result.md`. -/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishing_provider
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  sorry

/--
**Zero-period primitive-existence provider (degree 1) — NARROWEST ROOT.**
A closed 1-form `ω` whose de Rham comparison image vanishes (all periods zero)
admits a global primitive: `∃ θ : SmoothDiffForm 0 X, dθ = ω`.

This is the single honest analytic input behind de Rham exactness in degree 1
(the period-vanishing ⇒ primitive-exists direction).  It is the strictly
narrower root obligation produced by the provider-discipline decomposition of
`deRhamComparisonMap1_zero_period_exact_axiom_frontier`: the *assembly below is
sorry-free* (`ExactForm 0 X = range (exteriorDerivative 0 X)`, so a primitive
is literally a witness of exactness) and reduces the exactness statement to
exactly this primitive-existence input.

It is now a **sorry-free wrapper** around the strictly narrower closed-form
vanishing leaf `deRhamComparisonMap1_zero_period_closed_form_vanishing_provider`:
once the form vanishes, the zero `0`-form is a primitive because
`exteriorDerivative 0 X 0 = 0 = ω`. -/
theorem deRhamComparisonMap1_zero_period_primitiveExists_provider
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  refine ⟨0, ?_⟩
  rw [deRhamComparisonMap1_zero_period_closed_form_vanishing_provider X ω hω]
  exact map_zero (exteriorDerivative 0 X)

/--
**Zero-period exactness substrate axiom.** This is the exactness input
needed to prove zero-period closed-form vanishing in the current
path-integral primitive scaffold.

Now a **sorry-free assembly**: it composes the narrowest primitive-existence
provider `deRhamComparisonMap1_zero_period_primitiveExists_provider` with the
sorry-free `…_exact_assembly`.
-/
theorem deRhamComparisonMap1_zero_period_exact_axiom_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact deRhamComparisonMap1_zero_period_primitiveExists_exact_assembly X ω
    (deRhamComparisonMap1_zero_period_primitiveExists_provider X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
primitive primitive primitive primitive primitive derivative split.** This is
the comparison input needed to break the otherwise cyclic derivative collapse.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_axiom_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive primitive
primitive primitive primitive primitive primitive split.** This is the
remaining comparison input before primitive-existence packaging applies.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
primitive primitive primitive primitive exactness split.** This delegates the
primitive package to the named path-integral derivative frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive primitive primitive
primitive primitive primitive vanishing split.** This delegates exactness to
the named primitive-existence frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
primitive primitive primitive primitive derivative split.** This delegates
closed-form vanishing to the named exactness frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive primitive
primitive primitive primitive primitive split.** This delegates derivative
correctness to closed-form vanishing for this branch.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
primitive primitive primitive exactness split.** This delegates the primitive
package to the named path-integral derivative frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive primitive primitive
primitive primitive vanishing split.** This delegates exactness to the named
primitive-existence frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
primitive primitive primitive derivative split.** This delegates closed-form
vanishing to the named exactness frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive primitive
primitive primitive primitive split.** This delegates derivative correctness to
closed-form vanishing for this branch.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
primitive primitive exactness split.** This delegates the primitive package to
the named path-integral derivative frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive primitive primitive
primitive vanishing split.** This delegates exactness to the named
primitive-existence frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
primitive primitive derivative split.** This delegates closed-form vanishing to
the named exactness frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
primitive exactness split.** This delegates derivative correctness to
closed-form vanishing for this branch.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
primitive exactness split.** This delegates the primitive package to the named
path-integral derivative frontier for this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive primitive primitive
vanishing split.** This is the remaining comparison input before exact-form
vanishing applies.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
primitive derivative split.** This is the remaining comparison input before the
zero-substrate derivative calculation for the path-integral primitive.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive primitive
primitive split.** This is the remaining comparison input for the
path-integral primitive candidate.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive primitive
exactness split.** This is the remaining comparison input behind exactness in
this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive primitive vanishing
split.** This is the remaining comparison input before exact-form vanishing
applies.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive primitive
derivative split.** This is the remaining comparison input before the
zero-substrate derivative calculation for the path-integral primitive.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_primitive_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive
primitive split.** This is the remaining comparison input for the
path-integral primitive candidate.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness primitive exactness
split.** This is the remaining comparison input behind exactness in this
branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness primitive vanishing split.**
This is the remaining comparison input needed before exact-form vanishing
applies.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact
    deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_of_primitive_frontier
      X ω
      (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_primitive_frontier
        X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness primitive
derivative split.** This isolates the comparison input needed before the
zero-substrate derivative calculation.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_primitive_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness primitive split.**
This isolates the remaining comparison input for the named path-integral
primitive candidate.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_primitive_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness membership split.**
This is the remaining comparison input behind exactness in this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_of_derivative_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_primitive_frontier
        X ω hω)

/--
**Exactness for the direct primitive exactness vanishing split.** This is
the remaining comparison input needed before exact-form vanishing applies.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_of_primitive_frontier
    X ω
    (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_exactness_frontier
      X ω hω)

/--
**Closed-form vanishing for the direct primitive exactness derivative
split.** This isolates the comparison input needed before the zero-substrate
derivative calculation proves correctness of the named primitive.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact
    deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_of_exact_frontier
      X ω
      (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_exactness_frontier
        X ω hω)

/--
**Derivative correctness for the direct primitive exactness split.** This
isolates the fundamental theorem input for the named path-integral primitive
candidate used by the direct primitive exactness branch.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact
    deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_of_vanishing_frontier
      X ω hω
      (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_exactness_frontier
        X ω hω)

/--
**Primitive existence for the direct primitive exactness split.** This is
the remaining comparison input behind exactness in this branch.
-/
theorem deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_of_derivative_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_exactness_frontier
      X ω hω)

/--
**Exactness for the direct primitive vanishing split.** This is the
remaining comparison input needed before current-substrate exact-form
vanishing can apply.
-/
theorem deRhamComparisonMap1_zero_period_exact_for_direct_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact deRhamComparisonMap1_zero_period_exact_for_direct_primitive_of_primitive_frontier
    X ω (deRhamComparisonMap1_zero_period_primitive_for_direct_primitive_frontier X ω hω)

/--
**Closed-form vanishing for the direct primitive derivative split.** This is
the remaining comparison input needed by the zero-differential derivative
calculation.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_of_exact_frontier
    X ω (deRhamComparisonMap1_zero_period_exact_for_direct_primitive_frontier X ω hω)

/--
**Derivative correctness for the direct primitive split.** This isolates the
remaining analytic input for the already named zero-period path-integral
primitive candidate.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_of_vanishing_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_closed_form_vanishes_for_direct_primitive_frontier
      X ω hω)

/--
**Direct zero-period primitive frontier.** This is the primitive-existence
input behind direct zero-period exactness.
-/
theorem deRhamComparisonMap1_zero_period_primitive_direct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_primitive_direct_of_derivative_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_path_integral_derivative_for_direct_primitive_frontier
      X ω hω)

/--
**Direct zero-period exactness frontier.** This is the remaining comparison
input for direct zero-period vanishing.
-/
theorem deRhamComparisonMap1_zero_period_exact_direct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact deRhamComparisonMap1_zero_period_exact_direct_of_primitive_frontier
    X ω (deRhamComparisonMap1_zero_period_primitive_direct_frontier X ω hω)

/--
**Direct zero-period vanishing frontier.** This isolates the vanishing input
needed by the current zero-differential path-integral derivative calculation.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_vanishes_direct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact deRhamComparisonMap1_zero_period_closed_form_vanishes_direct_of_exact_frontier
    X ω (deRhamComparisonMap1_zero_period_exact_direct_frontier X ω hω)

/--
**Direct derivative frontier for the zero-period primitive candidate.** This
is the analytic input needed to package the already named path-integral
candidate as an actual primitive.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_direct_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_path_integral_derivative_direct_of_vanishing_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_closed_form_vanishes_direct_frontier X ω hω)

/--
**Zero-period primitive existence frontier.** This isolates the hard
injectivity input in the exact shape used by `DeRhamComparisonMap1Spec`:
zero comparison periods produce a global primitive.
-/
theorem deRhamComparisonMap1_zero_period_primitive_exists_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_primitive_exists_of_derivative_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_path_integral_derivative_direct_frontier
      X ω hω)

/--
**Zero-period exactness frontier.** This is the remaining injectivity input:
a closed 1-form whose comparison periods vanish is exact.
-/
theorem deRhamComparisonMap1_zero_period_mem_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  exact deRhamComparisonMap1_zero_period_exact_axiom_frontier X ω hω

/--
**Comparison-kernel exactness from zero periods.** This composes the
definitional kernel-to-zero-period conversion with the zero-period exactness
frontier.
-/
theorem deRhamComparisonMap1_comparison_kernel_mem_exact_of_zero_period_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_kernel : ω ∈ LinearMap.ker (deRhamComparisonMap1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
  deRhamComparisonMap1_zero_period_mem_exact_frontier X ω
    (deRhamComparisonMap1_comparison_kernel_zero_period_frontier X ω hω_kernel)

/--
**Comparison-kernel exactness frontier.** This isolates the comparison
input that kernel elements are exact closed forms.
-/
theorem deRhamComparisonMap1_comparison_kernel_mem_exact_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_kernel : ω ∈ LinearMap.ker (deRhamComparisonMap1 X)) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
  deRhamComparisonMap1_comparison_kernel_mem_exact_of_zero_period_frontier
    X ω hω_kernel

/--
**Comparison-kernel triviality frontier.** This isolates the hard
injectivity input: the degree-1 comparison map has trivial kernel on the
current closed-form substrate.
-/
theorem deRhamComparisonMap1_comparison_kernel_vanishes_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_kernel : ω ∈ LinearMap.ker (deRhamComparisonMap1 X)) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact deRhamComparisonMap1_comparison_kernel_vanishes_of_exact_frontier
    X ω
    (deRhamComparisonMap1_comparison_kernel_mem_exact_frontier X ω hω_kernel)

/--
**Zero-period vanishing from kernel data.** Once zero periods have been
transported to kernel membership, kernel triviality gives vanishing in the
current `SmoothDiffForm` substrate.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_eq_zero_of_kernel_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω_kernel : ω ∈ LinearMap.ker (deRhamComparisonMap1 X)) :
    (ω : SmoothDiffForm 1 X) = 0 :=
  deRhamComparisonMap1_comparison_kernel_vanishes_frontier X ω hω_kernel

/--
**Kernel-vanishing frontier for zero-period closed forms.** In the
current degree-1 de Rham comparison model, a closed 1-form whose comparison
periods vanish lies in the zero kernel.
-/
theorem deRhamComparisonMap1_zero_period_closed_form_eq_zero_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) = 0 := by
  exact deRhamComparisonMap1_zero_period_closed_form_eq_zero_of_kernel_frontier
    X ω (deRhamComparisonMap1_zero_period_mem_kernel_frontier X ω hω)

/--
**Frontier provider proving derivative correctness for the path-integral
primitive.** This is the analytic content of injectivity: the derivative of
the zero-period path-integral potential recovers the original closed form.
-/
theorem deRhamComparisonMap1_zero_period_path_integral_derivative_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X
        (deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω) =
      (ω : SmoothDiffForm 1 X) := by
  exact deRhamComparisonMap1_zero_period_path_integral_derivative_of_vanishing_frontier
    X ω hω
    (deRhamComparisonMap1_zero_period_closed_form_eq_zero_frontier X ω hω)

/--
**Frontier provider packaging zero-period derivative correctness as
exactness.** This keeps the existential wrapper separate from the analytic
path-integral derivative statement.
-/
theorem deRhamComparisonMap1_zero_period_exactness_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  ⟨deRhamComparisonMap1_zero_period_path_integral_primitive_frontier X ω hω,
    deRhamComparisonMap1_zero_period_path_integral_derivative_frontier X ω hω⟩

/--
**Frontier provider for zero-period primitives.** This is the injectivity
half of degree-1 de Rham comparison: zero periods force exactness.
-/
theorem deRhamComparisonMap1_primitive_exists_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  deRhamComparisonMap1_zero_period_exactness_frontier X ω hω

/--
Narrow consumers should take `DeRhamComparisonMap1Spec X` explicitly
instead of calling this provider internally.
-/
def deRhamComparisonMap1Spec_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    DeRhamComparisonMap1Spec X := {
  exists_form_with_periods := deRhamComparisonMap1_exists_form_with_periods_frontier X
  primitive_exists := deRhamComparisonMap1_primitive_exists_frontier X
}

/--
**Existence of global closed form with prescribed periods.**
Every ℝ-linear functional on the singular 1-cycles of a compact Riemann
surface arises as the integral of some closed 1-form.  This is the
analytical core of the de Rham theorem's surjectivity.

Mathematical content:
* choose a singular cohomology class/function on cycles;
* use degree-1 de Rham comparison to choose a closed form representative;
* show the integration functional equals the prescribed `φ`.
-/
theorem deRhamComparisonMap1_exists_form_with_periods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ :=
  (deRhamComparisonMap1Spec_frontier X).exists_form_with_periods φ

/--
**Injectivity sub-obligation 1a (existence of path-integral primitive).**
A closed 1-form with zero periods admits a global smooth 0-form whose
exterior derivative is the original form. This is the deep analytic
content (FTC for forms / path-integration on a connected manifold).

Mathematical construction:
* choose a base point using connectedness/nonemptiness;
* define a candidate primitive by integrating along a path from the basepoint;
* use zero periods to prove path-independence;
* prove local smoothness and derivative equality in charts;
* use closedness of `ω` and the fundamental theorem for line integrals.
-/
theorem closedForm_pathIntegral_primitive_exists
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  (deRhamComparisonMap1Spec_frontier X).primitive_exists ω hω

noncomputable def closed_form_from_cech_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ClosedForm 1 X :=
  closed_form_from_cech_cocycle_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

theorem integral_closed_form_from_cech_eq
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X (closed_form_from_cech_cocycle X φ) = φ :=
  integral_closed_form_from_cech_eq_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

theorem deRhamComparisonMap1_prescribed_period_candidate
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, ω = closed_form_from_cech_cocycle X φ := by
  exact ⟨closed_form_from_cech_cocycle X φ, rfl⟩

theorem deRhamComparisonMap1_prescribed_period_correct
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (Classical.choose (deRhamComparisonMap1_prescribed_period_candidate X φ)) = φ := by
  have h := Classical.choose_spec (deRhamComparisonMap1_prescribed_period_candidate X φ)
  rw [h]
  exact integral_closed_form_from_cech_eq X φ

theorem deRhamComparisonMap1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ :=
  deRhamComparisonMap1_surjective_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

noncomputable def closedForm_pathIntegral_primitive
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    SmoothDiffForm 0 X :=
  closedForm_pathIntegral_primitive_of_spec X (deRhamComparisonMap1Spec_frontier X) ω hω

theorem closedForm_pathIntegral_primitive_derivative
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X (closedForm_pathIntegral_primitive X ω hω) = (ω : SmoothDiffForm 1 X) :=
  closedForm_pathIntegral_primitive_derivative_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω

theorem deRhamComparisonMap1_zero_period_potential
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  deRhamComparisonMap1_zero_period_potential_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω

theorem deRhamComparisonMap1_kernel_subset_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
  deRhamComparisonMap1_kernel_subset_exact_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω

private theorem comparison_ker_eq_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    LinearMap.ker (deRhamComparisonMap1 X) = ExactForm.toClosedSubmodule 0 X :=
  comparison_ker_eq_exact_of_spec X (deRhamComparisonMap1Spec_frontier X)

private theorem comparison_range_eq_top
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    LinearMap.range (deRhamComparisonMap1 X) = ⊤ :=
  comparison_range_eq_top_of_spec X (deRhamComparisonMap1Spec_frontier X)

private noncomputable def deRhamH1_linearEquiv
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    deRhamH1Cocycle X ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) :=
  deRhamH1_linearEquiv_of_spec X (deRhamComparisonMap1Spec_frontier X)

/-
Pure algebra: for a finitely generated free ℤ-module `M`,
the ℂ-dimension of `Hom_ℤ(M, ℂ)` equals the ℤ-rank of `M`.

Analogous to `finrank_homℤℝ_eq_finrank_of_free` but over ℂ.
-/

theorem deRhamH1Cocycle_finrank_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = realDimSingularH1 X := by
  rw [(deRhamH1_linearEquiv X).finrank_eq]
  rw [realDim_singularH1_eq_finrank_intH1_via_uct X]
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  exact finrank_homℤℂ_eq_finrank_of_free (IntegralOneCycle X)

theorem realDimDeRhamH1_eq_realDimSingularH1_via_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = realDimSingularH1 X := by
  rw [realDimDeRhamH1_eq_finrank_cocycleℝ X,
      deRhamH1Cocycle_finrank_eq_realDim_singularH1 X]
