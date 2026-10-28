/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/HolomorphicForms/HodgeDecomposition.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

theorem complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = analyticHarmonicGenus X :=
  complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus_via_cocycle X

/--
Combines `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (harmonic
projection) and `analyticHarmonicGenus_eq_two_analyticGenus`
(harmonic = holo + anti-holo, conjugation).
-/
theorem complexDimDeRhamH1ℂ_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    complexDimDeRhamH1ℂ X = 2 * analyticGenus ℂ X := by
  rw [complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus X,
      analyticHarmonicGenus_eq_two_analyticGenus X]

/--
Combines:
* `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (real-of-complex equality,
  in `DeRhamCohomology.lean`),
* `complexDimDeRhamH1ℂ_eq_two_analyticGenus` (Hodge decomp + conjugation,
  in this file).
-/
theorem realDimDeRhamH1_eq_two_analyticGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    realDimDeRhamH1 X = 2 * analyticGenus ℂ X := by
  rw [realDim_deRhamH1_eq_complexDim_deRhamH1ℂ X,
      complexDimDeRhamH1ℂ_eq_two_analyticGenus X]
