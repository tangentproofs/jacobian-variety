/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/HolomorphicForms/HodgeDeRhamRank.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
Combines:

The chain is `2g = realDim H¹_dR = rank ℤ H₁`.
-/
theorem two_analyticGenus_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    2 * analyticGenus ℂ X
      = Module.finrank ℤ (JacobianChallenge.Periods.IntegralOneCycle X) := by
  rw [← realDimDeRhamH1_eq_two_analyticGenus X,
      realDim_deRhamH1_eq_finrank_intH1 X]
