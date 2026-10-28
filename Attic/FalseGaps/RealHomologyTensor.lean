/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/RealHomologyTensor.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
This refines the previously-monolithic obligation into the named
ingredients:
1. UCT (`realDimSingularH1_eq_finrank_intHom1`),
2. finite generation + freeness (`IntegralOneCycle_finite`,
   `IntegralOneCycle_torsionFree`),
3. pure algebra (`finrank_homℤℝ_eq_finrank_of_free`).
-/
theorem realDim_singularH1_eq_finrank_intH1_via_uct
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimSingularH1 X = Module.finrank ℤ (IntegralOneCycle X) := by
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  rw [realDimSingularH1_eq_finrank_intHom1 X,
      finrank_homℤℝ_eq_finrank_of_free (IntegralOneCycle X)]
