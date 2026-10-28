/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/HolomorphicForms/DeRhamSingular.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

theorem realDim_deRhamH1_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = realDimSingularH1 X :=
  realDimDeRhamH1_eq_realDimSingularH1_via_cocycle X

/--
Refinement direction: split into
`(a) IntegralOneCycle_finiteFree X : Module.Free ℤ (IntegralOneCycle X) ∧ Module.Finite ℤ _`
and
`(b) finrank_homℤℝ_of_free : ∀ M [Module.Free ℤ M] [Module.Finite ℤ M], Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M`.
Both are pure linear-algebra obligations.  See `IntegralOneCycleRank.lean`.
-/
theorem realDim_singularH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimSingularH1 X = Module.finrank ℤ (IntegralOneCycle X) :=
  realDim_singularH1_eq_finrank_intH1_via_uct X

/--
This is the **de Rham side** of the top-level `hodge_deRham_rank_eq`
assembly.
-/
theorem realDim_deRhamH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = Module.finrank ℤ (IntegralOneCycle X) := by
  rw [realDim_deRhamH1_eq_realDim_singularH1 X,
      realDim_singularH1_eq_finrank_intH1 X]
