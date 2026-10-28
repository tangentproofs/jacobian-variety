/-!
# RETIRED — not built, not imported (declarations moved out of `Jacobian/Periods/IntegralOneCycleRank.lean`)

Goal (d) of the independent repair: gaps that are **false as stated** and **unreachable**
from the public API (declaration-level dependency sweep from `Jacobian/Solution.lean`)
are retired together with every declaration that depends on them. See
`Attic/FalseGaps/README.md` for the counterexamples. This file does not compile on its
own and nothing may import it.
-/

/--
Bottom-up content: a compact smooth manifold admits a finite CW (or
triangulated) structure (Whitehead, Radó for surfaces); cellular homology
of a finite CW complex is the homology of a complex of finitely generated
free ℤ-modules; finitely generated abelian groups are finitely generated
ℤ-modules. Mathlib v4.28.0 lacks both finite CW structures on manifolds
and the cellular-homology comparison theorem with singular homology.

This is the *finite-generation* ingredient. The companion freeness
ingredient is `IntegralOneCycle_torsionFree` below; together they imply
`Module.Free ℤ (IntegralOneCycle X)`.
-/
theorem IntegralOneCycle_finite
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) :=
  IntegralOneCycle_finite_via_cellular X

/--
Bottom-up content: the universal-coefficient short exact sequence
`0 → Ext(H_0, ℤ) → H¹(X, ℤ) → Hom(H₁(X, ℤ), ℤ) → 0` and the fact that
`H_0(X, ℤ) = ℤ` for connected `X` make `H¹(X, ℤ)` torsion-free; dualising
shows `H₁(X, ℤ)` is torsion-free *for orientable closed surfaces*
(Poincaré duality).  In general dimensions the torsion-freeness of `H₁`
needs a separate argument (Hurewicz + abelianisation of `π_1`).
-/
theorem IntegralOneCycle_torsionFree
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) :=
  IntegralOneCycle_torsionFree_via_cellular X
