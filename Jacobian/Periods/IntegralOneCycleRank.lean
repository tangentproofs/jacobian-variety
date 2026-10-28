import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.CellularHomologyRS
import Jacobian.Periods.FreeModuleHomFinrank
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Pure-algebra rank leaves for `IntegralOneCycle X`

The `realDim_singularH1_eq_finrank_intH1` theorem in
`Jacobian/HolomorphicForms/DeRhamSingular.lean` factors through two
*pure-algebra* leaves:

1. `IntegralOneCycle X` is a finitely generated free ℤ-module
   (compact-manifold-singular-homology fact, via the cellular structure
   inherited from a Radó triangulation; ABSENT in v4.28.0).

2. For any finitely generated free ℤ-module `M`, the ℝ-dimension of
   `Hom_ℤ(M, ℝ)` equals the ℤ-rank of `M`.

This file states (1) and (2) as named obligations, plus the algebraic
fact (2′) that finite-rank free ℤ-modules tensor up to finite-dimensional
ℝ-vector spaces of the same finrank.

## TOPDOWN role
-/

namespace JacobianChallenge.Periods

open scoped Manifold



/--
This is one of the smallest leaves in the entire `hodge_deRham_rank_eq`
chain.  Bottom-up content: pick a basis `b : Fin n → M`; the map
`Hom_ℤ(M, ℝ) → Fin n → ℝ` sending `f ↦ f ∘ b` is an ℝ-linear
isomorphism; both sides are `n`-dimensional over ℝ.

Mathlib v4.28.0 has `Module.Basis.constr`, `LinearEquiv.finrank_eq`,
`Module.finrank_pi`, and `Module.finrank_eq_card_basis`.  A direct proof
should fit in <40 lines.
-/
theorem finrank_homℤℝ_eq_finrank_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M :=
  finrank_homℤℝ_eq_finrank_of_free_via_basis M

end JacobianChallenge.Periods
