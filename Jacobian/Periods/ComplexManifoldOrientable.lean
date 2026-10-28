import Jacobian.Periods.Orientable
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Complex 1-manifolds are orientable

Stage B2 of the polygonal-model plan: a complex one-dimensional
manifold is orientable as a real two-dimensional manifold.

## Top-down role

`complexManifold_orientable` is the (currently-trivial) instance
that makes `[Orientable X]` available wherever a complex chart on
`X` is in scope. The instance is the named site at which the eventual
holomorphic-Jacobian-positivity argument will land.

## Bottom-up content

A holomorphic transition map `ψ ∘ φ⁻¹ : ℂ → ℂ` is orientation-preserving
because its real Jacobian
`((Re w)_x  (Re w)_y; (Im w)_x  (Im w)_y) =
  ((Re w)_x  -(Im w)_x; (Im w)_x   (Re w)_x)`
(by Cauchy–Riemann) has determinant `|w'|² ≥ 0`. Once
`Jacobian.Periods.Orientable` carries genuine content (consistent
chart choice / top-degree homology / volume form), this instance will
produce a real proof from `IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ X`.

For now `Orientable` carries a lightweight witness, so the instance is
inhabited by `⟨⟨()⟩⟩`.
-/

namespace JacobianChallenge.Periods

open scoped Manifold


instance complexManifold_orientable
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Orientable X :=
  ⟨⟨()⟩⟩

end JacobianChallenge.Periods
