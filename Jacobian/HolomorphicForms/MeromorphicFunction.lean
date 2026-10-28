import Jacobian.HolomorphicForms.VanishingOrder
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
Production API promoted from blueprint: `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The set `Mer(X)` of meromorphic functions on a compact Riemann surface,
viewed as the field of meromorphic germ sections.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- The type of meromorphic functions on a compact Riemann surface `X`. -/
@[ext] structure MeromorphicFunctionType (X : Type*) [TopologicalSpace X]

    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /--
Underlying set function from `X` to the Riemann sphere
  `OnePoint ℂ`.
-/
  toFun : X → OnePoint ℂ
  /--
The lift `X → OnePoint ℂ` is continuous: poles map to `∞`, and
  in the disk model of a chart, `toFun` tends to `∞` near each pole.
-/
  toFun_continuous : Continuous toFun
  /--
The ℂ-projection of `toFun` is meromorphic at every point of `X`,
  in the manifold sense (chart-pulled-back).
-/
  isMeromorphic :
    ∀ p, JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
           (fun q => (toFun q).getD 0) p

namespace MeromorphicFunctionType

/-- Apply a `MeromorphicFunctionType` as a function `X → OnePoint ℂ`. -/
instance instCoeFun (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    CoeFun (MeromorphicFunctionType X) (fun _ => X → OnePoint ℂ) :=
  ⟨MeromorphicFunctionType.toFun⟩

end MeromorphicFunctionType

end JacobianChallenge.HolomorphicForms
