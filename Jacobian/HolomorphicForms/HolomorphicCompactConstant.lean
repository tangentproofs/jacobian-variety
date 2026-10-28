import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Global holomorphic functions on a compact connected Riemann surface

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A holomorphic function on a compact connected complex 1-manifold is
constant — the maximum modulus principle in analytic-manifold form.
Equivalently, `H⁰(X, 𝒪_X) ≃ ℂ`: the global sections of the structure
sheaf form a one-dimensional `ℂ`-vector space spanned by constant
functions.

This is a sec02 MEDIUM follow-up to the merged `CanonicalDivisor.lean`
chain. Per the explicit comment in
`Jacobian/HolomorphicForms/CanonicalDivisor.lean`:

> These belong to follow-up nodes once the analytic-sheaf machinery
> lands (`H⁰(𝒪_X) = ℂ` for compact connected RS via maximum modulus
> principle; …).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**MEDIUM.** Every holomorphic function on a compact connected
complex 1-manifold is constant. Proof via Mathlib's
`MDifferentiable.exists_eq_const_of_compactSpace`
(`Mathlib.Geometry.Manifold.Complex`), which packages the maximum
modulus principle in the manifold-`MDifferentiable` form. Steps:
`ContMDiff … ⊤ f` ⇒ `MDifferentiable I 𝓘(ℂ,ℂ) f` (via
`ContMDiff.mdifferentiable` with `1 ≤ ⊤`), and `[ConnectedSpace X]`
implies `[PreconnectedSpace X]`.
-/
theorem holomorphic_compact_connected_constant
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f) :
    ∃ c : ℂ, ∀ x : X, f x = c := by
  have hmd : MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) f :=
    hf.mdifferentiable WithTop.top_ne_zero
  obtain ⟨c, hc⟩ := hmd.exists_eq_const_of_compactSpace
  exact ⟨c, fun x => congrFun hc x⟩


theorem holomorphic_compact_connected_const_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {f : X → ℂ}
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (x y : X) : f x = f y := by
  obtain ⟨c, hc⟩ := holomorphic_compact_connected_constant X f hf
  rw [hc x, hc y]

end JacobianChallenge.HolomorphicForms
