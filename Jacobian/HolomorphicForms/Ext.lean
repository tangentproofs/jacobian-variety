import Jacobian.HolomorphicForms.Defs

/-!
# Extensionality for `HolomorphicOneForm`

`HolomorphicOneForm` extends `ContMDiffSection`, which already has an
`ext` principle on the underlying section. This file repackages that
principle in user-friendly forms keyed to `.toFun`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Two holomorphic 1-forms are equal iff their `toFun` agree pointwise. -/
theorem ext_toFun_iff {η ζ : HolomorphicOneForm E X} :
    η = ζ ↔ ∀ x, η.toFun x = ζ.toFun x := by
  constructor
  · rintro rfl x; rfl
  · intro h
    apply ContMDiffSection.ext
    intro x
    exact h x

/-- Pointwise extensionality. -/
theorem ext_toFun {η ζ : HolomorphicOneForm E X}
    (h : ∀ x, η.toFun x = ζ.toFun x) : η = ζ :=
  ext_toFun_iff.mpr h

/--
Two holomorphic 1-forms are equal iff their `toFun` agree at all
points and tangent vectors.
-/
theorem ext_toFun_apply_iff {η ζ : HolomorphicOneForm E X} :
    η = ζ ↔ ∀ x v, η.toFun x v = ζ.toFun x v := by
  rw [ext_toFun_iff]
  refine ⟨fun h x v => by rw [h x], fun h x => ?_⟩
  ext v
  exact h x v

/-- Vector-pointwise extensionality. -/
theorem ext_toFun_apply {η ζ : HolomorphicOneForm E X}
    (h : ∀ x v, η.toFun x v = ζ.toFun x v) : η = ζ :=
  ext_toFun_apply_iff.mpr h

/--
A holomorphic 1-form equals zero iff it vanishes pointwise.

Specialization of `ext_toFun_iff` at `ζ = 0`.  The right-to-left
direction unfolds `(0).toFun` via `ContMDiffSection.coe_zero`.
-/
theorem eq_zero_iff_toFun {η : HolomorphicOneForm E X} :
    η = 0 ↔ ∀ x, η.toFun x = 0 := by
  rw [ext_toFun_iff]
  rfl

/-- A holomorphic 1-form is zero from pointwise vanishing. -/
theorem eq_zero_of_toFun {η : HolomorphicOneForm E X}
    (h : ∀ x, η.toFun x = 0) : η = 0 :=
  eq_zero_iff_toFun.mpr h

end JacobianChallenge.HolomorphicForms
