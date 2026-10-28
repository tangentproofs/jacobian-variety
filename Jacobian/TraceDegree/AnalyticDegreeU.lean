import Jacobian.TraceDegree.AnalyticPullbackFunctorialU

/-!
# Universe-polymorphic analytic degree

This file provides the universe-polymorphic analytic degree `analyticDegreeU`
(E3a of the TraceDegree "E-chain"), together with its well-definedness lemmas —
the universe-`u` companions of the Type-0 `analyticDegree` (`AnalyticDegree.lean:60`)
/ `analyticDegree_constant` (`:72`) / `branchedDegree_eq_of_compatible` (`:90`) /
`analyticDegree_eq_canonical_branchedDegree` (`:119`), needed by the public
`degree` / `pushforward_pullback` for `X : Type u` (Milestone C).

## Genuine — no sorry

The degree is the Classical case-split `if f constant then 0 else if a
RamificationIndexCompatible branched-cover datum exists then its branchedDegree
else 0`. Its foundations are already universe-polymorphic:
`BranchedCoverData (X Y : Type*)` (`BranchedCover.lean:56`),
`branchedDegree {X Y : Type*}` (`:163`) and
`branchedDegree_eq_weightedFiberCard {X Y : Type*}` (`:173`). The Type-0
well-definedness lemma `branchedDegree_eq_of_compatible` is `.{0,0}`-bound (it
sits in `AnalyticDegree.lean`'s `{X Y : Type}` block), but its proof uses only
the `Type*` `branchedDegree_eq_weightedFiberCard`, `Set.Finite.toFinset_inj`, and
the `RamificationIndexCompatible` application, so it is restated verbatim here as
`branchedDegree_eq_of_compatibleU`. Every declaration in this file is sorry-free
(`analyticDegreeU` is a Classical case-split over universe-polymorphic
branched-cover data — no frontier obligation). The trace identity that *consumes*
this degree (`analyticPushforward_analyticPullbackU`) is the separate next step
E3b, where the deep `trace_pullback` content is isolated.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [FiniteDimensionalHolomorphicOneForms ℂ Y]

/--
**Concrete analytic degree** for `X Y : Type u`. Universe-polymorphic companion
of `analyticDegree` (`AnalyticDegree.lean:60`):

* `0` if `f` is constant;
* `branchedDegree` of a Classically chosen `RamificationIndexCompatible`
  branched-cover datum, if one exists;
* `0` otherwise.

`[Nonempty Y]` (needed by `branchedDegree`) comes from `ConnectedSpace Y`.
-/
noncomputable def analyticDegreeU (f : X → Y)
    (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if _hconst : ∃ y₀, ∀ x, f x = y₀ then 0
  else
    if hbc : ∃ hbc : BranchedCoverData X Y f,
        hbc.RamificationIndexCompatible then
      branchedDegree hbc.choose
    else 0

-- The well-definedness lemmas below reference only `BranchedCoverData` /
-- `IsHolomorphic` / the degree def, not the manifold/T2/Compact/StableChartAt/
-- FiniteDim instances (`ConnectedSpace Y` is still needed — it supplies
-- `[Nonempty Y]` to `branchedDegree`); omit the unused section variables.
omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
 [FiniteDimensionalHolomorphicOneForms ℂ X]
  [T2Space Y] [CompactSpace Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
 [FiniteDimensionalHolomorphicOneForms ℂ Y]

/-- Constant maps have analytic degree zero. Universe-`u` companion of
`analyticDegree_constant` (`AnalyticDegree.lean:72`). -/
theorem analyticDegree_constantU (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    analyticDegreeU f hf = 0 := by
  unfold analyticDegreeU
  simp [hconst]

/-- **Branched-degree-uniqueness** for holomorphic maps: two
`RamificationIndexCompatible` branched-cover data on the same holomorphic map have
equal `branchedDegree`. Universe-`u` companion of `branchedDegree_eq_of_compatible`
(`AnalyticDegree.lean:90`); verbatim port (its proof is universe-polymorphic). -/
theorem branchedDegree_eq_of_compatibleU
    {f : X → Y} (hHol : IsHolomorphic f)
    (h₁ h₂ : BranchedCoverData X Y f)
    (hc₁ : h₁.RamificationIndexCompatible)
    (hc₂ : h₂.RamificationIndexCompatible) :
    branchedDegree h₁ = branchedDegree h₂ := by
  classical
  set y : Y := Classical.arbitrary Y
  rw [branchedDegree_eq_weightedFiberCard h₁ y,
      branchedDegree_eq_weightedFiberCard h₂ y]
  unfold BranchedCoverData.weightedFiberCard
  have hfin_eq : (h₁.finite_fiber y).toFinset = (h₂.finite_fiber y).toFinset :=
    Set.Finite.toFinset_inj.mpr rfl
  rw [hfin_eq]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [hc₁ x (hHol.holomorphicAt x), hc₂ x (hHol.holomorphicAt x)]

/-- **Analytic degree equals branched degree, canonical form.** For a nonconstant
holomorphic map, `analyticDegreeU` agrees with the `branchedDegree` of any
`RamificationIndexCompatible` datum. Universe-`u` companion of
`analyticDegree_eq_canonical_branchedDegree` (`AnalyticDegree.lean:119`). -/
theorem analyticDegree_eq_canonical_branchedDegreeU (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hHol : IsHolomorphic f)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    analyticDegreeU f hf = branchedDegree hbc := by
  classical
  unfold analyticDegreeU
  simp only [dif_neg hnonconst]
  have hex : ∃ hbc : BranchedCoverData X Y f, hbc.RamificationIndexCompatible :=
    ⟨hbc, hcompat⟩
  rw [dif_pos hex]
  exact branchedDegree_eq_of_compatibleU hHol hex.choose hbc hex.choose_spec hcompat

end JacobianChallenge.TraceDegree
