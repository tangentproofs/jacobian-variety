import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.ChartStabilityRefutation
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Eval-at-one for cotangent sections, and the frame assumption it needs

Reading a cotangent section `σ` "at `1`" — the function `x ↦ σ.toFun x 1`
— silently uses a **global frame** for the tangent bundle: it feeds the
*same* number `1` into every fibre `TangentSpace 𝓘(ℂ, ℂ) x`. That is
legitimate only when the atlas trivializes the tangent bundle, because
`fun x => TotalSpace.mk' ℂ x (1 : ℂ)` is then a nowhere-vanishing
continuous tangent section.

For a **compact** Riemann surface that forces `χ(X) = 2 - 2 * genus X = 0`,
i.e. genus `1`. So the assumption is false for every genus other than `1`
— notably for the sphere, which the challenge's `genus_eq_zero_iff_homeo`
is about.

This file previously obtained the assumption from the typeclass
`JacobianChallenge.Periods.StableChartAt ℂ X`, which
`Jacobian/Periods/ChartStabilityRefutation.lean` refutes outright for
compact connected `X`. The repair here does **not** hide the assumption
in a different typeclass. It gives it a name,
`AtlasTrivializesTangent X`, and makes it an **explicit hypothesis** on
every theorem that needs it, so that the assumption is visible in each
signature and has to be discharged — or admitted — at the call site.

Two things are true about `AtlasTrivializesTangent` and both matter:

* It is **satisfiable**: `atlasTrivializesTangent_of_chartStable` derives
  it from chart stability, which holds for the model space `ℂ` charted on
  itself. So this is an honest hypothesis, not a disguised `False`.
* It is **not available** for a compact Riemann surface of genus `≠ 1`.
  Every consumer that instantiates at such an `X` therefore has a real
  obligation, which is now impossible to overlook.

The eventual fix for the consumers is not to discharge this hypothesis
but to stop needing it: read the section through the trivialization at
the point being examined (`ContinuousLinearMap.inCoordinates`) and carry
a transformation law, rather than reading it against a global `1`. That
rebuild is tracked as goal (a) step 2 in `ref/stablechart-uses.md` §6.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open Bundle
open JacobianChallenge.Periods

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
**The frame assumption behind every "eval at `1`" reading.**

`AtlasTrivializesTangent X` says the constant-`1` section of the tangent
bundle of `X` is smooth. Equivalently, `X` carries a nowhere-vanishing
smooth tangent vector field that the atlas writes as the constant `1`.

This is an honest, satisfiable hypothesis (see
`atlasTrivializesTangent_of_chartStable`), and it is **false** for a
compact Riemann surface of genus `≠ 1`, where `χ(X) ≠ 0` forbids a
nowhere-zero continuous vector field. It is stated as a plain `Prop` and
passed explicitly — never as a typeclass — so it cannot spread as an
invisible binder the way `StableChartAt` did.
-/
def AtlasTrivializesTangent (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Prop :=
  ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
    (fun x : X => TotalSpace.mk' ℂ (E := TangentSpace (𝓘(ℂ, ℂ))) x (1 : ℂ))

/--
**Chart stability implies the frame assumption** — this is the honest
remnant of the old `contMDiff_tangentSection_one`.

The proof is the original one, with the refuted typeclass replaced by an
explicit `ChartStable ℂ X` hypothesis: `Bundle.contMDiffAt_section`
reduces smoothness to smoothness of the trivialization at `x₀`, which by
`FiberBundleCore.localTriv_apply` sends
`⟨y, 1⟩ ↦ ⟨y, coordChange (achart ℂ y) (achart ℂ x₀) y 1⟩`; chart
stability collapses the `coordChange` to the identity on
`(chartAt ℂ x₀).source`.

This is what makes `AtlasTrivializesTangent` satisfiable rather than
vacuous: the model space `ℂ` charted on itself is chart-stable. It is
*not* a route to the hypothesis for a compact connected `X`, where
`not_chartStable_of_compactSpace` refutes the premise.
-/
theorem atlasTrivializesTangent_of_chartStable (hs : ChartStable ℂ X) :
    AtlasTrivializesTangent X := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  refine (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
  have hx₀ : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds hx₀] with y hy
  have hachart : achart ℂ y = achart ℂ x₀ := hs.achart_eq_of_mem_source hy
  change (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ x₀) y (1 : ℂ) = (1 : ℂ)
  rw [hachart]
  exact (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
    (achart ℂ x₀) y hy (1 : ℂ)

/--
Eval-at-1 of a smooth cotangent section is continuous, **conditional on
`AtlasTrivializesTangent X`**.

Uses `ContMDiff.clm_bundle_apply` to pair the cotangent section with the
constant tangent section supplied by `htriv`.
-/
theorem continuous_eval_at_one_of_contMDiffSection
    (htriv : AtlasTrivializesTangent X) (σ : HolomorphicOneForm ℂ X) :
    Continuous (fun x => (σ.toFun x) (1 : ℂ)) := by
  -- Step 1: Apply clm_bundle_apply to get smooth section of trivial bundle
  have hresult : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => TotalSpace.mk' ℂ (E := Trivial X ℂ) x
        (show (Trivial X ℂ) x from (σ.toFun x) (1 : ℂ))) :=
    σ.contMDiff.clm_bundle_apply htriv
  -- Step 2: Extract continuity from the trivial bundle section
  have hcont := hresult.continuous
  rw [continuous_iff_continuousAt] at hcont ⊢
  intro x₀
  have hx := hcont x₀
  rw [FiberBundle.continuousAt_totalSpace] at hx
  convert hx.2

end JacobianChallenge.HolomorphicForms
