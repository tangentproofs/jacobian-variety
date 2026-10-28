import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.Periods.PeriodLattice
import Jacobian.Periods.PeriodFullComplexLatticeU
import Jacobian.ComplexTorus.ULiftTransport
import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.AbelJacobi.AnalyticOfCurveU
import Jacobian.AbelJacobi.AnalyticOfCurveInjectiveU
import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.TraceDegree.AnalyticDegree
import Jacobian.TraceDegree.PiecewiseC1Instance
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Jacobian.TraceDegree.AnalyticPushforwardFunctorialU
import Jacobian.TraceDegree.AnalyticPullbackFunctorialU
import Jacobian.TraceDegree.AnalyticPushPullU

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! # Solution mirror of `Jacobian/Challenge.lean` -/

open scoped ContDiff -- for ω notation
open scoped Manifold -- for 𝓘 notation

namespace JacobianChallenge.Solution

-- Global instance adapter to unlock the top-down signatures without exposing extra binders.
-- (The former `StableChartAt` adapter instance that stood here was refuted by
-- `JacobianChallenge.Periods.not_chartStable_of_compactSpace` and has been deleted.)
noncomputable instance (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X :=
  JacobianChallenge.HolomorphicForms.compactRiemannSurface_finiteDimensionalHolomorphicOneForms_frontier X

/-- The genus of a compact Riemann surface: the complex dimension of its space of
holomorphic 1-forms. Stated directly as `Module.finrank` (definitionally
`analyticGenus ℂ X`) so that the *value* does not depend on the finiteness proof; the
finiteness theorem is a named classical input, used only where a basis is needed. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (JacobianChallenge.HolomorphicForms.HolomorphicOneForm ℂ X)

lemma genus_eq_zero_with_routeData_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : genus X = 0)
    (hmod :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.PoleModulusData)
    (hbranch :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.BranchedCoverDataOfPoleDegree) :
    Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero_with_routeData X
    (by simpa [genus] using h) hmod hbranch

/-- Genus zero classification. -/
lemma genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere X

end JacobianChallenge.Solution

-- =========================================================================
--  PUBLIC UNIFIED SPEC INTERFACE (matching Jacobian/Challenge.lean strictly)
-- =========================================================================

/-- The genus of a compact Riemann surface. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  JacobianChallenge.Solution.genus (X := X)

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.Solution.genus_eq_zero_iff_homeo (X := X)

universe u in
/-- The Jacobian of a compact Riemann surface. -/
def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u :=
  ULift.{u} (JacobianChallenge.ComplexTorus.quotient (Fin (genus X) → ℂ)
    (JacobianChallenge.Periods.periodFullComplexLatticeU X))

namespace Jacobian

-- let X be a compact Riemann surface.
-- The universe is pinned to the explicit name `u_1` (rather than left to
-- auto-binding) so the public theorems export with `levelParams = [u_1]`,
-- matching `Challenge.lean`'s auto-bound `u_1`. The comparator compares the
-- whole `ConstantVal` structurally — universe-parameter *names* included — so a
-- divergence here (Solution drifting to `u_2`) makes every X-only theorem
-- mismatch even though the type structure is byte-identical.
universe u_1
variable {X : Type u_1} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : AddCommGroup (Jacobian X) := inferInstanceAs (AddCommGroup (ULift _))
noncomputable instance : TopologicalSpace (Jacobian X) := inferInstanceAs (TopologicalSpace (ULift _))
instance : T2Space (Jacobian X) := inferInstanceAs (T2Space (ULift _))
instance : CompactSpace (Jacobian X) := inferInstanceAs (CompactSpace (ULift _))
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  inferInstanceAs (ChartedSpace (Fin (genus X) → ℂ) (ULift _))
noncomputable instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ULift _))
noncomputable instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ULift _))

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. -/
noncomputable def ofCurve (P : X) : X → Jacobian X :=
  fun Q => ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurveU X P Q)

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up
      (Λ := JacobianChallenge.Periods.periodFullComplexLatticeU X)).comp
    (JacobianChallenge.AbelJacobi.analyticOfCurve_contMDiffU (X := X) P)

lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  show ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurveU X P P) = 0
  rw [JacobianChallenge.AbelJacobi.analyticOfCurve_selfU]; rfl

lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := by
  intro a b hab
  apply JacobianChallenge.AbelJacobi.analyticOfCurve_injectiveU X P (by rw [genus] at h; exact h)
  exact ULift.up_injective hab

-- `Y`'s universe is pinned to `u_2` for the same reason `X` is pinned to `u_1`
-- above: the comparator compares universe-parameter names literally, and
-- `Challenge.lean`'s auto-bound second curve is `u_2`.
universe u_2
variable {Y : Type u_2} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  JacobianChallenge.ComplexTorus.ULiftContinuousAddMonoidHom'
    (JacobianChallenge.TraceDegree.analyticPushforwardU f hf)

theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) := by
  show ContMDiff _ _ ω
    (fun a : Jacobian X =>
      (ULift.up (JacobianChallenge.TraceDegree.analyticPushforwardU f hf a.down) : Jacobian Y))
  exact (JacobianChallenge.ComplexTorus.contMDiff_uLift_up
        (Λ := JacobianChallenge.Periods.periodFullComplexLatticeU Y)).comp
    ((JacobianChallenge.TraceDegree.analyticPushforward_contMDiffU f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down
        (Λ := JacobianChallenge.Periods.periodFullComplexLatticeU X)))

lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P := by
  show (ULift.up (JacobianChallenge.TraceDegree.analyticPushforwardU id contMDiff_id P.down)
      : Jacobian X) = P
  rw [JacobianChallenge.TraceDegree.analyticPushforward_id_applyU P.down]
  rfl

-- `Z`'s universe is pinned to `u_3` to match `Challenge.lean`'s auto-bound
-- third curve (see the `u_1`/`u_2` pins above).
universe u_3
variable {Z : Type u_3} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforwardU (g ∘ f) (hg.comp hf) P.down)
    = ULift.up (JacobianChallenge.TraceDegree.analyticPushforwardU g hg
        (JacobianChallenge.TraceDegree.analyticPushforwardU f hf P.down))
  rw [JacobianChallenge.TraceDegree.analyticPushforward_comp_applyU f hf g hg P.down]

/-- Pullback map between Jacobians associated to a map of the underlying curves. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  JacobianChallenge.ComplexTorus.ULiftContinuousAddMonoidHom'
    (JacobianChallenge.TraceDegree.analyticPullbackU f hf)

theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := by
  show ContMDiff _ _ ω
    (fun a : Jacobian Y =>
      (ULift.up (JacobianChallenge.TraceDegree.analyticPullbackU f hf a.down) : Jacobian X))
  exact (JacobianChallenge.ComplexTorus.contMDiff_uLift_up
        (Λ := JacobianChallenge.Periods.periodFullComplexLatticeU X)).comp
    ((JacobianChallenge.TraceDegree.analyticPullback_contMDiffU f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down
        (Λ := JacobianChallenge.Periods.periodFullComplexLatticeU Y)))

lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := by
  show (ULift.up (JacobianChallenge.TraceDegree.analyticPullbackU id contMDiff_id P.down)
      : Jacobian X) = P
  rw [JacobianChallenge.TraceDegree.analyticPullback_id_applyU P.down]
  rfl

lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPullbackU (g.comp f) (hg.comp hf) P.down)
    = ULift.up (JacobianChallenge.TraceDegree.analyticPullbackU f hf
        (JacobianChallenge.TraceDegree.analyticPullbackU g hg P.down))
  rw [JacobianChallenge.TraceDegree.analyticPullback_comp_applyU f hf g hg P.down]

-- NB: the binder is named `hf` (not `_hf`) to match `Challenge.lean` exactly.
-- The comparator compares the definition's *type* structurally, and Lean's
-- derived `BEq` on `Expr` distinguishes binder names — so `_hf` vs `hf` would
-- fail `definitionHoleMatches` even though the kernel types are defeq.
set_option linter.unusedVariables false in
noncomputable def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if _hconst : ∃ y₀, ∀ x, f x = y₀ then 0
  else
    if hne : Nonempty Y then
      haveI : Nonempty Y := hne
      if hbc : ∃ hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f,
          hbc.RamificationIndexCompatible then
        JacobianChallenge.HolomorphicForms.branchedDegree
          (X := X) (Y := Y) (f := f) hbc.choose
      else 0
    else 0

@[simp]
theorem _root_.ContMDiff.degree_constant (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀, ∀ x, f x = y₀) :
    ContMDiff.degree f hf = 0 := by
  unfold ContMDiff.degree
  simp [hconst]

/-- The public `ContMDiff.degree` (whose signature deliberately omits `[ConnectedSpace Y]`
to match `Jacobian/Challenge.lean`) agrees with the concrete `analyticDegreeU`. In the
Riemann-surface context `[ConnectedSpace Y]` supplies the `Nonempty Y` that `degree`'s
body decides Classically, so the extra `if hne : Nonempty Y` wrapper reduces to its
`then` branch. -/
theorem _root_.ContMDiff.degree_eq_analyticDegreeU (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff.degree f hf = JacobianChallenge.TraceDegree.analyticDegreeU f hf := by
  unfold ContMDiff.degree JacobianChallenge.TraceDegree.analyticDegreeU
  have hne : Nonempty Y := inferInstance
  simp only [hne, dif_pos]

/--
**The `else 0` fallback of `ContMDiff.degree` never fires** (named existence lemma). For a
nonconstant holomorphic map of compact Riemann surfaces there is a ramification-compatible
branched-cover datum, built from `f` itself: ramification index = local analytic order
(`branchedCoverData_of_nonconstant_holomorphic`), with the local `k`-fold ramification
and weighted-fibre conservation packages derived from smoothness.

So the three branches of `ContMDiff.degree` are exactly: `f` constant ↦ `0` (the intended
value, not a fallback); `f` nonconstant ↦ the weighted fibre count `branchedDegree`
(`ContMDiff.degree_eq_branchedDegree`); and the two inner `else 0` branches are
unreachable — the `Nonempty Y` one because `Y` is connected, the `∃ hbc` one by this lemma.
-/
theorem _root_.ContMDiff.exists_branchedCoverData (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    ∃ hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f,
      hbc.RamificationIndexCompatible :=
  have hHol := JacobianChallenge.HolomorphicForms.isHolomorphic_of_contMDiff hf
    (JacobianChallenge.HolomorphicForms.hasLocalKfoldRamification_of_contMDiff hf)
  have hw := JacobianChallenge.HolomorphicForms.hasWeightedFiberConservation_of_contMDiff hf
  ⟨JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic hHol hw hnonconst,
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol hw hnonconst⟩

/--
For a nonconstant `f`, `ContMDiff.degree` is the weighted fibre count `branchedDegree` of
**any** ramification-compatible branched-cover datum (the value does not depend on the
datum: `branchedDegree_eq_of_compatibleU`). No existence hypothesis is needed for the
degree to take this branch: see `ContMDiff.exists_branchedCoverData`.
-/
theorem _root_.ContMDiff.degree_eq_branchedDegree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀)
    (hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ContMDiff.degree f hf = JacobianChallenge.HolomorphicForms.branchedDegree hbc := by
  rw [ContMDiff.degree_eq_analyticDegreeU f hf]
  exact JacobianChallenge.TraceDegree.analyticDegree_eq_canonical_branchedDegreeU f hf
    (JacobianChallenge.HolomorphicForms.isHolomorphic_of_contMDiff hf
      (JacobianChallenge.HolomorphicForms.hasLocalKfoldRamification_of_contMDiff hf))
    hbc hcompat hnonconst

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforwardU f hf
      (JacobianChallenge.TraceDegree.analyticPullbackU f hf P.down))
    = (ContMDiff.degree f hf) • P
  rw [JacobianChallenge.TraceDegree.analyticPushforward_analyticPullbackU f hf P.down]
  show (ULift.up ((JacobianChallenge.TraceDegree.analyticDegreeU f hf) • P.down) : Jacobian Y)
    = (ContMDiff.degree f hf) • P
  rw [ContMDiff.degree_eq_analyticDegreeU f hf]
  rfl

end Jacobian
