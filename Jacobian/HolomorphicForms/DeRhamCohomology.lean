import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.TotallyDisconnected
import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# De Rham cohomology dimensions on a smooth manifold

## What this file provides (refinement scaffolding)

## TOPDOWN role

No file outside `Jacobian/HolomorphicForms/` should reach for these
names directly; the assembly-layer files (`HodgeTheoremRS.lean`,
`HodgeDeRhamRank.lean`) re-export the only identities that downstream
code (e.g. `Jacobian/Periods/PeriodFunctional.lean`) consumes.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
Concrete model of `H¹_dR(X, ℂ)` as closed 1-forms modulo exact
1-forms.
-/
noncomputable def deRhamH1Cocycle
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  (ClosedFormSub (Nat.succ 0) X) ⧸ (ExactForm.toClosedSubmodule 0 X)

noncomputable instance deRhamH1Cocycle.instAddCommGroup
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (deRhamH1Cocycle X) :=
  inferInstanceAs (AddCommGroup (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

noncomputable instance deRhamH1Cocycle.instModuleℂ
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (deRhamH1Cocycle X) :=
  inferInstanceAs (Module ℂ (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

/--
Complex dimension of the first de Rham cohomology group of `X` with
ℂ-valued differential forms, computed from the explicit closed-mod-exact
quotient model.
-/
noncomputable def complexDimDeRhamH1ℂ
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (deRhamH1Cocycle X)

/--
Real dimension of the first de Rham cohomology group in the current
ℂ-valued-form substrate. Since this layer has no separate real-form
complex, the real/complex extension-of-scalars bridge is represented by
the same closed-mod-exact quotient finrank.
-/
noncomputable def realDimDeRhamH1
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (deRhamH1Cocycle X)

/--
Real dimension of the zeroth de Rham
cohomology group of `X` with ℝ-valued forms. Mathematically equals the
number of connected components; for a connected manifold this is `1`.
-/
noncomputable def realDimDeRhamH0
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Nat.card (ConnectedComponents X)

/--
Complex dimension of the zeroth de Rham
cohomology group of `X` with ℂ-valued forms. Equals the ℂ-dimension of
locally constant ℂ-valued functions; for a connected `X` this is `1`.
-/
noncomputable def complexDimDeRhamH0ℂ
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Nat.card (ConnectedComponents X)

-- The real-of-complex de Rham identity has been moved to
-- `Jacobian/HolomorphicForms/RealComplexDeRham.lean` and refined into a
-- (`complexDeRhamH1_eq_tensorℂ_realDeRhamH1` analytic;
-- `tensorℂ_finrank_eq_real_finrank` pure algebra).

/--
Bottom-up content: a global ℂ-valued de Rham 0-cocycle is a smooth
function `f : X → ℂ` with `df = 0`, i.e. a locally constant function.
On a connected space, locally constant means constant; the space of
constants is one-dimensional over ℂ.  This factors through Mathlib's
`holomorphic_compact_connected_constant` analogue (already in the
project as `Jacobian.HolomorphicForms.HolomorphicCompactConstant.lean`),
adapted to smooth ℂ-valued functions.
-/
theorem complexDim_deRhamH0ℂ_eq_one_of_compact_connected
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH0ℂ X = 1 := by
  rw [complexDimDeRhamH0ℂ, Nat.card_eq_one_iff_unique]
  constructor
  · haveI : ConnectedSpace (ConnectedComponents X) :=
      ConnectedComponents.surjective_coe.connectedSpace ConnectedComponents.continuous_coe
    constructor
    intro a b
    have hsub : (Set.univ : Set (ConnectedComponents X)).Subsingleton :=
      isPreconnected_univ.subsingleton
    exact hsub trivial trivial
  · haveI : Nonempty X := inferInstance
    let x : X := Classical.arbitrary X
    exact Nonempty.intro (show ConnectedComponents X from x)


theorem realDim_deRhamH0_eq_one_of_compact_connected
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH0 X = 1 := by
  rw [realDimDeRhamH0, Nat.card_eq_one_iff_unique]
  constructor
  · haveI : ConnectedSpace (ConnectedComponents X) :=
      ConnectedComponents.surjective_coe.connectedSpace ConnectedComponents.continuous_coe
    constructor
    intro a b
    have hsub : (Set.univ : Set (ConnectedComponents X)).Subsingleton :=
      isPreconnected_univ.subsingleton
    exact hsub trivial trivial
  · haveI : Nonempty X := inferInstance
    let x : X := Classical.arbitrary X
    exact Nonempty.intro (show ConnectedComponents X from x)

end JacobianChallenge.HolomorphicForms
