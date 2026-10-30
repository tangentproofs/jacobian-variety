import Jacobian.HolomorphicForms.AnalyticGenus
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Basis-aligned dual equivalence

For a complex manifold `X` with `FiniteDimensionalHolomorphicOneForms`,
this file builds the noncomputable linear equivalence between the linear
dual `HolomorphicOneForm E X →ₗ[ℂ] ℂ` and the basis-aligned model space
`Fin (analyticGenus E X) → ℂ`:

```text
holomorphicOneFormDualEquiv :
  (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (analyticGenus E X) → ℂ)
```

This is the bridge that lets period-lattice work in the basis-aligned model
(originally `Jacobian/Periods/PeriodLattice.lean`, since retired to
`Attic/FalseGaps/`; now `Jacobian/Periods/GenuinePeriodLattice.lean`) connect
to the period-pairing image in `Jacobian/Periods/PeriodFunctional.lean`
(linear-dual space). It uses Mathlib's `Module.finBasis` (an arbitrary
basis) and `Module.Basis.dualBasis` to dualize.

The equivalence depends on a choice of basis (it is not canonical — the
underlying basis is `Module.finBasis ℂ (HolomorphicOneForm E X)`, which
is itself an arbitrary choice via `Module.Free.chooseBasis`). For
defining `periodSubgroup` in the basis-aligned model it suffices that
*some* equivalence exists — the resulting subgroup depends on the basis,
but its abstract isomorphism class (and all topological/discreteness
properties) does not.

This file is a Claude-owned design move (commit aa2e593 next-tick plan):
the bottom-up infrastructure introduced to unfreeze the then-`opaque`
`periodSubgroup`. That is done — `PeriodLattice.lean` is retired to
`Attic/FalseGaps/`, and `Periods.periodSubgroup` is now a definition
(the range of `periodPairing`).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

/--
An arbitrary `Fin (analyticGenus E X)`-indexed basis of
`HolomorphicOneForm E X`. Comes from `Module.finBasis`, which itself
calls `Module.Free.chooseBasis`. The choice is non-canonical.
-/
noncomputable def holomorphicOneFormFinBasis :
    Module.Basis (Fin (analyticGenus E X)) ℂ (HolomorphicOneForm E X) :=
  Module.finBasis ℂ (HolomorphicOneForm E X)

/--
The dual basis of `holomorphicOneFormFinBasis`: an arbitrary
`Fin (analyticGenus E X)`-indexed basis of the linear dual
`HolomorphicOneForm E X →ₗ[ℂ] ℂ`.
-/
noncomputable def holomorphicOneFormDualFinBasis :
    Module.Basis (Fin (analyticGenus E X)) ℂ
      (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (holomorphicOneFormFinBasis E X).dualBasis

/--
The basis-aligned dual equivalence: a noncomputable `LinearEquiv`
between the linear dual of holomorphic 1-forms and the basis-aligned
model space. Uses the dual basis of an arbitrary chosen basis.
-/
noncomputable def holomorphicOneFormDualEquiv :
    (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      (Fin (analyticGenus E X) → ℂ) :=
  (holomorphicOneFormDualFinBasis E X).equivFun

/--
Pointwise reformulation: applying the equivalence to a dual basis
vector gives the standard basis vector at the same index.
-/
theorem holomorphicOneFormDualEquiv_dualBasis_apply
    (i : Fin (analyticGenus E X)) :
    holomorphicOneFormDualEquiv E X
        (holomorphicOneFormDualFinBasis E X i) =
      Pi.single i 1 := by
  ext j
  rw [holomorphicOneFormDualEquiv, Module.Basis.equivFun_self,
      Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun heq : j = i => h heq.symm)]

/--
Inverse direction: the standard basis vector `Pi.single i 1` pulls
back through the equivalence to the dual basis vector at index `i`.
Direct corollary of the forward apply lemma.
-/
theorem holomorphicOneFormDualEquiv_symm_pi_single
    (i : Fin (analyticGenus E X)) :
    (holomorphicOneFormDualEquiv E X).symm (Pi.single i 1) =
      holomorphicOneFormDualFinBasis E X i := by
  rw [LinearEquiv.symm_apply_eq, holomorphicOneFormDualEquiv_dualBasis_apply]

/--
The duality property of the chosen basis and its dual: the `i`-th
dual basis vector applied to the `j`-th basis vector is `δ_{ji}`. Direct
specialization of `Module.Basis.dualBasis_apply_self`.
-/
theorem holomorphicOneFormDualFinBasis_apply_holomorphicOneFormFinBasis
    (i j : Fin (analyticGenus E X)) :
    holomorphicOneFormDualFinBasis E X i
        (holomorphicOneFormFinBasis E X j) =
      (if j = i then 1 else 0 : ℂ) :=
  (holomorphicOneFormFinBasis E X).dualBasis_apply_self i j

/--
The basis-aligned dual equivalence applied to a functional `φ` and
evaluated at coordinate `i` reproduces `φ` applied to the `i`-th basis
1-form. This is the natural "evaluate-at-basis" interpretation of the
basis-aligned dual equivalence.
-/
theorem holomorphicOneFormDualEquiv_apply_eq_apply_basis
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ)
    (i : Fin (analyticGenus E X)) :
    holomorphicOneFormDualEquiv E X φ i =
      φ (holomorphicOneFormFinBasis E X i) := by
  classical
  -- holomorphicOneFormDualEquiv E X = (basisX.dualBasis).equivFun
  -- ((basisX.dualBasis).equivFun φ) i = the i-th coefficient when φ is
  -- expressed in the dual basis.
  -- φ = ∑ k, ((basisX.dualBasis).equivFun φ) k • basisX.dualBasis k
  -- Apply both sides at basisX i; on RHS, dualBasis k (basisX i) = δ_{i,k}
  -- so only the k = i term survives, giving the i-th coefficient.
  have hsum : ∑ k, ((holomorphicOneFormFinBasis E X).dualBasis.equivFun φ k) •
      ((holomorphicOneFormFinBasis E X).dualBasis k) = φ :=
    (holomorphicOneFormFinBasis E X).dualBasis.sum_equivFun φ
  have h := congrArg (fun ψ => ψ (holomorphicOneFormFinBasis E X i)) hsum
  rw [LinearMap.coe_sum, Finset.sum_apply] at h
  simp only [LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.dualBasis_apply_self] at h
  rw [Finset.sum_eq_single i] at h
  · rw [if_pos rfl, mul_one] at h
    show ((holomorphicOneFormFinBasis E X).dualBasis.equivFun φ) i = _
    exact h
  · intro k _ hki
    rw [if_neg (fun h' => hki h'.symm), mul_zero]
  · intro hi; exact (hi (Finset.mem_univ _)).elim

end JacobianChallenge.HolomorphicForms
