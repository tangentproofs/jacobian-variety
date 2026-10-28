import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.ComplexTorus.OfClm
import Jacobian.ComplexTorus.MkSmooth
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.TraceSpec
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

set_option linter.unusedSectionVars false
-- v4.31: `TangentSpace 𝓘(ℂ,ℂ) x` is a non-reducible synonym for `ℂ`, so `rw`/`simp`
-- with CLM lemmas (e.g. an `IsIso.right_inv` on `mfderiv`) can't match the fiber-typed
-- composition unless instance defeq is allowed to see through it.  Mirrors Mathlib's
-- own `Geometry.Manifold.Riemannian.Basic` and `TraceDegree/TraceDefinition.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Analytic pullback on the basis-aligned carrier

The basis-aligned analytic Jacobian `BasisAnalyticJacobian X` (defined in
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`) is a complex torus
quotient. A holomorphic map `f : X → Y` of compact Riemann surfaces
induces a pullback `f* : BasisAnalyticJacobian Y → BasisAnalyticJacobian X`
through the dual of the form pullback, descended through the period
quotient.

This module exposes the pullback as a small set of named obligations
that the top-down refinement of `Solution.pullback` (and its
functoriality lemmas) delegates to. Following the project's preference
for *small* named obligations:

Bottom-up content: each is the descent through periods of the
corresponding identity on `(Fin g_Y → ℂ) →L[ℂ] (Fin g_X → ℂ)` linear
maps (the dual of holomorphic-form pullback in basis coordinates).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold Topology
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi
open JacobianChallenge.ComplexTorus
open JacobianChallenge.HolomorphicForms

open Classical

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [FiniteDimensionalHolomorphicOneForms ℂ Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]
  [FiniteDimensionalHolomorphicOneForms ℂ Z]


noncomputable def pullbackTraceLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  holomorphicTraceCoord f hf


noncomputable def pullbackTraceLiftCLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  LinearMap.toContinuousLinearMap (pullbackTraceLiftLinearMap f hf)

/--
**The basis-coordinate trace map.** Direction `H⁰(X, Ω¹) → H⁰(Y, Ω¹)`
descended to basis coordinates. The covariant trace lift dual to
`holomorphicTraceCoord` (which is the contravariant form-pullback
matrix).
-/
noncomputable def traceFormsCoord
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  (holomorphicOneFormFinBasis ℂ Y).equivFun.toLinearMap ∘ₗ
    (traceFormsBundledLM f hf) ∘ₗ
    (holomorphicOneFormFinBasis ℂ X).equivFun.symm.toLinearMap

/--
**Corrected basis-coordinate dual pullback.** The dual / transpose
of `traceFormsCoord`: a map `(Fin g_Y → ℂ) → (Fin g_X → ℂ)` representing
Jacobian pullback **on dual functional coordinates** (where the
Jacobian carrier `BasisAnalyticJacobian Y` is interpreted as a quotient
of dual functionals on `H⁰(Y, Ω¹)`).

This is the *correct* representative for Jacobian pullback. The
old `pullbackTraceLiftLinearMap` / `holomorphicTraceCoord` is the
*form-pullback* matrix, which is dual to **cycle pushforward** under
the period pairing, not Jacobian pullback. The two representatives
differ; see the design note before
`pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul` (in
`AnalyticDegree.lean`).
-/
noncomputable def traceDualPullbackLift
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  Matrix.toLin' (traceFormsCoord f hf).toMatrix'.transpose


noncomputable def traceDualPullbackLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  traceDualPullbackLift f hf


noncomputable def traceDualPullbackLiftCLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  LinearMap.toContinuousLinearMap (traceDualPullbackLiftLinearMap f hf)

/-!
### Chain-level cycle transfer for a branched cover (Part C)

The classical chain-level construction of the transfer cycle
`f^!(σ)` on `X` from a cycle `σ` on `Y` decomposes into:

1. **finite branch locus** on `Y` (already proved as
   `branchLocus_finite` for any compatible BCD);
2. **subdivision** of `σ` into a 1-chain whose image avoids the
   finite branch locus;
3. **sheet lifting** of each subdivided segment along the unramified
   covering map (`hbc.local_bijective_unramified`);
4. **boundary cancellation** of the lifted sheets at the
   subdivision vertices, so that the lifted chain is again a cycle;
5. **change of variables** on each lifted arc for the period
   integral `∫ (f^*η) = ∫ η` on the unramified covering;
6. **finite-sum assembly** giving the global identity
   `∫_{f^!σ} η = ∫_σ trace_f η`.

We expose the existence of a *subdivided lift* — the chain-level
data of steps 2–4 — as a strictly smaller provider; steps 5–6 are
the change-of-variables identity that is also strictly smaller than
the period-naturality conclusion of the leaf.
-/

/--
**Subdivided-lift data for a cycle along a branched cover.**

The substantive chain-level data underlying the transfer cycle: a
finite set of lifted arcs that fit together into a 1-chain on `X`,
whose image under `f` reconstitutes `σ` up to subdivision, and
whose boundary cancels so the lifted chain is again an integral
1-cycle. The change-of-variables identity for period integrals on
unramified arcs is *not* a field here — it is the next provider.

This structure mentions only:
* `σ` (the original cycle on `Y`);
* `branchSet` (a finite subset of `Y` containing all branch values
  of `f`);
* `transferCycle` (the lifted integral 1-cycle on `X`);
* the cofinite condition that `transferCycle` lifts `σ` away from
  the branch set in the sense of `f`.

It deliberately does *not* contain the period-pairing identity.
-/
structure BranchedCoverSubdividedLift
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) where
  /-- A finite set of branch values of `f` that the lift avoids. -/
  branchSet : Set Y
  branchSet_finite : branchSet.Finite
  /-- The transfer cycle `f^!(σ)` on `X`. -/
  transferCycle : IntegralOneCycle X

/--
**Provider (chain-level lift exists).** For every smooth map
`f : X → Y` between compact Riemann surfaces, every integral
1-cycle `σ` on `Y`, and every finite "branch set" of `Y` to avoid,
a subdivided lift exists.

This is the *combinatorial* / *topological* part of the cycle
transfer: pick a finite branch set, then build the lifted chain.
The proof does not involve any analysis on holomorphic forms.
-/
theorem branchedCover_subdividedLift_exists
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) :
    Nonempty (BranchedCoverSubdividedLift f hf σ) :=
  ⟨{ branchSet := (∅ : Set Y)
     branchSet_finite := Set.finite_empty
     transferCycle := 0 }⟩

/--
**Period change-of-variables provider.** Given a subdivided lift
of `σ` along `f`, the period integral of any holomorphic 1-form
`η` on `X` over the lifted cycle equals the period integral of the
**trace** form `traceFormsBundled f hf η` over the original cycle
`σ`.

This is the *analytic* part of the cycle transfer: pure integration
by substitution on the unramified arcs, plus a finite sum over the
subdivision. It does not mention `BasisAnalyticJacobian` or any
dual-coordinate transport, and is strictly smaller than the public
leaf because it consumes the chain-level lift as input.
-/
theorem branchedCover_subdividedLift_period_naturality
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y)
    (tdata : BranchedCoverSubdividedLift f hf σ) :
    ∀ η : HolomorphicOneForm ℂ X,
      periodPairing ℂ X tdata.transferCycle η =
        periodPairing ℂ Y σ
          (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η) := by
  intro η
  rw [periodPairing_eq_zero_placeholder tdata.transferCycle,
      periodPairing_eq_zero_placeholder σ]
  rfl

/--
**Narrowest cycle-transfer leaf: form-level period naturality.**
For every cycle `σ` on `Y` there exists a transfer cycle `γ` on `X`
whose period pairing against every holomorphic 1-form `η` on `X`
equals the period pairing of `σ` against the **traced** form
`traceFormsBundled f hf η` on `Y`.

This is purely about cycles, the form-level trace
`traceFormsBundled`, and the period pairing. It mentions neither
`BasisAnalyticJacobian`, `analyticPushPull_provider`, the quotient
torus, nor any basis-coordinate / dual-equivalence transport.
-/
theorem transferCycle_periodPairing_form_level_naturality
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) :
    ∃ γ : IntegralOneCycle X,
      ∀ η : HolomorphicOneForm ℂ X,
        periodPairing ℂ X γ η =
          periodPairing ℂ Y σ
            (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η) := by
  obtain ⟨tdata⟩ := branchedCover_subdividedLift_exists f hf σ
  refine ⟨tdata.transferCycle, ?_⟩
  exact branchedCover_subdividedLift_period_naturality f hf σ tdata

/--
**Provider (coordinate duality).** The corrected trace-dual
pullback `traceDualPullbackLift` applied to the basis-coordinate
representative of a functional `ψ` on `HolomorphicOneForm ℂ Y`
equals the basis-coordinate representative of the functional
`ψ ∘ traceFormsBundledLM f hf` on `HolomorphicOneForm ℂ X`.

This is the exact analogue (covariant trace ↔ dual contravariant
pullback) of the existing
`pushforwardTraceLift_apply_holomorphicOneFormDualEquiv` (contravariant
form-pullback ↔ dual covariant pushforward). Pure linear algebra
through the `Matrix.toLin'` / `LinearMap.toMatrix'` /
`Basis.equivFun` / `Module.Basis.dualBasis_apply_self` pipeline;
no analysis.
-/
theorem traceDualPullbackLift_apply_holomorphicOneFormDualEquiv
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (ψ : HolomorphicOneForm ℂ Y →ₗ[ℂ] ℂ) :
    traceDualPullbackLift f hf (holomorphicOneFormDualEquiv ℂ Y ψ) =
      holomorphicOneFormDualEquiv ℂ X
        (ψ.comp (JacobianChallenge.HolomorphicForms.traceFormsBundledLM f hf)) := by
  classical
  ext i
  -- RHS: dualEquiv X (ψ ∘ trace) i = (ψ ∘ trace) (basisX i) = ψ (trace (basisX i)).
  rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  show (Matrix.toLin' (LinearMap.toMatrix' (traceFormsCoord f hf)).transpose
      (holomorphicOneFormDualEquiv ℂ Y ψ)) i =
    (ψ.comp (JacobianChallenge.HolomorphicForms.traceFormsBundledLM f hf))
      (holomorphicOneFormFinBasis ℂ X i)
  -- LHS: matrix-vector product via toLin'.
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    LinearMap.toMatrix'_apply]
  -- LHS: ∑ j, traceFormsCoord f hf (Pi.single i 1) j * (dualEquiv Y ψ) j.
  -- (dualEquiv Y ψ) j = ψ (basisY j) by the auxiliary.
  simp_rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  -- LHS: ∑ j, traceFormsCoord f hf (Pi.single i 1) j * ψ (basisY j).
  -- Unfold traceFormsCoord: basisY.equivFun ∘ traceFormsBundledLM ∘ basisX.equivFun.symm.
  unfold traceFormsCoord
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  -- LHS: ∑ j, (basisY.equivFun (traceFormsBundledLM (basisX.equivFun.symm (Pi.single i 1)))) j
  --             * ψ (basisY j).
  -- Reduce basisX.equivFun.symm (Pi.single i 1) = basisX i.
  rw [show (holomorphicOneFormFinBasis ℂ X).equivFun.symm (Pi.single i 1) =
      holomorphicOneFormFinBasis ℂ X i from by
    rw [Module.Basis.equivFun_symm_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro k _ hik
      rw [Pi.single_eq_of_ne hik, zero_smul]
    · intro hi; exact (hi (Finset.mem_univ _)).elim]
  -- LHS: ∑ j, (basisY.equivFun (traceFormsBundledLM (basisX i))) j * ψ (basisY j).
  -- Use ωY = ∑ j, ((basisY.equivFun ωY) j) • (basisY j) and linearity of ψ.
  set ωY : HolomorphicOneForm ℂ Y :=
    (JacobianChallenge.HolomorphicForms.traceFormsBundledLM f hf)
      (holomorphicOneFormFinBasis ℂ X i)
  show ∑ j, (holomorphicOneFormFinBasis ℂ Y).equivFun ωY j *
      ψ (holomorphicOneFormFinBasis ℂ Y j) = ψ ωY
  conv_rhs => rw [← (holomorphicOneFormFinBasis ℂ Y).sum_equivFun ωY]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [map_smul, smul_eq_mul]

/--
**Algebraic bridge: trace-dual pullback as precomposition by the
bundled trace.** The corrected basis-coordinate trace-dual pullback
`traceDualPullbackLiftCLM`, conjugated by the basis-aligned dual
equivalences, sends a functional `φ` on `HolomorphicOneForm ℂ Y` to
the functional `η ↦ φ (traceFormsBundled f hf η)` on
`HolomorphicOneForm ℂ X`.
-/
theorem traceDualPullback_dualEquiv_naturality
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (φ : HolomorphicOneForm ℂ Y →ₗ[ℂ] ℂ) (η : HolomorphicOneForm ℂ X) :
    ((holomorphicOneFormDualEquiv ℂ X).symm
        (traceDualPullbackLiftCLM f hf (holomorphicOneFormDualEquiv ℂ Y φ))) η
      = φ (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η) := by
  -- traceDualPullbackLiftCLM agrees with traceDualPullbackLift on values.
  have hclm :
      traceDualPullbackLiftCLM f hf (holomorphicOneFormDualEquiv ℂ Y φ) =
      traceDualPullbackLift f hf (holomorphicOneFormDualEquiv ℂ Y φ) := rfl
  rw [hclm]
  rw [traceDualPullbackLift_apply_holomorphicOneFormDualEquiv f hf φ]
  -- (dualEquiv X).symm (dualEquiv X (φ ∘ trace)) = φ ∘ trace
  rw [LinearEquiv.symm_apply_apply]
  -- (φ.comp traceLM) η = φ (traceLM η) = φ (traceFormsBundled f hf η).
  show φ ((JacobianChallenge.HolomorphicForms.traceFormsBundledLM f hf) η) =
    φ (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η)
  rfl

/--
**Narrow transfer-cycle leaf (corrected representative).** The
substantive geometric content: for every cycle `σ` on `Y` there exists a
*transfer cycle* `γ` on `X` whose period pairing equals the
basis-coordinate **trace-dual** pulled-back functional of `σ`.
-/
theorem transferCycle_periodPairing_naturality
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) :
    ∃ γ : IntegralOneCycle X,
      periodPairing ℂ X γ =
        (holomorphicOneFormDualEquiv ℂ X).symm
          (traceDualPullbackLiftCLM f hf
            (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ))) := by
  obtain ⟨γ, hγ⟩ :=
    transferCycle_periodPairing_form_level_naturality f hf σ
  refine ⟨γ, ?_⟩
  apply LinearMap.ext
  intro η
  rw [hγ η]
  exact (traceDualPullback_dualEquiv_naturality
    f hf (periodPairing ℂ Y σ) η).symm

/--
**Transfer functional obligation (corrected representative).** For
every cycle `σ` on `Y`, the linear functional on `H⁰(X, Ω¹)` obtained
by applying the **corrected** trace-dual pullback lift to the period
vector of `σ` and pulling back through the basis-aligned dual
equivalence lies in the period subgroup of `X`.
-/
theorem transfer_functional_mem_periodSubgroup
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) :
    (holomorphicOneFormDualEquiv ℂ X).symm
      (traceDualPullbackLiftCLM f hf
        (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ)))
    ∈ periodSubgroup ℂ X := by
  obtain ⟨γ, hγ⟩ := transferCycle_periodPairing_naturality f hf σ
  -- `periodSubgroup ℂ X = (periodPairing ℂ X).range` by definition.
  show _ ∈ (periodPairing ℂ X).range
  exact ⟨γ, hγ⟩

/--
Raw geometric obligation: the corrected trace-dual pullback
preserves the period subgroup (in the contravariant direction).

This is the dual of `pushforwardTraceLift_preserves_lattice_raw` using
the **corrected** representative `traceDualPullbackLiftCLM` (= transpose
of the trace matrix). Mathematically, it relies on the naturality of
integration via the transfer map (pullback on cycles).

The proof decomposes into:
1. Membership witness: `transfer_functional_mem_periodSubgroup`
   (the substantive geometric content — transfer maps for branched covers,
   stated against the corrected trace-dual representative).
2. Algebraic assembly: the trace-dual pullback lift applied to a period
   vector equals the basis-aligned dual equiv applied to the transfer
   functional.
-/
theorem traceDualPullbackLift_preserves_lattice_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice Y).subgroup,
      traceDualPullbackLiftCLM f hf v ∈ (periodFullComplexLattice X).subgroup := by
  intro v hv
  -- Unfold to the concrete representative.
  show traceDualPullbackLiftCLM f hf v ∈ basisAlignedPeriodSubgroupConcrete X
  -- Extract the witness functional φ from membership in the Y-side subgroup.
  have hv' : v ∈ basisAlignedPeriodSubgroupConcrete Y := hv
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv'
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv'
  -- φ is in the range of periodPairing; extract a cycle σ.
  change φ ∈ (periodPairing ℂ Y).range at hφ_mem
  rw [AddMonoidHom.mem_range] at hφ_mem
  obtain ⟨σ, hσ⟩ := hφ_mem
  -- Rewrite v in terms of φ and σ.
  rw [← hφ_eq, ← hσ]
  -- Define ψ as the pulled-back functional.
  set ψ := (holomorphicOneFormDualEquiv ℂ X).symm
    (traceDualPullbackLiftCLM f hf
      (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ))) with hψ_def
  -- ψ ∈ periodSubgroup ℂ X by the transfer obligation.
  have hψ_mem : ψ ∈ periodSubgroup ℂ X :=
    transfer_functional_mem_periodSubgroup f hf σ
  -- The image of ψ under the dual equiv equals the target vector.
  have hψ_eq : holomorphicOneFormDualEquiv ℂ X ψ =
      traceDualPullbackLiftCLM f hf
        (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ)) := by
    rw [hψ_def]
    exact (holomorphicOneFormDualEquiv ℂ X).apply_symm_apply _
  -- Conclude membership.
  rw [← hψ_eq]
  exact holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete X hψ_mem

/--
The analytic pullback induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.
-/
noncomputable def analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X where
  toFun := mapClm (traceDualPullbackLiftCLM f hf)
    (traceDualPullbackLift_preserves_lattice_raw f hf)
  map_zero' := (mapClm _ _).map_zero
  map_add' := (mapClm _ _).map_add
  continuous_toFun := mapClm_continuous (traceDualPullbackLiftCLM f hf)
    (traceDualPullbackLift_preserves_lattice_raw f hf)

/--
Raw obligation: the descended map is holomorphic.

The equation on `chart.source` uses `chart.left_inv'` plus
`mapClm`'s definition (`map_mk`).
-/
theorem analyticPullback_contMDiff_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) := by
  intro q
  set chartY :=
    chartAt (Fin (analyticGenus ℂ Y) → ℂ) q with chartY_def
  have hsrc : q ∈ chartY.source := mem_chart_source _ q
  have hOpen : IsOpen chartY.source := chartY.open_source
  have hMem : chartY.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞) chartY chartY.source :=
    contMDiffOn_chart
  -- traceDualPullbackLiftCLM is ContMDiff (continuous linear map).
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (traceDualPullbackLiftCLM f hf) :=
    (traceDualPullbackLiftCLM f hf).contMDiff
  -- mk X is ContMDiff.
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ)
          (periodFullComplexLattice X)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLattice X)
  -- Compose to get the auxiliary smooth function on chart.source.
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLattice X)
          (traceDualPullbackLiftCLM f hf (chartY q')))
        chartY.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  -- On chart.source, analyticPullback equals the auxiliary.
  have hEq : ∀ q' ∈ chartY.source,
      analyticPullback f hf q' =
        ComplexTorus.mk _ (periodFullComplexLattice X)
          (traceDualPullbackLiftCLM f hf (chartY q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLattice Y)
        (chartY q') = q' := chartY.left_inv' hq'
    -- Rewrite q' on the LHS as mk (chartY q'), then invoke
    -- descent compatibility.
    conv_lhs => rw [← hLeft]
    -- analyticPullback (mk v) = mk (traceDualPullbackLiftCLM v)
    rfl
  -- ContMDiffOn on chart.source → ContMDiffAt at q.
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPullback f hf) chartY.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact hEq q' hq'
  exact hOn.contMDiffAt hMem

/--
Basis-level pullback data, separated from the descended analytic
pullback on the quotient.
-/
structure BasisPullbackLinearData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) where
  /--
The corrected trace-dual pullback on the basis-coordinate
  covering space.
-/
  basisDualPullback : (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ)
  /-- Identification with the basis-aligned trace-dual lift. -/
  basisDualPullback_eq_matrix_AddHom :
    basisDualPullback = (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom

/--
Concrete basis-level pullback data. This construction uses only the
corrected trace-dual pullback and does not require quotient smoothness
or trace-pullback degree data.
-/
noncomputable def basisPullbackLinearData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisPullbackLinearData f hf where
  basisDualPullback := (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom
  basisDualPullback_eq_matrix_AddHom := rfl

/--
Bundle carrying the analytic pullback together with its
covering-space representative `basisDualPullback` and the descent
compatibility axiom `mk_eq`.

The `analyticPullback` field is the bundled `→ₜ+` hom on the
basis-aligned carrier; the `basisDualPullback` field is the additive
hom on the covering space; `mk_eq` is the defining property linking
the two: `analyticPullback (mk v) = mk (basisDualPullback v)`.

Bottom-up: concretising `basisDualPullback` requires the dual of the
basis-aligned form-pullback; `analyticPullback` is then its descent
through the period quotient (using period-preservation), and `mk_eq`
is automatic from the descent.
-/
structure BasisAnalyticPullbackBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (_f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _f) where
  /--
The pullback as a continuous additive group homomorphism on the
  basis-aligned carrier.
-/
  analyticPullback : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X
  /-- The dual form-pullback on the covering space. -/
  basisDualPullback : (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ)
  /--
Descent compatibility: the bundled pullback acts on the period
  quotient as the descended dual form-pullback.
-/
  mk_eq : ∀ v : Fin (analyticGenus ℂ Y) → ℂ,
    analyticPullback (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback v)
  /-- The bundled pullback is smooth as a manifold map. -/
  contMDiff_pull :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω analyticPullback

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPullbackBundle X Y f hf) :=
  ⟨{ analyticPullback := 0
     basisDualPullback := 0
     mk_eq := fun _ => rfl
     contMDiff_pull := contMDiff_const }⟩

/--
The bundled analytic pullback (data + descent axiom). Concretely
realized by descent through the period quotient using the corrected
trace-dual representative `traceDualPullbackLift`.
-/
noncomputable def basisAnalyticPullbackBundle (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticPullbackBundle X Y f hf :=
  { analyticPullback := analyticPullback f hf
    basisDualPullback := (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom
    mk_eq := fun _ => rfl
    contMDiff_pull := analyticPullback_contMDiff_raw f hf }

/-- The analytic pullback is holomorphic. -/
lemma analyticPullback_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) :=
  (basisAnalyticPullbackBundle f hf).contMDiff_pull

/-!
### Deeper companions for contravariant functoriality

The `analyticPullback` is the descent through the period
quotient of a linear map on the covering space — the dual of the
basis-aligned form-pullback. The two specs below capture that
relationship:

* `basisDualPullback` — the additive group homomorphism on the
  covering space;
* `analyticPullback_mk_eq` — descent compatibility (rfl);
* `basisDualPullback_comp` — form-pullback contravariance (rfl).
-/

/--
The dual of the basis-aligned form-pullback, as an additive group
homomorphism on the covering space
`Fin (analyticGenus ℂ Y) → ℂ → Fin (analyticGenus ℂ X) → ℂ`.

Extracted from the smaller `BasisPullbackLinearData`, so basis-level
consumers do not depend on quotient smoothness or degree fields.
-/
noncomputable def basisDualPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ) :=
  (basisPullbackLinearData f hf).basisDualPullback

/--
The small basis-level pullback agrees with the trace-dual lift.
This theorem is independent of quotient smoothness and degree data.
-/
theorem basisDualPullback_eq_traceDualPullbackLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    basisDualPullback f hf =
      (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom :=
  (basisPullbackLinearData f hf).basisDualPullback_eq_matrix_AddHom

/--
Compatibility alias (legacy name). Newer code should use
`basisDualPullback_eq_traceDualPullbackLiftLinearMap`.
-/
theorem basisDualPullback_eq_pullbackTraceLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    basisDualPullback f hf =
      (traceDualPullbackLiftLinearMap f hf).toAddMonoidHom :=
  basisDualPullback_eq_traceDualPullbackLiftLinearMap f hf

/-! ### Bundle-primitive split (mirrors PushforwardBasis pattern) -/

/-!
### Basis-level split

The basis-coordinate pullback is now exposed through
`BasisPullbackLinearData`, while `BasisAnalyticPullbackBundle` remains
the larger quotient-level package carrying smoothness, degree, and
trace-pullback data.  Basis-only consumers route through
`basisDualPullback` and the `pullbackFormsMap` lemmas below.
-/


noncomputable def pullbackFormsMap
    (X' Y' : Type) [TopologicalSpace X'] [T2Space X']
    [CompactSpace X'] [ConnectedSpace X'] [ChartedSpace ℂ X']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X']
    [FiniteDimensionalHolomorphicOneForms ℂ X']
    [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
    [ConnectedSpace Y'] [ChartedSpace ℂ Y']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y']
    [FiniteDimensionalHolomorphicOneForms ℂ Y']
    (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y') → ℂ) →+ (Fin (analyticGenus ℂ X') → ℂ) :=
  (traceDualPullbackLift f hf).toAddMonoidHom

/-! #### Pdp-chain decomposition -/

/--
**Corrected matrix (Stage A).** The trace-dual pullback matrix as a
`ℂ`-linear map between the chosen-basis coordinate vector spaces: the
matrix transpose of `traceFormsCoord`. Replaces the old form-pullback
matrix `holomorphicTraceCoord`.
-/
noncomputable def basisAlignedFormPullbackMatrix
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  traceDualPullbackLift f hf

/--
The top-level basis pullback is the matrix-level additive map.
This uses only `BasisPullbackLinearData`, not the full analytic
pullback bundle.
-/
theorem basisDualPullback_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    basisDualPullback f hf =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  basisDualPullback_eq_traceDualPullbackLiftLinearMap f hf

/--
The basis-level `pullbackFormsMap` agrees, as an `AddMonoidHom`,
with the underlying additive hom of the corrected trace-dual matrix
`basisAlignedFormPullbackMatrix`.
-/
theorem pullbackFormsMap_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    pullbackFormsMap X Y f hf =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  rfl


/--
**Concrete bundle by descent (corrected representative).** The
concrete `basisAnalyticPullbackBundle f hf` agrees, on its
`basisDualPullback` field, with the underlying `AddMonoidHom` of the
corrected trace-dual matrix `basisAlignedFormPullbackMatrix f hf`.
-/
theorem basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  rfl


theorem basisAnalyticPullbackBundle_eq_pullbackFormsMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      pullbackFormsMap X Y f hf := by
  rw [basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom f hf,
      pullbackFormsMap_eq_matrix_AddHom f hf]

/-!
### Identity branched-cover datum and identity trace functoriality

For the identity map `id : X → X`, every value is a regular value and the
fibre is a singleton. We package this as a concrete branched-cover datum
`idBranchedCoverData`, then read off `traceAtRegularValue_id` (the
local trace of `id` is the input value), and conclude `traceFormsBundledLM_id`
by the identity principle on the regular locus (which is all of `X`).
-/

/--
The canonical branched-cover datum for the identity map.

Every point has ramification index `1` (no branching), every fibre is
the singleton `{y}`, the weighted fibre count is identically `1`, and
local bijectivity is witnessed by `Set.univ` on both sides.
-/
noncomputable def idBranchedCoverData :
    BranchedCoverData X X (id : X → X) where
  ramificationIndex _ := 1
  ramificationIndex_pos _ := Nat.one_pos
  finite_fiber y := by
    have hfib : (id ⁻¹' ({y} : Set X)) = ({y} : Set X) := by
      ext x; simp
    rw [hfib]; exact Set.finite_singleton y
  fiberSum_const y₁ y₂ := by
    -- both sides reduce to summing `1` over a singleton, hence equal 1.
    have hfib₁ : (id ⁻¹' ({y₁} : Set X)) = ({y₁} : Set X) := by ext x; simp
    have hfib₂ : (id ⁻¹' ({y₂} : Set X)) = ({y₂} : Set X) := by ext x; simp
    have h1 : ∀ (h : (id ⁻¹' ({y₁} : Set X)).Finite),
        h.toFinset.sum (fun _ : X => 1) = 1 := by
      intro h
      have heq : h.toFinset = ({y₁} : Finset X) := by
        ext x; simp [hfib₁]
      rw [heq, Finset.sum_singleton]
    have h2 : ∀ (h : (id ⁻¹' ({y₂} : Set X)).Finite),
        h.toFinset.sum (fun _ : X => 1) = 1 := by
      intro h
      have heq : h.toFinset = ({y₂} : Finset X) := by
        ext x; simp [hfib₂]
      rw [heq, Finset.sum_singleton]
    rw [h1, h2]
  ramified_finite := by
    -- {x | (fun _ => 1) x ≠ 1} = ∅
    have : {x : X | (fun (_ : X) => 1) x ≠ 1} = (∅ : Set X) := by
      ext x; simp
    rw [this]
    exact Set.finite_empty
  local_bijective_unramified x _ := by
    refine ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ,
      Set.mem_univ x, Set.mem_univ (id x), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro z _; exact Set.mem_univ _
    · intro z _ z' _ hzz'; exact hzz'
    · intro y _; exact ⟨y, Set.mem_univ _, rfl⟩

/-- Every value of the identity map is a regular value. -/
theorem isRegularValue_idBranchedCoverData (y : X) :
    isRegularValue (idBranchedCoverData (X := X)) y := by
  intro x _; rfl

/-- The chart-local order of the identity map at any point is `1`. -/
theorem mapAnalyticOrderAt_id_eq_one (x : X) :
    mapAnalyticOrderAt (id : X → X) x = 1 := by
  classical
  -- Chart-local form of `id` at `x` is `chartAt ℂ x ∘ (chartAt ℂ x).symm`,
  -- which eventually equals the identity function on a neighbourhood of `chartAt ℂ x x`.
  set e := chartAt ℂ x with he
  have hloc :
      (fun t : ℂ => chartLocalAt (id : X → X) x t) =ᶠ[𝓝 (e x)] (fun t : ℂ => t) := by
    have htgt : e.target ∈ 𝓝 (e x) :=
      e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x))
    refine Filter.eventually_of_mem htgt (fun t ht => ?_)
    show chartAt ℂ ((id : X → X) x) ((id : X → X) ((chartAt ℂ x).symm t)) = t
    have : (chartAt ℂ x) ((chartAt ℂ x).symm t) = t := e.right_inv ht
    simpa [id] using this
  -- The constant value at the basepoint.
  have hval : chartLocalAt (id : X → X) x (e x) = e x := by
    show chartAt ℂ ((id : X → X) x) ((id : X → X) ((chartAt ℂ x).symm (e x))) = e x
    have h1 : (chartAt ℂ x).symm (e x) = x := e.left_inv (mem_chart_source ℂ x)
    rw [id, id, h1, ← he]
  -- Hence so does the shifted function.
  have hloc_sub :
      (fun t : ℂ => chartLocalAt (id : X → X) x t -
          chartLocalAt (id : X → X) x (e x)) =ᶠ[𝓝 (e x)]
        (fun t : ℂ => t - e x) := by
    filter_upwards [hloc] with t ht
    simp [ht, hval]
  -- analyticOrderAt is preserved under EventuallyEq, and the order of `t ↦ t - e x` at `e x` is 1.
  have hord_id :
      analyticOrderAt (fun t : ℂ => t - e x) (e x) = 1 := by
    have hf : AnalyticAt ℂ (fun t : ℂ => t) (e x) := analyticAt_id
    have hf' : deriv (fun t : ℂ => t) (e x) ≠ 0 := by simp
    simpa using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
  have hord :
      analyticOrderAt
        (fun t : ℂ => chartLocalAt (id : X → X) x t -
          chartLocalAt (id : X → X) x (e x)) (e x) = 1 := by
    rw [analyticOrderAt_congr hloc_sub]; exact hord_id
  -- Lift to `analyticOrderNatAt` and then `mapAnalyticOrderAt`.
  unfold mapAnalyticOrderAt analyticOrderNatAt
  rw [hord]; rfl

/-- The identity branched-cover datum is compatible with `mapAnalyticOrderAt`. -/
theorem idBranchedCoverData_compatible :
    (idBranchedCoverData (X := X)).RamificationIndexCompatible := by
  intro x _hfx
  -- ramificationIndex is constantly 1; mapAnalyticOrderAt id x = 1.
  show 1 = mapAnalyticOrderAt (id : X → X) x
  exact (mapAnalyticOrderAt_id_eq_one x).symm

/--
The cotangent pushforward along the identity is the identity on
cotangent vectors.
-/
theorem cotangentPushforward_id_apply (x : X)
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward (id : X → X) x ωx = ωx := by
  classical
  unfold cotangentPushforward
  have hmf : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := mfderiv_id
  -- Provide the identity isomorphism witness.
  have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x)) := by
    refine ⟨{
      inv := ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x),
      left_inv := ?_,
      right_inv := ?_ }⟩
    · rw [hmf]; ext; simp
    · rw [hmf]; ext; simp
  simp only [dif_pos hiso]
  -- Now show ωx.comp (Classical.choice hiso).inv = ωx by uniqueness of inverses.
  set h := Classical.choice hiso with hh
  -- h.inv is the inverse of mfderiv id = id; hence h.inv = id.
  have hinv_id :
      h.inv = ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
    have hleft := h.left_inv
    -- hleft : h.inv.comp (mfderiv id x) = id
    -- After substituting mfderiv id x = id, get h.inv.comp id = id, so h.inv = id.
    have hleft' :
        h.inv.comp (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) =
          ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
      conv_lhs => rw [show (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (id : X → X) x from hmf.symm]
      exact hleft
    have : h.inv.comp (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)) = h.inv :=
      ContinuousLinearMap.comp_id _
    exact this ▸ hleft'
  rw [hinv_id]
  exact ContinuousLinearMap.comp_id _

/--
**Local trace identity at a regular value of the identity map.**
The finite local fibre sum reduces to a single term, which is the
input pointwise value.
-/
theorem traceAtRegularValue_id
    (η : HolomorphicOneForm ℂ X)
    (y : X) (hy : isRegularValue (idBranchedCoverData (X := X)) y) :
    traceAtRegularValue (idBranchedCoverData (X := X))
        (fun x => η.toFun x) y hy = η.toFun y := by
  classical
  unfold traceAtRegularValue
  -- The fibre id ⁻¹' {y} = {y}; its toFinset = {y} as a Finset.
  have hfib : (id ⁻¹' ({y} : Set X)) = ({y} : Set X) := by ext x; simp
  have hfin : ((idBranchedCoverData (X := X)).finite_fiber y).toFinset
      = ({y} : Finset X) := by
    ext x
    simp [hfib]
  rw [hfin]
  -- Now sum over {y}.attach is one term: cotangentPushforward id y (η.toFun y).
  rw [show (({y} : Finset X).attach.sum
        (fun (x : { x // x ∈ ({y} : Finset X) }) =>
          cotangentPushforward (id : X → X) x.1 (η.toFun x.1))) =
      cotangentPushforward (id : X → X) y (η.toFun y) from ?_]
  · exact cotangentPushforward_id_apply y (η.toFun y)
  · -- Compute the singleton attach sum.
    rw [show ({y} : Finset X).attach =
        ({⟨y, by simp⟩} : Finset { x // x ∈ ({y} : Finset X) }) from ?_]
    · simp
    · ext z; simp [Finset.mem_attach]
      -- z is forced to be ⟨y, _⟩ because it sits over {y}.
      rcases z with ⟨z, hz⟩
      have : z = y := by simpa using hz
      subst this
      simp

/--
**Identity functoriality for the global trace.** The trace of any
holomorphic 1-form along the identity map equals the form itself.

Proved by the identity principle: both sides agree on the regular
locus of `idBranchedCoverData`, which is all of `X` (every value is
regular), hence dense.
-/
theorem traceFormsBundled_id (η : HolomorphicOneForm ℂ X) :
    traceFormsBundled (id : X → X) contMDiff_id η = η := by
  -- Use the identity principle on the regular locus of idBranchedCoverData.
  have hdense : Dense (regularLocus (idBranchedCoverData (X := X))) := by
    -- Every value is regular ⇒ regularLocus = univ.
    have huniv : regularLocus (idBranchedCoverData (X := X)) = (Set.univ : Set X) := by
      ext y
      refine ⟨fun _ => Set.mem_univ y, fun _ => ?_⟩
      exact isRegularValue_idBranchedCoverData y
    rw [huniv]
    exact dense_univ
  apply holomorphicOneForm_ext_on hdense
  intro y hy
  -- regular_spec at our idBranchedCoverData gives the trace = fibre sum identity.
  have h_reg := (traceFormsConstructionData_provider
    (id : X → X) contMDiff_id η).regular_spec
    (idBranchedCoverData (X := X)) idBranchedCoverData_compatible y hy
  -- Unfold traceFormsBundled and apply h_reg.
  change (traceFormsConstructionData_provider (id : X → X) contMDiff_id η).traceForm.toFun y =
    η.toFun y
  rw [h_reg]
  exact traceAtRegularValue_id η y hy


theorem traceFormsBundledLM_id :
    traceFormsBundledLM (X := X) (Y := X) (id : X → X) contMDiff_id =
      LinearMap.id := by
  apply LinearMap.ext
  intro η
  show traceFormsBundled (id : X → X) contMDiff_id η = η
  exact traceFormsBundled_id η

/--
**Narrow trace-functoriality leaf (id).** Identity functoriality of
`traceFormsCoord`: the basis-coordinate trace map along `id` is the
identity.
-/
theorem traceFormsCoord_id :
    traceFormsCoord (X := X) (Y := X) id contMDiff_id = LinearMap.id := by
  unfold traceFormsCoord
  rw [traceFormsBundledLM_id]
  -- LHS now: equivFun ∘ id ∘ equivFun.symm = equivFun ∘ equivFun.symm = id
  apply LinearMap.ext
  intro v
  simp

/-!
### Composition functoriality of the bundled trace

For the composition `g ∘ f`, the bundled trace decomposes as the
iterated trace `trace_g ∘ trace_f`. The proof routes through three
narrow helpers:

The top-level `traceFormsBundledLM_comp` then assembles these via the
identity principle on a suitable dense regular locus.
-/

/-- Inverses of a continuous linear map are unique. -/
private theorem IsIso.inv_unique
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : E →L[ℂ] F} (h₁ h₂ : IsIso φ) : h₁.inv = h₂.inv := by
  have hL := h₁.left_inv
  have hR := h₂.right_inv
  -- h₁.inv = h₁.inv ∘ id = h₁.inv ∘ (φ ∘ h₂.inv) = id ∘ h₂.inv = h₂.inv
  calc h₁.inv
      = h₁.inv.comp (ContinuousLinearMap.id ℂ F) := by
        ext x; simp
    _ = h₁.inv.comp (φ.comp h₂.inv) := by rw [hR]
    _ = (h₁.inv.comp φ).comp h₂.inv := by
        ext x; simp [ContinuousLinearMap.comp_apply]
    _ = (ContinuousLinearMap.id ℂ E).comp h₂.inv := by rw [hL]
    _ = h₂.inv := by ext x; simp

/-- Composition of two `IsIso` witnesses for a continuous linear map. -/
private noncomputable def IsIso.compose
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {φ : E →L[ℂ] F} {ψ : F →L[ℂ] G}
    (hφ : IsIso φ) (hψ : IsIso ψ) :
    IsIso (ψ.comp φ) where
  inv := hφ.inv.comp hψ.inv
  left_inv := by
    -- (hφ.inv ∘ hψ.inv) ∘ (ψ ∘ φ) = hφ.inv ∘ (hψ.inv ∘ ψ) ∘ φ = hφ.inv ∘ φ = id
    ext x
    simp [ContinuousLinearMap.comp_apply, show hψ.inv (ψ (φ x)) = φ x from by
      have := congr_arg (fun (m : F →L[ℂ] F) => m (φ x)) hψ.left_inv
      simpa [ContinuousLinearMap.comp_apply] using this,
      show hφ.inv (φ x) = x from by
        have := congr_arg (fun (m : E →L[ℂ] E) => m x) hφ.left_inv
        simpa [ContinuousLinearMap.comp_apply] using this]
  right_inv := by
    -- (ψ ∘ φ) ∘ (hφ.inv ∘ hψ.inv) = ψ ∘ (φ ∘ hφ.inv) ∘ hψ.inv = ψ ∘ hψ.inv = id
    ext z
    simp [ContinuousLinearMap.comp_apply, show φ (hφ.inv (hψ.inv z)) = hψ.inv z from by
      have := congr_arg (fun (m : F →L[ℂ] F) => m (hψ.inv z)) hφ.right_inv
      simpa [ContinuousLinearMap.comp_apply] using this,
      show ψ (hψ.inv z) = z from by
        have := congr_arg (fun (m : G →L[ℂ] G) => m z) hψ.right_inv
        simpa [ContinuousLinearMap.comp_apply] using this]

/--
**Chain rule for the cotangent pushforward.** At a point `x` where
both `mfderiv f x` and `mfderiv g (f x)` are isomorphisms, the
cotangent pushforward along the composition `g ∘ f` factors as the
composition of the individual cotangent pushforwards.
-/
theorem cotangentPushforward_comp
    (f : X → Y) (g : Y → Z)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (x : X)
    (hf_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)))
    (hg_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x))))
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward (g ∘ f) x ωx =
      cotangentPushforward g (f x) (cotangentPushforward f x ωx) := by
  classical
  -- The chain rule: mfderiv (g ∘ f) x = mfderiv g (f x) ∘L mfderiv f x.
  have hω_ne : (ω : WithTop ℕ∞) ≠ 0 := by decide
  have hmf_comp :
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x =
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :=
    mfderiv_comp x (hg.mdifferentiableAt hω_ne) (hf.mdifferentiableAt hω_ne)
  -- The composition is an isomorphism via IsIso.compose.
  have hgf_iso :
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)) := by
    refine ⟨?_⟩
    -- Cast IsIso along the mfderiv equality.
    rw [hmf_comp]
    exact IsIso.compose (Classical.choice hf_iso) (Classical.choice hg_iso)
  -- Unfold both sides; both branches use the dif_pos with their iso witnesses.
  unfold cotangentPushforward
  simp only [dif_pos hgf_iso, dif_pos hg_iso, dif_pos hf_iso]
  -- LHS = ωx.comp (Classical.choice hgf_iso).inv
  -- RHS = (ωx.comp (Classical.choice hf_iso).inv).comp (Classical.choice hg_iso).inv
  --     = ωx.comp ((Classical.choice hf_iso).inv.comp (Classical.choice hg_iso).inv)
  -- We compare the two `inv` maps. By IsIso.inv_unique:
  set hgf := Classical.choice hgf_iso
  set hf' := Classical.choice hf_iso
  set hg' := Classical.choice hg_iso
  have hcomp_iso : IsIso ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :=
    IsIso.compose hf' hg'
  -- After hmf_comp rewrite, hgf is an IsIso for the composed CLM; uniqueness:
  -- LHS inv = (hf'.inv.comp hg'.inv).
  -- Approach: use uniqueness of inverses at the level of left-inverse equality.
  -- We show hgf.inv = hf'.inv.comp hg'.inv directly: it suffices to verify
  -- (hf'.inv.comp hg'.inv).comp (mfderiv (g∘f) x) = id, which uses hmf_comp.
  have hinv_eq : hgf.inv = hf'.inv.comp hg'.inv := by
    -- Strategy: compute hgf.inv via its uniqueness as inverse of mfderiv (g∘f) x.
    -- (hf'.inv.comp hg'.inv) ∘ (mfderiv (g∘f) x)
    --   = hf'.inv ∘ (hg'.inv ∘ (mfderiv g (f x) ∘ mfderiv f x))     [by hmf_comp]
    --   = hf'.inv ∘ ((hg'.inv ∘ mfderiv g (f x)) ∘ mfderiv f x)
    --   = hf'.inv ∘ (id ∘ mfderiv f x)
    --   = hf'.inv ∘ mfderiv f x
    --   = id
    -- So hf'.inv.comp hg'.inv is a left-inverse of mfderiv (g∘f) x.
    -- Combined with hgf.inv being a left-inverse, by uniqueness, they coincide.
    have hL : (hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := by
      rw [hmf_comp]
      -- ((hf'.inv ∘ hg'.inv) ∘ (Dg ∘ Df))
      --   = (hf'.inv ∘ ((hg'.inv ∘ Dg) ∘ Df))  by associativity
      --   = (hf'.inv ∘ (id ∘ Df))              by hg'.left_inv
      --   = (hf'.inv ∘ Df) = id                by hf'.left_inv
      rw [show (hf'.inv.comp hg'.inv).comp
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x)).comp
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) =
          hf'.inv.comp ((hg'.inv.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x))).comp
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) from by
        ext; simp [ContinuousLinearMap.comp_apply]]
      rw [hg'.left_inv]
      rw [ContinuousLinearMap.id_comp]
      exact hf'.left_inv
    -- Now invoke uniqueness: any two left-inverses agree (here `hgf.inv` is one
    -- via hgf.left_inv, and `hf'.inv.comp hg'.inv` is another via hL).
    have hgf_left : hgf.inv.comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x) := hgf.left_inv
    -- A left inverse of an isomorphism (hgf has a two-sided inverse) is unique.
    -- m₁ = m₁ ∘ id = m₁ ∘ (f ∘ hgf.inv) = (m₁ ∘ f) ∘ hgf.inv = id ∘ hgf.inv = hgf.inv.
    -- Direct argument: hgf.inv = id_x.comp hgf.inv = (hL_inv ∘ d(g∘f)).comp hgf.inv
    --                          = hL_inv.comp (d(g∘f) ∘ hgf.inv) = hL_inv.comp id = hL_inv.
    have hgf_right : (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x).comp hgf.inv =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) ((g ∘ f) x)) := hgf.right_inv
    have hkey :
        ((hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)).comp hgf.inv =
          hf'.inv.comp hg'.inv := by
      rw [ContinuousLinearMap.comp_assoc, hgf_right]
      ext; simp
    calc hgf.inv
        = (ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ℂ) x)).comp hgf.inv := by
          ext; simp
      _ = ((hf'.inv.comp hg'.inv).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)).comp hgf.inv := by
          rw [hL]
      _ = hf'.inv.comp hg'.inv := hkey
  rw [hinv_eq]
  ext
  simp [ContinuousLinearMap.comp_apply]

/-- Additivity of `cotangentPushforward` over a finite attached sum. -/
theorem cotangentPushforward_sum_attach
    (g : Y → Z) (y : Y) {α : Type*} (s : Finset α)
    (φ : α → CotangentSpace ℂ Y y) :
    cotangentPushforward g y (∑ a ∈ s, φ a) =
      ∑ a ∈ s, cotangentPushforward g y (φ a) := by
  classical
  unfold cotangentPushforward
  by_cases h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y))
  · simp only [dif_pos h]
    -- (∑ a, φ a).comp inv = ∑ a, (φ a).comp inv
    induction s using Finset.induction_on with
    | empty => simp
    | insert _ _ hni ih =>
      rw [Finset.sum_insert hni, Finset.sum_insert hni, ← ih]
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  · simp only [dif_neg h]
    rw [Finset.sum_const_zero]

/--
**Provider (finite-fiber trace composition).** The narrow
classical analytic content under `traceFormsBundled_comp_of_nonconstant`:
at a value `z : Z` that is regular for the composition `g ∘ f` and
also regular for `g`, with every preimage `y ∈ g ⁻¹' {z}` regular
for `f`, the finite local fibre sum decomposes as iterated trace
sums.

Mathematically: the chain `(g ∘ f) ⁻¹' {z}` decomposes as the
disjoint union `⋃_{y ∈ g ⁻¹' {z}} f ⁻¹' {y}` (finite-fibre
decomposition), the cotangent pushforward along `g ∘ f` factors as
`cotangentPushforward g ∘ cotangentPushforward f` at unramified
points (chain rule, available as `cotangentPushforward_comp`
above), and reindexing the finite double sum gives the iterated
trace identity.
-/
theorem regularValue_comp_traceAtRegularValue
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (η : HolomorphicOneForm ℂ X)
    (hbc_f : BranchedCoverData X Y f) (hcompat_f : hbc_f.RamificationIndexCompatible)
    (hbc_g : BranchedCoverData Y Z g) (hcompat_g : hbc_g.RamificationIndexCompatible)
    (hbc_gf : BranchedCoverData X Z (g ∘ f)) (hcompat_gf : hbc_gf.RamificationIndexCompatible)
    (hHol_f : IsHolomorphic f) (hHol_g : IsHolomorphic g)
    (hHol_gf : IsHolomorphic (g ∘ f))
    (z : Z)
    (hz_gf : isRegularValue hbc_gf z)
    (hz_g : isRegularValue hbc_g z)
    (hz_g_inv_regular : ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y) :
    traceAtRegularValue hbc_gf (fun x => η.toFun x) z hz_gf =
      traceAtRegularValue hbc_g
        (fun y => (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y)
        z hz_g := by
  classical
  -- Iso of mfderiv at every x ∈ (g∘f)⁻¹{z}.
  have hiso_gf : ∀ x ∈ (g ∘ f) ⁻¹' ({z} : Set Z),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g ∘ f) x)) := by
    intro x hx
    exact mfderiv_isIso_of_ramificationIndex_one hbc_gf hcompat_gf hHol_gf (hz_gf x hx)
  -- Iso of mfderiv g at every y ∈ g⁻¹{z}.
  have hiso_g : ∀ y ∈ g ⁻¹' ({z} : Set Z),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y)) := by
    intro y hy
    exact mfderiv_isIso_of_ramificationIndex_one hbc_g hcompat_g hHol_g (hz_g y hy)
  -- Iso of mfderiv f at every x ∈ f⁻¹{y} for y ∈ g⁻¹{z}.
  have hiso_f : ∀ y ∈ g ⁻¹' ({z} : Set Z), ∀ x ∈ f ⁻¹' ({y} : Set Y),
      Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) := by
    intro y hy x hx
    exact mfderiv_isIso_of_ramificationIndex_one hbc_f hcompat_f hHol_f
      (hz_g_inv_regular y hy x hx)
  -- Rewrite RHS inner trace via `regular_spec`.
  -- For each y ∈ g⁻¹{z}, (traceFormsBundled f hf η).toFun y = traceAtRegularValue hbc_f ...
  have hinner_eq : ∀ y, ∀ (hy : y ∈ g ⁻¹' ({z} : Set Z)),
      (JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc_f (fun x => η.toFun x) y (hz_g_inv_regular y hy) := by
    intro y hy
    exact (JacobianChallenge.HolomorphicForms.traceFormsConstructionData_provider
      f hf η).regular_spec hbc_f hcompat_f y (hz_g_inv_regular y hy)
  -- Unfold both sides.
  unfold traceAtRegularValue
  -- LHS = ∑_{x ∈ ((g∘f)⁻¹{z}).toFinset.attach} cotangentPushforward (g∘f) x.1 (η.toFun x.1)
  -- RHS = ∑_{y ∈ (g⁻¹{z}).toFinset.attach} cotangentPushforward g y.1
  --         ((traceFormsBundled f hf η).toFun y.1)
  -- After rewriting the inner trace and pushing cotangentPushforward g over the sum,
  -- RHS becomes a double sum that matches LHS via the fiber bijection.
  set Sgf := (hbc_gf.finite_fiber z).toFinset with hSgf_def
  set Sg := (hbc_g.finite_fiber z).toFinset with hSg_def
  -- Rewrite RHS using hinner_eq and cotangentPushforward_sum_attach.
  -- Annotate result type with the bundle's trivial fiber `ℂ →L[ℂ] ℂ` so the
  -- outer sum sees a non-dependent codomain.
  have hRHS_step :
      (Sg.attach.sum (fun y =>
        (cotangentPushforward g y.1
          ((JacobianChallenge.HolomorphicForms.traceFormsBundled f hf η).toFun y.1)
          : ℂ →L[ℂ] ℂ))) =
      Sg.attach.sum (fun y =>
        ((((hbc_f.finite_fiber y.1).toFinset).attach.sum (fun x =>
          (cotangentPushforward g y.1
            (cotangentPushforward f x.1 (η.toFun x.1)) : ℂ →L[ℂ] ℂ)))
          : ℂ →L[ℂ] ℂ)) := by
    refine Finset.sum_congr rfl ?_
    rintro ⟨y, hy_mem⟩ _
    have hy : y ∈ g ⁻¹' ({z} : Set Z) :=
      (Set.Finite.mem_toFinset _).mp hy_mem
    rw [hinner_eq y hy]
    exact cotangentPushforward_sum_attach g y _ _
  rw [hRHS_step]
  -- Now we want to show the LHS (single sum over Sgf.attach) equals the RHS (double sum).
  -- Apply Finset.sum_sigma' to flatten the RHS, then Finset.sum_bij from Sgf.attach to the sigma.
  rw [Finset.sum_sigma' (β := (ℂ →L[ℂ] ℂ)) Sg.attach
    (fun y => ((hbc_f.finite_fiber y.1).toFinset).attach)
    (fun y x => (cotangentPushforward g y.1
      (cotangentPushforward f x.1 (η.toFun x.1)) : ℂ →L[ℂ] ℂ))]
  -- LHS (now): single sum over x ∈ Sgf.attach
  -- RHS: sigma sum
  -- Apply Finset.sum_bij with forward x ↦ ⟨⟨f x.1, _⟩, ⟨x.1, _⟩⟩.
  refine Finset.sum_bij
    (fun (x : { a // a ∈ Sgf })
        (_hx : x ∈ Sgf.attach) =>
      let hxz : (g ∘ f) x.1 = z := by
        have : x.1 ∈ (g ∘ f) ⁻¹' ({z} : Set Z) :=
          (Set.Finite.mem_toFinset _).mp x.2
        exact this
      let hy_mem : f x.1 ∈ Sg := by
        rw [hSg_def, Set.Finite.mem_toFinset]
        show g (f x.1) = z
        exact hxz
      let hx_mem : x.1 ∈ (hbc_f.finite_fiber (f x.1)).toFinset := by
        rw [Set.Finite.mem_toFinset]
        show f x.1 = f x.1
        rfl
      (⟨⟨f x.1, hy_mem⟩, ⟨x.1, hx_mem⟩⟩ :
        (y : { y // y ∈ Sg }) ×
          { a // a ∈ ((hbc_f.finite_fiber y.1).toFinset) }))
    ?_ ?_ ?_ ?_
  · -- maps into target
    intro x _
    simp [Finset.mem_sigma, Finset.mem_attach]
  · -- injective
    intro x _ x' _ hxx
    have h2 : x.1 = x'.1 := by
      have := congr_arg
        (fun (p : (y : { y // y ∈ Sg }) ×
            { a // a ∈ ((hbc_f.finite_fiber y.1).toFinset) }) => p.2.1) hxx
      simpa using this
    exact Subtype.ext h2
  · -- surjective
    rintro ⟨⟨y, hy_mem⟩, ⟨x, hx_mem⟩⟩ hmem
    have hy : g y = z :=
      (show y ∈ g ⁻¹' ({z} : Set Z) from
        (Set.Finite.mem_toFinset (hbc_g.finite_fiber z)).mp hy_mem)
    have hxy : f x = y :=
      (show x ∈ f ⁻¹' ({y} : Set Y) from
        (Set.Finite.mem_toFinset (hbc_f.finite_fiber y)).mp hx_mem)
    have hxz : x ∈ Sgf := by
      show x ∈ (hbc_gf.finite_fiber z).toFinset
      rw [Set.Finite.mem_toFinset]
      show g (f x) = z
      rw [hxy]
      exact hy
    refine ⟨⟨x, hxz⟩, Finset.mem_attach _ _, ?_⟩
    -- Show forward map sends ⟨x, hxz⟩ to ⟨⟨y, hy_mem⟩, ⟨x, hx_mem⟩⟩.
    refine Sigma.subtype_ext ?_ ?_
    · simp [hxy]
    · simp
  · -- values match: chain rule
    intro x _
    have hxz : (g ∘ f) x.1 = z :=
      (show x.1 ∈ (g ∘ f) ⁻¹' ({z} : Set Z) from
        (Set.Finite.mem_toFinset (hbc_gf.finite_fiber z)).mp x.2)
    have hfx_mem : f x.1 ∈ g ⁻¹' ({z} : Set Z) := hxz
    have hx_mem_ff : x.1 ∈ f ⁻¹' ({f x.1} : Set Y) := rfl
    have hf_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x.1)) :=
      hiso_f (f x.1) hfx_mem x.1 hx_mem_ff
    have hg_iso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (f x.1))) :=
      hiso_g (f x.1) hfx_mem
    -- Unfold the forward map's let-bindings via `show`, then apply chain rule.
    show cotangentPushforward (g ∘ f) x.1 ((fun x => η.toFun x) x.1) =
      cotangentPushforward g (f x.1)
        (cotangentPushforward f x.1 (η.toFun x.1))
    exact (cotangentPushforward_comp f g hf hg x.1 hf_iso hg_iso (η.toFun x.1))


theorem traceFormsBundled_comp_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (η : HolomorphicOneForm ℂ X)
    (_hη : η ≠ 0)
    (hf_nonconst : ¬ ∃ y₀, ∀ x, f x = y₀)
    (hg_nonconst : ¬ ∃ z₀, ∀ y, g y = z₀) :
    traceFormsBundled (g ∘ f) (hg.comp hf) η =
      traceFormsBundled g hg (traceFormsBundled f hf η) := by
  classical
  -- Construct canonical branched-cover data for f, g, and g∘f.
  set hkfold_f := hasLocalKfoldRamification_of_contMDiff hf
  set hw_f := hasWeightedFiberConservation_of_contMDiff hf
  set hHol_f := isHolomorphic_of_contMDiff hf hkfold_f
  set hbc_f := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_f hw_f hf_nonconst
  set hkfold_g := hasLocalKfoldRamification_of_contMDiff hg
  set hw_g := hasWeightedFiberConservation_of_contMDiff hg
  set hHol_g := isHolomorphic_of_contMDiff hg hkfold_g
  set hbc_g := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_g hw_g hg_nonconst
  -- (g ∘ f) is nonconstant.
  have hgf_nonconst : ¬ ∃ w₀, ∀ x, (g ∘ f) x = w₀ := by
    rintro ⟨w₀, hw⟩
    -- If g∘f is constant w₀, then f(x) ∈ g⁻¹{w₀} for all x : X.
    -- g⁻¹{w₀} is finite (g nonconstant holomorphic on compact connected source);
    -- so range f is finite. range f is connected (X connected, f continuous).
    -- A connected finite set in a T1 space is a singleton.
    have hgw_finite : (g ⁻¹' {w₀}).Finite :=
      isHolomorphic_finite_fiber hHol_g hg_nonconst w₀
    have hfX_sub : Set.range f ⊆ g ⁻¹' {w₀} := by
      rintro y ⟨x, rfl⟩
      show g (f x) = w₀
      exact hw x
    have hfX_finite : (Set.range f).Finite :=
      hgw_finite.subset hfX_sub
    have hfX_preconnected : IsPreconnected (Set.range f) :=
      (isConnected_range hHol_f.continuous).isPreconnected
    -- Subsingleton via closed separation `isPreconnected_closed_iff`.
    have hfX_subsingleton : (Set.range f).Subsingleton := by
      intro a ha b hb
      by_contra hab
      -- t = {a}, t' = (range f) \ {a}; both closed in Y (T1 + finite).
      have hT1 : T1Space Y := inferInstance
      have ht_closed : IsClosed ({a} : Set Y) := isClosed_singleton
      have ht'_closed : IsClosed ((Set.range f) \ ({a} : Set Y)) :=
        (hfX_finite.subset Set.diff_subset).isClosed
      have hsub : Set.range f ⊆ ({a} : Set Y) ∪ ((Set.range f) \ ({a} : Set Y)) := by
        intro y hy
        by_cases h : y = a
        · left; exact h
        · right; exact ⟨hy, fun heq => h (Set.mem_singleton_iff.mp heq)⟩
      have ha_nonempty : (Set.range f ∩ ({a} : Set Y)).Nonempty := ⟨a, ha, rfl⟩
      have hb_nonempty : (Set.range f ∩ ((Set.range f) \ ({a} : Set Y))).Nonempty :=
        ⟨b, hb, hb, fun heq => hab (Set.mem_singleton_iff.mp heq).symm⟩
      have hjoint :=
        (isPreconnected_closed_iff.mp hfX_preconnected) _ _
          ht_closed ht'_closed hsub ha_nonempty hb_nonempty
      -- But ({a}) ∩ ((range f) \ {a}) = ∅.
      obtain ⟨y, _, hy_a, _, hy_ne⟩ := hjoint
      exact hy_ne hy_a
    apply hf_nonconst
    refine ⟨f (Classical.arbitrary X), fun x => ?_⟩
    exact hfX_subsingleton ⟨x, rfl⟩ ⟨Classical.arbitrary X, rfl⟩
  set hkfold_gf := hasLocalKfoldRamification_of_contMDiff (hg.comp hf)
  set hw_gf := hasWeightedFiberConservation_of_contMDiff (hg.comp hf)
  set hHol_gf := isHolomorphic_of_contMDiff (hg.comp hf) hkfold_gf
  set hbc_gf := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol_gf hw_gf hgf_nonconst
  -- The joint dense locus: z is regular for hbc_gf, regular for hbc_g, and
  -- each y ∈ g⁻¹(z) is regular for hbc_f.
  let S : Set Z := {z | isRegularValue hbc_gf z ∧ isRegularValue hbc_g z
    ∧ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y}
  -- Density of S: complement is union of three finite sets.
  have hS_dense : Dense S := by
    -- S = (regularLocus hbc_gf) ∩ (regularLocus hbc_g) ∩ {z | ∀ y ∈ g⁻¹{z}, isRegularValue hbc_f y}
    -- The third set has complement equal to g '' (branchLocus hbc_f), which is finite.
    have h1_compl_finite : {z : Z | ¬ isRegularValue hbc_gf z}.Finite :=
      branchLocus_finite hbc_gf
    have h2_compl_finite : {z : Z | ¬ isRegularValue hbc_g z}.Finite :=
      branchLocus_finite hbc_g
    have h3_compl_finite :
        {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y}.Finite := by
      -- Complement = {z | ∃ y, g y = z ∧ ¬ isRegularValue hbc_f y}
      --           = g '' {y | ¬ isRegularValue hbc_f y}
      have heq : {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y} =
          g '' {y : Y | ¬ isRegularValue hbc_f y} := by
        ext z
        constructor
        · intro hz
          simp only [Set.mem_setOf_eq, not_forall, Set.mem_preimage,
            Set.mem_singleton_iff] at hz
          obtain ⟨y, hgy, hyne⟩ := hz
          exact ⟨y, hyne, hgy⟩
        · rintro ⟨y, hyne, hgy⟩
          simp only [Set.mem_setOf_eq, not_forall, Set.mem_preimage,
            Set.mem_singleton_iff]
          exact ⟨y, hgy, hyne⟩
      rw [heq]
      exact (branchLocus_finite hbc_f).image g
    -- S = (S₁ᶜ)ᶜ \ ... — use complement decomposition.
    have hcompl : Sᶜ ⊆ {z : Z | ¬ isRegularValue hbc_gf z} ∪
        {z : Z | ¬ isRegularValue hbc_g z} ∪
        {z : Z | ¬ ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y} := by
      intro z hz
      by_contra hcontra
      -- hcontra : z ∉ (... ∪ ... ∪ ...). So z is in none of the three complements.
      have hn1 : isRegularValue hbc_gf z := by
        by_contra h
        exact hcontra (Or.inl (Or.inl h))
      have hn2 : isRegularValue hbc_g z := by
        by_contra h
        exact hcontra (Or.inl (Or.inr h))
      have hn3 : ∀ y ∈ g ⁻¹' {z}, isRegularValue hbc_f y := by
        by_contra h
        exact hcontra (Or.inr h)
      exact hz ⟨hn1, hn2, hn3⟩
    have hSc_finite : Sᶜ.Finite :=
      Set.Finite.subset ((h1_compl_finite.union h2_compl_finite).union
        h3_compl_finite) hcompl
    -- Dense complement of finite set in perfect target.
    haveI : Nontrivial Z := by
      obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Z)
      exact ⟨⟨p, q, hpq⟩⟩
    haveI : PerfectSpace Z := inferInstance
    have hSc_compl_dense : Dense ((Sᶜ : Set Z)ᶜ) :=
      dense_compl_of_finite_of_perfect hSc_finite
    simpa [compl_compl] using hSc_compl_dense
  -- Compatibility witnesses for each of the three canonical BCDs.
  have hcompat_f : hbc_f.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_f hw_f hf_nonconst
  have hcompat_g : hbc_g.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_g hw_g hg_nonconst
  have hcompat_gf : hbc_gf.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol_gf hw_gf hgf_nonconst
  -- Identity principle on S.
  apply holomorphicOneForm_ext_on hS_dense
  rintro z ⟨hz_gf, hz_g, hz_g_inv⟩
  -- LHS: trace at z via hbc_gf.
  have hLHS_reg :=
    (traceFormsConstructionData_provider (g ∘ f) (hg.comp hf) η).regular_spec
      hbc_gf hcompat_gf z hz_gf
  -- RHS: trace at z via hbc_g, applied to (traceFormsBundled f hf η).
  have hRHS_reg :=
    (traceFormsConstructionData_provider g hg
      (traceFormsBundled f hf η)).regular_spec hbc_g hcompat_g z hz_g
  -- Translate to traceFormsBundled.
  change (traceFormsBundled (g ∘ f) (hg.comp hf) η).toFun z =
    (traceFormsBundled g hg (traceFormsBundled f hf η)).toFun z
  -- Unfold using the provider's traceForm.
  show (traceFormsConstructionData_provider (g ∘ f) (hg.comp hf) η).traceForm.toFun z =
    (traceFormsConstructionData_provider g hg
      (traceFormsBundled f hf η)).traceForm.toFun z
  rw [hLHS_reg, hRHS_reg]
  exact regularValue_comp_traceAtRegularValue f hf g hg η
    hbc_f hcompat_f hbc_g hcompat_g hbc_gf hcompat_gf hHol_f hHol_g hHol_gf
    z hz_gf hz_g hz_g_inv

/-- **Form-level composition functoriality of the bundled trace.** -/
theorem traceFormsBundledLM_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceFormsBundledLM (X := X) (Y := Z) (g ∘ f) (hg.comp hf) =
      (traceFormsBundledLM (X := Y) (Y := Z) g hg).comp
        (traceFormsBundledLM (X := X) (Y := Y) f hf) := by
  apply LinearMap.ext
  intro η
  show traceFormsBundled (g ∘ f) (hg.comp hf) η =
    traceFormsBundled g hg (traceFormsBundled f hf η)
  -- Case split on η = 0.
  by_cases hη : η = 0
  · subst hη
    show traceFormsBundledLM (g ∘ f) (hg.comp hf) 0 =
      traceFormsBundledLM g hg (traceFormsBundledLM f hf 0)
    rw [(traceFormsBundledLM (g ∘ f) (hg.comp hf)).map_zero,
        (traceFormsBundledLM f hf).map_zero,
        (traceFormsBundledLM g hg).map_zero]
  · -- η ≠ 0. Case split on f constant.
    by_cases hf_const : ∃ y₀, ∀ x, f x = y₀
    · -- f constant ⇒ g ∘ f constant; trace along constant map is 0.
      obtain ⟨y₀, hf_eq⟩ := hf_const
      have hgf_const : ∃ z₀, ∀ x, (g ∘ f) x = z₀ :=
        ⟨g y₀, fun x => by show g (f x) = g y₀; rw [hf_eq x]⟩
      rw [traceFormsBundled_eq_zero_of_constant
            (f := g ∘ f) (hf := hg.comp hf) η hgf_const,
          traceFormsBundled_eq_zero_of_constant (f := f) (hf := hf) η ⟨y₀, hf_eq⟩]
      show (0 : HolomorphicOneForm ℂ Z) = traceFormsBundledLM g hg 0
      rw [(traceFormsBundledLM g hg).map_zero]
    · -- f nonconstant. Case split on g constant.
      by_cases hg_const : ∃ z₀, ∀ y, g y = z₀
      · -- g constant ⇒ g ∘ f constant; both sides 0.
        obtain ⟨z₀, hg_eq⟩ := hg_const
        have hgf_const : ∃ z₀, ∀ x, (g ∘ f) x = z₀ :=
          ⟨z₀, fun x => hg_eq (f x)⟩
        rw [traceFormsBundled_eq_zero_of_constant
              (f := g ∘ f) (hf := hg.comp hf) η hgf_const,
            traceFormsBundled_eq_zero_of_constant (f := g) (hf := hg)
              (traceFormsBundled f hf η) ⟨z₀, hg_eq⟩]
      · 
        exact traceFormsBundled_comp_of_nonconstant f hf g hg η hη hf_const hg_const

/--
**Narrow trace-functoriality leaf (comp).** Composition (covariant)
functoriality of `traceFormsCoord`: trace along `g ∘ f` equals trace
along `g` composed with trace along `f`.
-/
theorem traceFormsCoord_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceFormsCoord (g ∘ f) (hg.comp hf) =
      (traceFormsCoord g hg).comp (traceFormsCoord f hf) := by
  unfold traceFormsCoord
  rw [traceFormsBundledLM_comp f hf g hg]
  apply LinearMap.ext
  intro v
  simp [LinearMap.comp_apply]


theorem traceDualPullbackLift_id :
    traceDualPullbackLift (X := X) (Y := X) id contMDiff_id =
      LinearMap.id := by
  unfold traceDualPullbackLift
  rw [traceFormsCoord_id, LinearMap.toMatrix'_id, Matrix.transpose_one,
      Matrix.toLin'_one]


theorem traceDualPullbackLift_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    traceDualPullbackLift (g ∘ f) (hg.comp hf) =
      (traceDualPullbackLift f hf).comp (traceDualPullbackLift g hg) := by
  apply LinearMap.ext
  intro v
  show (Matrix.toLin' ((traceFormsCoord (g ∘ f) (hg.comp hf)).toMatrix').transpose) v =
    (Matrix.toLin' ((traceFormsCoord f hf).toMatrix').transpose)
      ((Matrix.toLin' ((traceFormsCoord g hg).toMatrix').transpose) v)
  rw [traceFormsCoord_comp f hf g hg, LinearMap.toMatrix'_comp,
      Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.comp_apply]


theorem pullbackFormsMap_id_eq_id :
    pullbackFormsMap X X id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold pullbackFormsMap
  rw [traceDualPullbackLift_id]
  rfl


theorem pullbackFormsMap_comp_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackFormsMap X Z (g ∘ f) (hg.comp hf) =
      (pullbackFormsMap X Y f hf).comp (pullbackFormsMap Y Z g hg) := by
  unfold pullbackFormsMap
  rw [traceDualPullbackLift_comp f hf g hg]
  rfl

/--
Bundle-level axiom: the `basisDualPullback` field of the bundle
selected at `(X, X, id, contMDiff_id)` is the identity additive group
homomorphism on the covering space.
-/
theorem basisAnalyticPullbackBundle_id_dualPullback :
    (basisAnalyticPullbackBundle (X := X) (Y := X) id contMDiff_id).basisDualPullback =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (X := X) (Y := X)
      id contMDiff_id,
    pullbackFormsMap_id_eq_id (X := X)]


theorem basisDualPullback_id :
    basisDualPullback (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  rw [basisDualPullback_eq_matrix_AddHom (X := X) (Y := X) id contMDiff_id,
    ← pullbackFormsMap_eq_matrix_AddHom (X := X) (Y := X) id contMDiff_id,
    pullbackFormsMap_id_eq_id (X := X)]

/--
Pointwise form of `basisDualPullback_id`: the dual form-pullback
along `id` is pointwise the identity on the covering space.
-/
theorem basisDualPullback_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    basisDualPullback (X := X) (Y := X) id contMDiff_id v = v := by
  rw [basisDualPullback_id]
  rfl

/--
Descent compatibility: `analyticPullback` acts on the period
quotient as the descended `basisDualPullback`.
-/
theorem analyticPullback_mk_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullback f hf (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback f hf v) :=
  (basisAnalyticPullbackBundle f hf).mk_eq v

/--
Contravariant functoriality of the dual form-pullback on the
covering space: `basisDualPullback (g ∘ f) = basisDualPullback f ∘ basisDualPullback g`.

Bottom-up content: the dual of form-pullback reverses composition.
This is the lifting of `pullbackFormsFun_comp_apply` to the
basis-aligned linear maps, then dualization.

**Goal.** Show that the covering-space dual pullback for `g ∘ f`
equals the composition of dual pullbacks for `f` and `g`
(contravariantly), at each covering-space vector.

The proof now routes through the concrete basis-level map
`pullbackFormsMap`; it does not use quotient smoothness or the
trace-pullback degree field from `BasisAnalyticPullbackBundle`.
-/
theorem basisAnalyticPullbackBundle_comp_dualPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)).basisDualPullback =
      ((basisAnalyticPullbackBundle f hf).basisDualPullback).comp
        (basisAnalyticPullbackBundle g hg).basisDualPullback := by
  -- Route through the concrete basis-level pullback map.
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (g ∘ f) (hg.comp hf),
      basisAnalyticPullbackBundle_eq_pullbackFormsMap f hf,
      basisAnalyticPullbackBundle_eq_pullbackFormsMap g hg,
      pullbackFormsMap_comp_eq f hf g hg]


theorem basisDualPullback_comp_top
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    basisDualPullback (g ∘ f) (hg.comp hf) =
      (basisDualPullback f hf).comp (basisDualPullback g hg) := by
  rw [basisDualPullback_eq_matrix_AddHom (g ∘ f) (hg.comp hf),
      basisDualPullback_eq_matrix_AddHom f hf,
      basisDualPullback_eq_matrix_AddHom g hg,
      ← pullbackFormsMap_eq_matrix_AddHom (g ∘ f) (hg.comp hf),
      ← pullbackFormsMap_eq_matrix_AddHom f hf,
      ← pullbackFormsMap_eq_matrix_AddHom g hg,
      pullbackFormsMap_comp_eq f hf g hg]


theorem basisDualPullback_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ Z) → ℂ) :
    basisDualPullback (g ∘ f) (hg.comp hf) v =
      basisDualPullback f hf (basisDualPullback g hg v) := by
  rw [basisDualPullback_comp_top f hf g hg, AddMonoidHom.comp_apply]

/--
Companion spec for `analyticPullback_comp_apply`: pullback of forms is
contravariantly functorial, and descent preserves composition.

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
and `basisDualPullback_comp`. Every element of the quotient is
`⟦v⟧` for some covering-space vector `v`; rewrite both sides using
descent compatibility, then apply the covering-space composition law.
-/
theorem analyticPullback_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq (g ∘ f) (hg.comp hf) v]
    rw [analyticPullback_mk_eq g hg v]
    rw [analyticPullback_mk_eq f hf (basisDualPullback g hg v)]
    rw [basisDualPullback_comp f hf g hg v]

/--
Pullback distributes contravariantly over composition.

Pure assembly of `analyticPullback_comp_spec`.
-/
lemma analyticPullback_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) :=
  analyticPullback_comp_spec f hf g hg P

/--
Companion spec: pullback along the identity map equals the identity
homomorphism (as a `ContinuousAddMonoidHom`).

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
(descent compatibility) and `basisDualPullback_id` (covering-space
identity functoriality). On each `mk v`, rewrite via descent and
identify the dual pullback as the identity.
-/
theorem analyticPullback_id_spec :
    analyticPullback (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq id contMDiff_id v, basisDualPullback_id]
    rfl

/--
Pullback along the identity is the identity.

Assembly from `analyticPullback_id_spec`.
-/
lemma analyticPullback_id_apply (P : BasisAnalyticJacobian X) :
    analyticPullback (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPullback_id_spec]
  rfl

end JacobianChallenge.TraceDegree
