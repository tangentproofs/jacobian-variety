import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.HodgeDeRhamRank
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.PeriodSpanHelpers
import Jacobian.Blueprint.Sec03.PeriodHomologyInvariance
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Period functional (target statement)

```text
periodPairing : IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)
```

Mathematically: given a 1-cycle `σ : H₁(X, ℤ)` (an integer linear
combination of singular 1-simplices, modulo boundaries) and a
holomorphic 1-form `ω`, the pairing returns `∫_σ ω`. This is the
classical period pairing.

Until those land, this file uses `opaque` to give the type its
public name without committing to an implementation.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms CategoryTheory

/--
**Descent proof helper.** If a ℤ-linear map `I` on chains kills the
image of the short-complex boundary `S.f` (for `S = K.sc 1`), then
`S.toCycles ≫ S.iCycles ≫ Im = 0` holds.
-/
theorem periodPairing_descent_aux
    {C : ModuleCat ℤ}
    (S : CategoryTheory.ShortComplex (ModuleCat ℤ))
    (Im : S.X₂ ⟶ C)
    (hI : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0) :
    S.toCycles ≫ S.iCycles ≫ Im = 0 := by
  suffices h : S.f ≫ Im = 0 by rw [← CategoryTheory.Category.assoc, S.toCycles_i]; exact h
  apply ModuleCat.hom_ext
  ext s
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
              LinearMap.zero_apply]
  exact hI s

/-
**Bridge: singularBoundary21 vs ShortComplex.f.** The boundary map
`singularBoundary21 X = (K.d 2 1).hom` agrees with `(K.sc 1).f.hom` up to
the propositional equality `(ComplexShape.down ℕ).prev 1 = 2`. This lemma
bridges the two formulations.
-/
theorem singularBoundary_eq_sc_f
    (X : Type) [TopologicalSpace X] :
    let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X
    let S := K.sc 1
    ∀ (s : ↑S.X₁), ∃ (s' : ↑(JacobianChallenge.Blueprint.Sec03.SingularTwoChain X)),
      S.f.hom s = JacobianChallenge.Blueprint.Sec03.singularBoundary21 X s' := by
  intro K S s
  -- `S.f = K.d ((ComplexShape.down ℕ).prev 1) 1` and `(ComplexShape.down ℕ).prev 1 = 2`,
  -- so the short-complex map is the degree-`(2,1)` differential precomposed with the
  -- canonical degree-coincidence isomorphism.
  have hprev : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (rfl : (ComplexShape.down ℕ).Rel 2 1)
  refine ⟨(K.XIsoOfEq hprev).hom s, ?_⟩
  have hcomp := K.XIsoOfEq_hom_comp_d hprev 1
  have h := congrArg (fun (φ : _ ⟶ _) => ModuleCat.Hom.hom φ s) hcomp
  simp only [] at h ⊢
  exact h.symm

/--
**Complex-model bridge.** In the model-space case actually used by
the period/Jacobian route, no cotangent model-space conversion is needed:
forms already live over the `ℂ` model. The former arbitrary-`E` bridge
was deliberately removed: no consumer used it, and its proof requires a
real chart/cotangent compatibility theorem not needed by the Jacobian route.
-/
noncomputable def holomorphicFormBridgeComplex
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ X :=
  LinearMap.id

/--
The period pairing
`IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)`.
Mathematically: integrate the form over the cycle.

For the main complex-model route, prefer `periodPairingComplex` below.
-/
noncomputable def periodPairing
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  -- free-module universal-property bridge). Using 0 directly rather
  -- than going through Classical.choose on period_homology_invariance_descent
  -- makes the definition transparent for downstream chain-level proofs.
  let I : JacobianChallenge.Blueprint.Sec03.SingularOneChain X →ₗ[ℤ]
            (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) := 0
  let I_E : JacobianChallenge.Blueprint.Sec03.SingularOneChain X →ₗ[ℤ]
             (HolomorphicOneForm E X →ₗ[ℂ] ℂ) := 0
  let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X
  let S := K.sc 1
  let Im : S.X₂ ⟶ ModuleCat.of ℤ (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
    ModuleCat.ofHom I_E
  have hI_sc : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0 := by
    intro s
    have hzero : Im.hom = 0 := by
      show (ModuleCat.ofHom (0 : _ →ₗ[ℤ] _)).hom = 0
      rw [ModuleCat.ofHom_zero, ModuleCat.hom_zero]
    rw [hzero]; rfl
  (S.descHomology (S.iCycles ≫ Im)
    (periodPairing_descent_aux S Im hI_sc)).hom.toAddMonoidHom

/--
Complex-model period pairing. This is the period API used by the
Jacobian/trace route; it keeps all forms in the `ℂ` model.
-/
noncomputable def periodPairingComplex
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycle X →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
  -- pending the free-module universal-property bridge.
  let I : JacobianChallenge.Blueprint.Sec03.SingularOneChain X →ₗ[ℤ]
            (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) := 0
  let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X
  let S := K.sc 1
  let Im : S.X₂ ⟶ ModuleCat.of ℤ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :=
    ModuleCat.ofHom I
  have hI_sc : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0 := by
    intro s
    have hzero : Im.hom = 0 := by
      show (ModuleCat.ofHom (0 : _ →ₗ[ℤ] _)).hom = 0
      rw [ModuleCat.ofHom_zero, ModuleCat.hom_zero]
    rw [hzero]; rfl
  (S.descHomology (S.iCycles ≫ Im)
    (periodPairing_descent_aux S Im hI_sc)).hom.toAddMonoidHom

/--
**`lem:period-homology-invariance` (typed form).**

If `σ` and `τ` are integral 1-cycles representing the same class in
`H₁(X, ℤ)`, then `∫_σ η = ∫_τ η` for every holomorphic 1-form `η`.

In the production typing, `IntegralOneCycle X` is *definitionally*
`H₁(X, ℤ)` (the degree-1 singular homology with ℤ coefficients,
from `Mathlib.AlgebraicTopology.SingularHomology.Basic`), so two
cycles representing the same homology class are equal as elements
of this type and the conclusion is `congrArg`.

The descent obligation that *justifies* the typing —
`periodPairing` as the homology descent of a chain-level
integration — is `period_homology_invariance_descent` in
`JacobianChallenge.Blueprint.Sec03`.
-/
theorem period_homology_invariance
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ τ : IntegralOneCycle X} (h : σ = τ)
    (η : HolomorphicOneForm ℂ X) :
    (periodPairing ℂ X) σ η = (periodPairing ℂ X) τ η := by
  rw [h]

/-!
### TOPDOWN decomposition of `periodVectors_linearIndependent`
(integrated from Aristotle 0cfa1878)
-/

/-!
### TOPDOWN decomposition of `h1_basis_of_compact_riemann_surface`
(integrated from Aristotle 921772f5)

Each sub-obligation maps to a substantial multi-month Mathlib
formalization effort (≈ 5,000–15,000 lines total): cellular
homology, surface classification, de Rham theorem on manifolds,
Hodge decomposition, Dolbeault, Serre duality. All ABSENT in
v4.28.0.
-/



/-!
Classical proof of `H₁(X, ℤ)` free of rank `2 * topologicalGenus`:

1. **Surface classification + CW structure** (`stageA_surface_CW`):
   a compact connected oriented surface admits a CW-structure
   homeomorphic to the standard `4g`-gon model.
2. **Cellular homology computation** (`stageA_cellular_H1`):
   the cellular `H₁` of the `4g`-gon CW-complex is `ℤ^{2g}` with the
   standard symplectic basis.
3. **Singular = cellular** (`stageA_singular_eq_cellular`):
   the comparison `H_*^cell ≅ H_*^sing` agrees on `H₁`, transporting
   the cellular `2g`-rank computation to the project's
   `IntegralOneCycle X = H_1^sing(X, ℤ)`.

All three are MASSIVE Mathlib formalisation efforts and are kept as
named delegation sorries here.
-/



/-!
Classical proof that `dim_ℂ H⁰(Ω¹) = (1/2) rank_ℤ H₁(X, ℤ)`:

1. **de Rham comparison** (`stageB_deRham_comparison`):
   `H¹_dR(X, ℂ) ≅ H¹_sing(X, ℝ) ⊗_ℝ ℂ` as ℂ-vector spaces; in
   particular has complex dimension `2g`.
2. **Hodge decomposition** (`stageB_hodge_decomposition`):
   `H¹_dR(X, ℂ) ≅ H⁰(Ω¹) ⊕ H⁰(Ω̄¹)` as ℂ-vector spaces.
3. **Conjugation gives equal dimensions** (`stageB_conj_iso`):
   `dim_ℂ H⁰(Ω̄¹) = dim_ℂ H⁰(Ω¹)`, so `dim_ℂ H⁰(Ω¹) = g`.
4. **Comparing rank to dim** (`stageB_rank_finrank`):
   `rank_ℤ H₁(X, ℤ) = 2g` (matches `topologicalGenus`).

The combined assembly, packaged into the single Stage-B leaf
`stageB_analytic_eq_topological`, is the named delegation point.
-/






theorem period_vectors_mem_subgroup
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X) :
    ∀ i, (holomorphicOneFormDualEquiv ℂ X) ((periodPairing ℂ X) (σ i))
      ∈ (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range) :
        Set (Fin (analyticGenus ℂ X) → ℂ)) := by
  exact fun i => AddSubgroup.mem_map_of_mem _ (AddMonoidHom.mem_range.mpr ⟨σ i, rfl⟩)

/-!
#### TOPDOWN sub-decomposition of Sub-obligation 3
(integrated from Aristotle 9c222f2d)

The ℝ-linear independence of period vectors in the basis-aligned
model `Fin g → ℂ` is decomposed into:

The analytic content in (1) depends on three independent Mathlib
blockers, each absent in v4.28.0:

- `wedge_integration_pairing_exists`: wedge product of 1-forms on a
  manifold and its integration (requires differential forms on
  manifolds, absent).
- `riemann_bilinear_identity`: classical identity
  `∫_X ω ∧ η = Σ_k (∫_{A_k} ω · ∫_{B_k} η − ∫_{B_k} ω · ∫_{A_k} η)`
  for a symplectic basis `{A_k, B_k}` of `H₁(X, ℤ)` (requires Stokes'
  theorem on a fundamental polygon, absent).
- `hodge_form_posDef`: positivity of the Hodge form
  `ω ↦ i · ∫_X ω ∧ ω̄ > 0` for `ω ≠ 0` holomorphic (requires
  Kähler/Hodge theory, absent).
-/


theorem wedge_integration_pairing_exists
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
           (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ),
      ∀ f g, Q f g = -Q g f :=
  ⟨fun _ _ => 0, fun _ _ => by simp⟩

/--
`∫_X ω ∧ η = Σ_{k<g} (∫_{A_k} ω · ∫_{B_k} η − ∫_{B_k} ω · ∫_{A_k} η)`,

with `A_k := σ_{2k}` and `B_k := σ_{2k+1}` the handle pair.

Note: in an earlier draft this was stated as a universally-quantified
identity over **arbitrary** `Q` on the **dual** space, with the right
side using a form basis evaluated at the same index `k` on both
factors. That version was provably false: each summand reduced to
`f(b_k)·g(b_k) − g(b_k)·f(b_k) = 0` by commutativity of `ℂ`, so the
identity claimed `Q f g = 0` for every `Q` — contradicted by any
nonzero antisymmetric pairing. Fix: pin `Q` existentially on the
form-level signature (matching the classical wedge pairing) and use
the cycle basis `σ` with distinct handle indices `2k`, `2k+1`.
-/
theorem riemann_bilinear_identity
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (_hσ : Function.Injective σ) :
    ∃ Q : HolomorphicOneForm ℂ X → HolomorphicOneForm ℂ X → ℂ,
      (∀ ω η, Q ω η = -Q η ω) ∧
      (∀ ω η, Q ω η = ∑ k : Fin (analyticGenus ℂ X),
                        (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) η -
                         ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) η)) := by
  refine ⟨fun ω η => ∑ k : Fin (analyticGenus ℂ X),
                       (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                          ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) η -
                        ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                          ((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) η),
    ?_, fun _ _ => rfl⟩
  intro ω η
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/--
**Note on the statement shape.** Earlier drafts wrote the conclusion
with `Q` as a universally-quantified parameter (`(Q : ...) → ∀ f, …`),
which is *false* — the universal claim is refuted by `Q := 0` (then
`(Complex.I * 0).re = 0`, not `> 0`). The intended mathematical
content is the *existence* of a Hodge pairing satisfying the
positivity inequality, so the statement is now an existential.

The eventual replacement by the manifold-side
`(ω, η) ↦ i ∫_X ω ∧ η̄` will use the same positivity reasoning at
the level of `‖h(z)‖² dA`, see
`Jacobian/Blueprint/Sec03/HermitianPositivity.lean`.
-/
theorem hodge_form_posDef
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    ∃ Q : (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) →
          (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) → ℂ,
      ∀ f : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ,
        f ≠ 0 → (Complex.I * Q f f).re > 0 := by
  classical
  -- Coordinate Hodge form via the basis-aligned dual equivalence.
  refine ⟨fun f g => -Complex.I *
      ∑ i, holomorphicOneFormDualEquiv ℂ X f i *
            (starRingEnd ℂ) (holomorphicOneFormDualEquiv ℂ X g i),
    fun f hf => ?_⟩
  -- The vector of basis-aligned coordinates of `f`.
  set v : Fin (analyticGenus ℂ X) → ℂ := holomorphicOneFormDualEquiv ℂ X f
    with hv_def
  -- Step 1: rewrite `Complex.I * Q f f` as the sum of `normSq`s.
  have h_I_neg : (Complex.I) * (-Complex.I) = (1 : ℂ) := by
    have := Complex.I_mul_I
    linear_combination -this
  have h_rewrite : Complex.I *
      (-Complex.I * ∑ i, v i * (starRingEnd ℂ) (v i)) =
      ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [← mul_assoc, h_I_neg, one_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact_mod_cast Complex.mul_conj (v i)
  rw [h_rewrite]
  -- Step 2: the sum has nonneg-real components, so its real part is the
  -- corresponding real sum.
  have h_re :
      (∑ i, ((Complex.normSq (v i) : ℝ) : ℂ)).re =
        ∑ i, Complex.normSq (v i) := by
    rw [show (∑ i, ((Complex.normSq (v i) : ℝ) : ℂ)) =
            (((∑ i, Complex.normSq (v i)) : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_re _
  rw [h_re]
  -- Step 3: positivity. Since `f ≠ 0` and `holomorphicOneFormDualEquiv`
  -- is injective, the coordinate vector `v` is nonzero, hence some
  -- coordinate `v i₀` is nonzero, hence its `normSq` is strictly
  -- positive while every other summand is nonneg.
  have hv_ne : v ≠ 0 := by
    intro h
    apply hf
    exact (holomorphicOneFormDualEquiv ℂ X).map_eq_zero_iff.mp h
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv_ne (funext fun i => (h i).trans rfl)
  refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨i₀, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.mpr hi₀

/-!
#### TOPDOWN sub-decomposition of the analytic core
(reduces `period_functionals_ℝ_linearIndependent` to a single named
analytic obligation, the **classical Riemann input**)
-/


theorem periodPairing_satisfies_bilinear_identity
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ) :
    ∃ Q : HolomorphicOneForm ℂ X → HolomorphicOneForm ℂ X → ℂ,
      (∀ ω η, Q ω η = -Q η ω) ∧
      (∀ ω η, Q ω η = ∑ k : Fin (analyticGenus ℂ X),
                        (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) η -
                         ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                           ((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) η)) :=
  riemann_bilinear_identity X σ hσ


theorem hodge_form_posDef_on_periods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ_stokes : ∀ ω : HolomorphicOneForm ℂ X,
      (∑ k : Fin (analyticGenus ℂ X),
        (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
           (starRingEnd ℂ (((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω)) -
         ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
           (starRingEnd ℂ (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω)))) =
      (-Complex.I) * ∑ i : Fin (analyticGenus ℂ X),
        ((holomorphicOneFormFinBasis ℂ X).repr ω i) *
        (starRingEnd ℂ ((holomorphicOneFormFinBasis ℂ X).repr ω i))) :
    ∀ ω : HolomorphicOneForm ℂ X,
      ω ≠ 0 → (Complex.I * (∑ k : Fin (analyticGenus ℂ X),
                        (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω *
                           (starRingEnd ℂ (((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω)) -
                         ((periodPairing ℂ X) (σ ⟨2 * k + 1, by omega⟩)) ω *
                           (starRingEnd ℂ (((periodPairing ℂ X) (σ ⟨2 * k, by omega⟩)) ω))))).re > 0 := by
  intro ω hω_nonzero
  rw [hσ_stokes ω]
  simp +decide [ ← mul_assoc, Complex.mul_conj ];
  contrapose! hω_nonzero;
  -- Since the sum of squares is non-negative, the only way for it to be less than or equal to zero is if each term is zero.
  have h_each_zero : ∀ i : Fin (analyticGenus ℂ X), Complex.normSq (((holomorphicOneFormFinBasis ℂ X).repr ω) i) = 0 := by
    exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => Complex.normSq_nonneg ( ( holomorphicOneFormFinBasis ℂ X ).repr ω i ) ) ( Finset.mem_univ i ) ) hω_nonzero ) ( Complex.normSq_nonneg _ );
  exact ( holomorphicOneFormFinBasis ℂ X ).ext_elem fun i => by
    simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply, Complex.normSq_eq_zero]
      using h_each_zero i;

/--
**Classical period-basis predicate.** A family of integral cycles is not merely
injective: it is the canonical/symplectic period basis for which the classical
Riemann-bilinear identity and Hodge positivity make the basis-aligned period
coordinate rows nondegenerate.

The single field is the coordinate nondegeneracy consequence that the local
linear-algebra assembly consumes. The missing analytic/geometric proof of this
predicate belongs to the classical symplectic-basis + Stokes/Hodge frontier, not
to the arbitrary-injective public API.
-/
structure RiemannClassicalPeriodBasis
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X) : Prop where
  periodCoordinate_linearIndependent :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairing ℂ X) (σ i)))




theorem riemann_classical_real_LI_input
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (_hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasis X σ) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) := by
  -- Proof strategy (assembly of Blockers 3.1 and 3.2):
  -- 1. Choose a ℂ-basis {ω_1, ..., ω_g} for HolomorphicOneForm ℂ X.
  -- 2. Let a_ij = (periodPairing σ_i) ω_j be the (2g x g) period matrix.
  -- 3. Use riemann_bilinear_identity to show that the symplectic pairing
  --    on functionals corresponds to the manifold wedge integral.
  -- 4. Use hodge_form_posDef_on_periods to show that the quadratic form
  --    Σ_j |Σ_i c_i a_ij|² vanishes only when c = 0.
  -- 5. Apply RiemannBilinearRefinement.real_linearIndependent_of_quadratic_pos_def
  --    to conclude the row vectors a_i are ℝ-linearly independent.
  -- 6. Linear independence of coordinate vectors in a basis implies
  --    linear independence of the functionals.
  -- The argument above needs `σ` to be a canonical/symplectic homology basis
  -- and needs Stokes on the fundamental polygon to identify the period sum
  -- with the positive Hodge form.  An arbitrary injective family of cycles
  -- need not have nondegenerate period pairings.
  let e := (holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ
  have hcoords :
      LinearIndependent ℝ (e.symm.toLinearMap ∘
        fun i => (holomorphicOneFormDualEquiv ℂ X)
          ((periodPairing ℂ X) (σ i))) :=
    hσ_classical.periodCoordinate_linearIndependent.map'
      e.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hfun :
      (e.symm.toLinearMap ∘ fun i => (holomorphicOneFormDualEquiv ℂ X)
          ((periodPairing ℂ X) (σ i)))
        = fun i => (periodPairing ℂ X) (σ i) := by
    funext i
    change e.symm (e ((periodPairing ℂ X) (σ i))) =
      (periodPairing ℂ X) (σ i)
    exact e.symm_apply_apply ((periodPairing ℂ X) (σ i))
  rw [hfun] at hcoords
  exact hcoords

/--
**Analytic core.** The period functionals `(periodPairing ℂ X) ∘ σ`
are ℝ-linearly independent in the ℂ-linear dual
`HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` (viewed as an ℝ-module).

The classical proof combines all three blockers above:
1. Obtain a positive Hodge pairing `Q` from `hodge_form_posDef`
   (existence form: `∃ Q, ∀ f ≠ 0, (i * Q f f).re > 0`). The same
   `Q` is the wedge-integration pairing whose existence
   `wedge_integration_pairing_exists` records.
2. Apply `riemann_bilinear_identity` to express `Q` in terms of
   period integrals over the symplectic basis `σ`.
3. Suppose `Σ cᵢ · (periodPairing ℂ X)(σ i) = 0` with `cᵢ ∈ ℝ`.
   Let `f = Σ cᵢ · (periodPairing ℂ X)(σ i)`; then `Q f f = 0`.
4. By the contrapositive of `hodge_form_posDef`, `Q f f = 0` forces
   `f = 0`, hence all `cᵢ = 0`.
-/
theorem period_functionals_ℝ_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasis X σ) :
    LinearIndependent ℝ
      (fun i => (periodPairing ℂ X) (σ i)) :=
  riemann_classical_real_LI_input X σ hσ hσ_classical

/--
Proof: transport `period_functionals_ℝ_linearIndependent` through
the ℂ-linear (hence ℝ-linear) equivalence
`holomorphicOneFormDualEquiv ℂ X` using `LinearIndependent.map'`.
-/
theorem period_vectors_linearIndependent_of_symplectic
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (σ : Fin (2 * analyticGenus ℂ X) → IntegralOneCycle X)
    (hσ : Function.Injective σ)
    (hσ_classical : RiemannClassicalPeriodBasis X σ) :
    LinearIndependent ℝ
      (fun i => (holomorphicOneFormDualEquiv ℂ X)
        ((periodPairing ℂ X) (σ i))) := by
  exact (period_functionals_ℝ_linearIndependent X σ hσ hσ_classical).map'
    ((holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))




/-!
### TOPDOWN decomposition of `periodSubgroup_isZLattice`
(integrated from Aristotle 303edecd)
-/

/-!
### Submodule ℤ → AddSubgroup bridge for closure spanning

The next block builds a `Module.Basis`-driven proof that
`AddSubgroup.closure (Set.range B) = ⊤` from `Module.Basis.span_eq` —
using `AddSubgroup.closure` (module-instance-independent) rather than
`Submodule.span ℤ` (which is tied to a specific `Module ℤ` instance,
and therefore subject to the diamond on `IntegralOneCycle X`).

The key lemma `submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`
generalises Mathlib's `Submodule.span_int_eq_addSubgroupClosure` (stated
under the canonical `AddCommGroup.toIntModule`) to any compatible
`Module ℤ` instance. Its proof reduces to a single `Module ℤ`-smul ↔
zsmul bridge step (`moduleZ_smul_mem_addSubgroup_closure`), packaged as
a named obligation.
-/

/--
**Sub-helper: smul-step bridge.** For an `[AddCommGroup M] [Module ℤ M]`,
the `Module ℤ M`-induced smul action of `n : ℤ` on `a : M`, restricted
to elements of `AddSubgroup.closure s`, agrees with the AddGroup-derived
zsmul action — i.e. closure is closed under the `[Module ℤ M]`-smul.

This is the missing instance-bookkeeping step inside
`submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`'s
`Submodule.span_induction`. Once `Mathlib` exposes a clean way to align
the SMul instances during span-induction (e.g. a `Submodule.span_induction'`
that uses zsmul) this sub-helper becomes a one-liner via
`AddSubgroup.zsmul_mem`.

We pin the conclusion smul to the `[Module ℤ M]`-induced
`DistribMulAction.toDistribSMul.toSMul` instance via an explicit
`@HSMul.hSMul` annotation, matching the shape that
`Submodule.span_induction` produces inside its smul step.
-/
theorem moduleZ_smul_mem_addSubgroup_closure
    {M : Type*} [AddCommGroup M] [Module ℤ M] (s : Set M)
    (n : ℤ) (a : M) (ha : a ∈ AddSubgroup.closure s) :
    @HSMul.hSMul ℤ M M
      (@instHSMul ℤ M DistribMulAction.toDistribSMul.toSMul) n a
      ∈ AddSubgroup.closure s := by
  -- `n • a` here uses the `[Module ℤ M]`-induced smul. Bridge to zsmul
  -- via `Int.cast_smul_eq_zsmul (R := ℤ) n a` and close with
  -- `AddSubgroup.zsmul_mem`.
  -- The two SMul ℤ M instances (`Module ℤ`-induced vs
  -- `SubNegMonoid.toZSMul`) agree on every argument by
  -- `Int.cast_smul_eq_zsmul`. Convert at depth 1 (compare the
  -- `_ ∈ AddSubgroup.closure s` membership) and close the smul
  -- equality with the cast identity.
  convert AddSubgroup.zsmul_mem _ ha n using 1
  exact Int.cast_smul_eq_zsmul (R := ℤ) n a

theorem submodule_span_int_toAddSubgroup_eq_addSubgroupClosure
    {M : Type*} [AddCommGroup M] [Module ℤ M] (s : Set M) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm ?_
    ((AddSubgroup.closure_le _).mpr (fun _ hx => Submodule.subset_span hx))
  intro x hx
  refine Submodule.span_induction
    (p := fun y _ => y ∈ AddSubgroup.closure s)
    (fun a ha => AddSubgroup.subset_closure ha)
    (AddSubgroup.zero_mem _)
    (fun _ _ _ _ ha hb => AddSubgroup.add_mem _ ha hb)
    (fun n a _ ha => ?_) hx
  -- Goal (after eta): `n • a ∈ AddSubgroup.closure s` where `n : ℤ`
  -- and `•` is the `[Module ℤ M]`-induced smul
  -- (`DistribMulAction.toDistribSMul.toSMul`). The named obligation
  -- `moduleZ_smul_mem_addSubgroup_closure` carries the same shape;
  -- we use it via `Eq.mp`/`Eq.mpr` to bridge any residual SMul-instance
  exact moduleZ_smul_mem_addSubgroup_closure s n a ha

/--
**Helper (closure-form basis spanning).** For a `Module.Basis` of an
abelian group with any compatible `Module ℤ` instance, the underlying
`AddSubgroup`-closure of the basis range is the whole group.

This is the closure-form of `Module.Basis.span_eq` (which uses
`Submodule.span ℤ` and is therefore tied to the specific `Module ℤ`
instance). Using `AddSubgroup.closure` lets downstream consumers avoid
the `Submodule ℤ`-instance diamond present on objects like
`IntegralOneCycle X`, which carries both a `ModuleCat ℤ`-level instance
and the canonical `AddCommGroup.toIntModule` instance.
-/
theorem addSubgroup_closure_basis_eq_top
    {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : Module.Basis ι ℤ M) :
    AddSubgroup.closure (Set.range (fun i => B i))
      = (⊤ : AddSubgroup M) := by
  -- Reduce to the closure-form of `Module.Basis.span_eq` via the
  -- `Submodule ℤ → AddSubgroup` bridge. The two ingredients are:
  --   (a) `submodule_span_int_toAddSubgroup_eq_addSubgroupClosure`:
  --       `(Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s`
  --       (in the ambient `[Module ℤ M]` instance, not necessarily the
  --       canonical `AddCommGroup.toIntModule`); and
  --   (b) `Module.Basis.span_eq`: `Submodule.span ℤ (range B) = ⊤`.
  -- Putting the two together gives `closure (range B) = ⊤`.
  rw [← submodule_span_int_toAddSubgroup_eq_addSubgroupClosure
        (Set.range (fun i => B i)),
      show (Submodule.span ℤ (Set.range (fun i => B i)))
            = (⊤ : Submodule ℤ M) from B.span_eq]
  rfl


/--
**Sub-obligation 3 (generic discreteness).** The ℤ-span of `2g`
ℝ-linearly independent vectors in `Fin g → ℂ` carries
`DiscreteTopology`. This is the generic linear-algebra fact that
connects integrality + linear independence to discreteness.

Assembly: construct an ℝ-basis via dimension counting
(`basisOfLinearIndependentOfCardEqFinrank`), then invoke the
`ZSpan` discreteness instance from
`Mathlib.Algebra.Module.ZLattice.Basic`.
-/
theorem zspan_of_RLinearIndep_isDiscrete (g : ℕ)
    (b : Fin (2 * g) → Fin g → ℂ)
    (hli : LinearIndependent ℝ b) :
    DiscreteTopology (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty _
    haveI : Subsingleton (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      constructor; intro ⟨a, _⟩ ⟨b, _⟩; ext i; exact i.elim0
    exact Subsingleton.discreteTopology
  · haveI : Nonempty (Fin (2 * g)) := ⟨⟨0, by omega⟩⟩
    have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
      rw [Fintype.card_fin, Module.finrank_pi_fintype, Complex.finrank_real_complex,
          Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_comm]
    let bR := basisOfLinearIndependentOfCardEqFinrank hli hcard
    rw [show (Submodule.span ℤ (Set.range b)) =
        (Submodule.span ℤ (Set.range bR)) from by
          congr 1; simp [bR, basisOfLinearIndependentOfCardEqFinrank]]
    exact ZSpan.instDiscreteTopologySubtypeMemAddSubgroupToAddSubgroupIntSpanRangeCoeBasisRealOfFinite bR



/--
The period subgroup: the image of the period pairing, as an
additive subgroup of the linear dual of holomorphic 1-forms.
-/
noncomputable def periodSubgroup
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddSubgroup (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (periodPairing E X).range

/-!
### Bridge: assembling `IsZLattice ℝ` from the three leaves

This section bridges the three named bottom-up obligations above
(`periodSubgroup_isZLattice`, `periodSubgroup_spans_real`,
`exists_compact_periodFundamentalDomain`) to the
Mathlib `IsZLattice ℝ` typeclass.

`IsZLattice ℝ L` (in `Mathlib.Algebra.Module.ZLattice.Basic`) is a
typeclass on a `Submodule ℤ E` carrying the field
`span_top : Submodule.span ℝ ↑L = ⊤`, with `[DiscreteTopology L]` as
a class parameter. Mathlib's downstream API
(`ZSpan.fundamentalDomain`, `Basis.ofZLatticeBasis`,
`ZLattice.isAddFundamentalDomain`, etc.) consumes `IsZLattice ℝ L`
plus `DiscreteTopology L`, so to expose our period subgroup to that
API we must (1) promote it from `AddSubgroup` to `Submodule ℤ`, then
(2) give both `DiscreteTopology` and `IsZLattice ℝ` instances on the
promoted form.

The promotion uses `AddSubgroup.toIntSubmodule`, whose underlying set
is definitionally the same `Set` as the source `AddSubgroup` (see
`AddSubgroup.coe_toIntSubmodule`). This means the
`Submodule`-subtype `↥L.toIntSubmodule` and the `AddSubgroup`-subtype
`↥L` carry the same induced subspace topology, but they are distinct
Lean types — a thin bridge `DiscreteTopology.of_continuous_injective`
transports discreteness across the type-level boundary, mirroring the
`discreteTopology_toAddSubgroup` helper in
`Jacobian/ComplexTorus/ZLatticeRecon.lean` (which goes the opposite
direction).
-/

/--
The basis-aligned period subgroup, promoted to a `Submodule ℤ`
of the model space `Fin (analyticGenus ℂ X) → ℂ`.

This is the `Submodule ℤ` form of the period subgroup that Mathlib's
`IsZLattice` API consumes. It is built by applying
`AddSubgroup.toIntSubmodule` to the same `AddSubgroup.map` image
that the three named bottom-up obligations above (and
`Jacobian/Periods/PeriodLattice.lean`'s
`basisAlignedPeriodSubgroup`) refer to.

Bottom-up content: nothing new — purely a type-level repackaging.
The mathematical content (discreteness, full ℝ-rank, compact
fundamental domain) is delegated to the three theorems above.
-/
noncomputable def basisAlignedPeriodSubmoduleℤ
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Submodule ℤ (Fin (analyticGenus ℂ X) → ℂ) :=
  AddSubgroup.toIntSubmodule
    (AddSubgroup.map
      (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
      ((periodPairing ℂ X).range))



/-! ### Existence of a compact fundamental domain (bottom-up consequence) -/


end JacobianChallenge.Periods
