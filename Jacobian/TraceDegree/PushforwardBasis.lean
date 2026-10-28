import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.Periods.PullbackNaturality
import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Jacobian.TraceDegree.PiecewiseC1Def
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Analytic pushforward on the basis-aligned carrier

A holomorphic map `f : X → Y` of compact Riemann surfaces induces a
pushforward `f_* : BasisAnalyticJacobian X → BasisAnalyticJacobian Y`,
typically constructed via the trace map on holomorphic 1-forms (or, in
basis coordinates, the dual of the trace), descended through the
period quotient.

This module mirrors `Jacobian/TraceDegree/PullbackBasis.lean` in the
opposite direction. Named obligations:

* `analyticPushforward f hf` — bundled `→ₜ+` hom on the basis-aligned
  carrier (`opaque`);
* `analyticPushforward_id_apply` — covariant identity functoriality;
* `analyticPushforward_comp_apply` — covariant composition;
* `analyticPushforward_contMDiff` — holomorphicity.

## TOPDOWN refactor: trace-coordinate interface

Earlier rounds bundled `analyticPushforward`, `pushforwardTraceLift`,
their descent compatibility, and their geometric properties together
in `BasisAnalyticPushforwardBundle`, then exposed each via
`Classical.choice` from a zero-valued `Inhabited` witness. This made
the identity functoriality `pushforwardTraceLift id = id` *unprovable*
at the bundle layer (the zero witness can't satisfy it), and attempts
to enrich the bundle with an `HEq`-based identity-case field hit an
instance diamond after `subst Y = X` (see prior commit
`410ce72`/`PullbackBasis HEq leak`).

This refactor breaks the bundle apart:

1. A small, contravariant **trace-coordinate interface**
   `holomorphicTraceCoord f hf : (Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`,
   opaque, with two named functoriality sorries
   (`holomorphicTraceCoord_id`, `holomorphicTraceCoord_comp`).
   These are the *Mathlib-level* trace/norm-on-holomorphic-1-forms
   obligations a future
   `Mathlib.Analysis.Complex.RiemannSurface.Trace` would discharge.

3. **Three "raw" geometric sorries** carrying the genuinely geometric
   content the bundle used to bundle:

* `pushforwardTraceLift_preserves_lattice_raw` — the trace lift
     sends the period subgroup of `X` into the period subgroup of `Y`
     (Riemann bilinear / period-lattice content);
   * `analyticPushforward_mk_spec_raw` — descent compatibility:
     `analyticPushforward (mk v) = mk (pushforwardTraceLift v)`
     (descent of the trace map through the period quotient);
   * `analyticPushforward_contMDiff_raw` — the descended map is
     holomorphic (Mathlib quotient-smoothness content).
-/

namespace JacobianChallenge.TraceDegree

set_option linter.unusedSectionVars false

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi
open JacobianChallenge.ComplexTorus

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

/-!
### Trace-coordinate interface

The fundamental small interface this module exposes. A holomorphic
map `f : X → Y` of compact Riemann surfaces should induce a
`ℂ`-linear *pullback on holomorphic 1-forms*
`f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`. After choosing bases of
`HolomorphicOneForm ℂ Y` and `HolomorphicOneForm ℂ X` (of dimensions
`analyticGenus ℂ Y` and `analyticGenus ℂ X` respectively), this is a
linear map of basis-coordinate vector spaces. We expose it as the
opaque `holomorphicTraceCoord` interface together with two named
functoriality sorries that match the Mathlib-style functoriality of
the form-pullback.
-/

/--
The basis-coordinate representation of the holomorphic-1-form
*pullback* induced by `f : X → Y`, as a ℂ-linear map
`(Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`.

This is the **contravariant** direction (forms pull back along `f`),
which is why the codomain is `Fin g_X → ℂ` and the domain is
`Fin g_Y → ℂ`. The covariant pushforward
`pushforwardTraceLift f hf : (Fin g_X → ℂ) →+ (Fin g_Y → ℂ)`
is defined below as the matrix transpose of this map.

Bottom-up: built concretely from `pullbackFormsBundledLM` (the smooth
bundle of the chain-rule pullback), composed with the basis-aligned
linear equivalences `holomorphicOneFormFinBasis.equivFun` to convert
between abstract forms and `Fin g → ℂ` coordinates.
-/
noncomputable def holomorphicTraceCoord
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  (holomorphicOneFormFinBasis ℂ X).equivFun.toLinearMap ∘ₗ
    (pullbackFormsBundledLM X Y f hf) ∘ₗ
    (holomorphicOneFormFinBasis ℂ Y).equivFun.symm.toLinearMap

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Identity functoriality of the trace-coordinate map. -/
theorem holomorphicTraceCoord_id :
    holomorphicTraceCoord (X := X) (Y := X) id contMDiff_id =
      LinearMap.id := by
  unfold holomorphicTraceCoord
  rw [pullbackFormsBundledLM_id, LinearMap.id_comp]
  exact LinearMap.ext fun x => (holomorphicOneFormFinBasis ℂ X).equivFun.apply_symm_apply x

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] in
/-- Composition functoriality of the trace-coordinate map. -/
theorem holomorphicTraceCoord_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    holomorphicTraceCoord (g ∘ f) (hg.comp hf) =
      (holomorphicTraceCoord f hf).comp (holomorphicTraceCoord g hg) := by
  unfold holomorphicTraceCoord
  rw [pullbackFormsBundledLM_comp f hf g hg]
  -- The middle `Y.equivFun.symm ∘ₗ Y.equivFun` cancels at point level.
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-!
### Top-level `pushforwardTraceLift` via matrix transpose

The *covariant* pushforward direction is the transpose (a.k.a. dual,
under self-duality of `Fin n → ℂ`) of `holomorphicTraceCoord`.
Concretely, we go through the standard `LinearMap.toMatrix'` /
`Matrix.transpose` / `Matrix.toLin'` pipeline.
-/


noncomputable def pushforwardTraceLift
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →+ (Fin (analyticGenus ℂ Y) → ℂ) :=
  (Matrix.toLin' (holomorphicTraceCoord f hf).toMatrix'.transpose).toAddMonoidHom

/-- `pushforwardTraceLift` along the identity is the identity. -/
theorem pushforwardTraceLift_id :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold pushforwardTraceLift
  rw [holomorphicTraceCoord_id, LinearMap.toMatrix'_id, Matrix.transpose_one,
      Matrix.toLin'_one]
  rfl

/-- `pushforwardTraceLift` distributes over composition (covariantly). -/
theorem pushforwardTraceLift_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) := by
  refine AddMonoidHom.ext fun v => ?_
  show (Matrix.toLin'
      (LinearMap.toMatrix' (holomorphicTraceCoord (g ∘ f) (hg.comp hf))).transpose) v =
    (Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord g hg)).transpose)
      ((Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord f hf)).transpose) v)
  rw [holomorphicTraceCoord_comp f hf g hg, LinearMap.toMatrix'_comp,
      Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.comp_apply]

/-! ### Top-level `analyticPushforward` and the three raw geometric sorries -/

/--
Bridge identity between `pushforwardTraceLift` and the form-pullback /
basis-aligned dual equivalence.

The algebraic relationship: `pushforwardTraceLift = transpose-of-matrix(holomorphicTraceCoord)`,
and `holomorphicTraceCoord = basisX.equivFun ∘ pullbackFormsBundledLM ∘ basisY.equivFun.symm`.
So `pushforwardTraceLift v j = ∑ i, (holomorphicTraceCoord matrix)[i,j] * v i
= ∑ i, (basisX.equivFun (pullbackFormsBundledLM (basisY j))) i * v i`.
When `v = dualEquiv X φ`, `v i = φ (basisX i)`, and the sum collapses via
linearity of `φ` to `φ (pullbackFormsBundledLM (basisY j))`, which equals
`(φ ∘ pullbackFormsBundledLM)(basisY j) = (dualEquiv Y (φ ∘ pullbackFormsBundledLM)) j`.
-/
theorem pushforwardTraceLift_apply_holomorphicOneFormDualEquiv
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :
    pushforwardTraceLift f hf (holomorphicOneFormDualEquiv ℂ X φ) =
      holomorphicOneFormDualEquiv ℂ Y
        (φ.comp (pullbackFormsBundledLM X Y f hf)) := by
  classical
  ext j
  -- RHS: dualEquiv Y (φ.comp pullbackBundled) j = (φ.comp pullbackBundled) (basisY j)
  --                                              = φ (pullbackBundled (basisY j))
  -- via the new auxiliary `holomorphicOneFormDualEquiv_apply_eq_apply_basis`.
  rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  show (Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord f hf)).transpose
      (holomorphicOneFormDualEquiv ℂ X φ)) j =
    (φ.comp (pullbackFormsBundledLM X Y f hf)) (holomorphicOneFormFinBasis ℂ Y j)
  -- LHS: matrix-vector product via toLin'.
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    LinearMap.toMatrix'_apply]
  -- LHS: ∑ i, holomorphicTraceCoord f hf (Pi.single j 1) i * (dualEquiv X φ) i.
  -- (dualEquiv X φ) i = φ (basisX i) by the auxiliary.
  simp_rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  -- LHS: ∑ i, holomorphicTraceCoord f hf (Pi.single j 1) i * φ (basisX i).
  -- Unfold holomorphicTraceCoord: it's basisX.equivFun ∘ pullbackBundled ∘ basisY.equivFun.symm.
  unfold holomorphicTraceCoord
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  -- LHS: ∑ i, (basisX.equivFun (pullbackBundled (basisY.equivFun.symm (Pi.single j 1)))) i * φ (basisX i).
  -- Reduce basisY.equivFun.symm (Pi.single j 1) = basisY j.
  rw [show (holomorphicOneFormFinBasis ℂ Y).equivFun.symm (Pi.single j 1) =
      holomorphicOneFormFinBasis ℂ Y j from by
    rw [Module.Basis.equivFun_symm_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_smul]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, zero_smul]
    · intro hj; exact (hj (Finset.mem_univ _)).elim]
  -- LHS: ∑ i, (basisX.equivFun (pullbackBundled (basisY j))) i * φ (basisX i).
  -- Use ω = ∑ i, ((basisX.equivFun ω) i) • (basisX i) and linearity of φ.
  set ωX : HolomorphicOneForm ℂ X :=
    (pullbackFormsBundledLM X Y f hf) (holomorphicOneFormFinBasis ℂ Y j)
  show ∑ i, (holomorphicOneFormFinBasis ℂ X).equivFun ωX i *
      φ (holomorphicOneFormFinBasis ℂ X i) = φ ωX
  -- ωX = ∑ i, ((basisX.equivFun ωX) i) • basisX i.
  conv_rhs => rw [← (holomorphicOneFormFinBasis ℂ X).sum_equivFun ωX]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, smul_eq_mul]

/--
**BUG FIX** (formerly ID 121). The original statement
`∀ γ, ∃ K, ChartLiftLipschitzOnPartitions γ K` was *false* for
arbitrary continuous paths: a nowhere-differentiable path, e.g.
a space-filling curve restricted to `[0,1]`, cannot satisfy a
uniform Lipschitz bound on its chart lifts.

Fix: add the hypothesis `ChartLiftPiecewiseC1 γ' K₀` — the path is
piecewise C¹ with a uniform derivative bound `K₀`. Then the
Lipschitz conclusion follows from the mean-value inequality
(`Convex.lipschitzOnWith_of_nnnorm_derivWithin_le`) applied to each
chart-lifted segment on the compact convex set `[0, 1]`.
-/
theorem cycleLipPath_obligation :
    ∀ {a b : X} (γ' : Path a b) (K₀ : NNReal)
      (_ : ChartLiftPiecewiseC1 γ' K₀),
      ∃ K : NNReal, ChartLiftLipschitzOnPartitions γ' K := by
  intro a b γ' K₀ hγ
  exact ⟨K₀, fun n hn pickX i h => by
    obtain ⟨hDiff, hBound⟩ := hγ n hn pickX i h
    exact (convex_Icc 0 1).lipschitzOnWith_of_nnnorm_derivWithin_le
      (hDiff.differentiableOn (by norm_num)) hBound⟩

/--
Raw geometric obligation (chain-level uniform Lipschitz).

The chain-level uniformised version of `cycleLipPath_obligation`:
for any finite family of paths `γs i : Path (a i) (b i)` in `X`,
each satisfying a piecewise-C¹ condition with its own bound `K_i`,
there is a *single* Lipschitz constant `K` that bounds the chart-lift
of every `γs i` on every uniform-grain partition simultaneously.
-/
theorem cycleLipChain_obligation :
    ∀ (m : ℕ) (a b : Fin m → X)
      (γs : ∀ i : Fin m, Path (a i) (b i))
      (_ : ∀ i : Fin m, ∃ K₀ : NNReal, ChartLiftPiecewiseC1 (γs i) K₀),
      ∃ K : NNReal, ∀ i : Fin m, ChartLiftLipschitzOnPartitions (γs i) K := by
  intro m a b γs hC1
  -- For each i, obtain a Lipschitz constant K_i from the path-level obligation.
  choose K₀s hK₀s using hC1
  choose Ks hKs using fun i => cycleLipPath_obligation (γs i) (K₀s i) (hK₀s i)
  -- Take K = sup of all K_i (works even when m = 0, giving K = 0).
  refine ⟨Finset.sup Finset.univ Ks, fun i => ?_⟩
  -- ChartLiftLipschitzOnPartitions is monotone in K via LipschitzOnWith monotonicity.
  intro n hn pickX j h
  have hKi := hKs i n hn pickX j h
  intro x hx y hy
  exact le_trans (hKi hx hy) (by gcongr; exact Finset.le_sup (Finset.mem_univ i))



noncomputable def pushforwardTraceLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  Matrix.toLin' (holomorphicTraceCoord f hf).toMatrix'.transpose


noncomputable def pushforwardTraceLiftCLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  LinearMap.toContinuousLinearMap (pushforwardTraceLiftLinearMap f hf)














/-!
These two were the bundle-level identity/composition obligations
under the previous design. They are now trivial aliases for
`pushforwardTraceLift_id` / `pushforwardTraceLift_comp`. Kept under
their old names so the docstrings in `PullbackBasis.lean` that name
them remain accurate.
-/


theorem basisAnalyticPushforwardBundle_id_traceLift :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) :=
  pushforwardTraceLift_id


theorem basisAnalyticPushforwardBundle_comp_traceLift
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) :=
  pushforwardTraceLift_comp f hf g hg

/-!
These names are preserved verbatim. Each is a small assembly of
`pushforwardTraceLift_id` / `pushforwardTraceLift_comp` plus
`AddMonoidHom`-API.
-/

theorem pushforwardTraceLift_id_apply_at
    (i : Fin (analyticGenus ℂ X)) (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v i = v i := by
  rw [pushforwardTraceLift_id]
  rfl

theorem pushforwardTraceLift_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v = v := by
  rw [pushforwardTraceLift_id]
  rfl

theorem pushforwardTraceLift_comp_spec_apply_at
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) (i : Fin (analyticGenus ℂ Z)) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v i =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) i := by
  rw [pushforwardTraceLift_comp f hf g hg, AddMonoidHom.comp_apply]

theorem pushforwardTraceLift_comp_spec_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) := by
  rw [pushforwardTraceLift_comp f hf g hg, AddMonoidHom.comp_apply]

theorem pushforwardTraceLift_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (pushforwardTraceLift (g ∘ f) (hg.comp hf) : _ →+ _) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) :=
  pushforwardTraceLift_comp f hf g hg











end JacobianChallenge.TraceDegree
